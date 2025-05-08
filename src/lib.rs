use std::{
    fs,
    marker::PhantomData,
    path::{Path, PathBuf},
};

use figment::{
    providers::Format,
    value::{Dict, Map, Tag, Value},
    Error, Figment, Metadata, Profile, Provider, Source,
};

/// A [`Provider`] that sources values from a (possibly nested) directory of files in a given
/// [`Format`].
///
/// # Constructing
///
/// A [`Directory`] provider is typically constructed indirectly via a type that
/// implements the [`Format`] trait via the [`FormatExt::directory()`] method which in-turn defers
/// [`Directory::new()`] by default:
///
/// ```rust
/// // The `FormatExt` trait must be in-scope to use its methods.
/// use figment::providers::{Format, Toml};
/// use figment_directory::{Directory, FormatExt as _};
///
/// // These two are equivalent, except the former requires the explicit type.
/// let json_directory = Directory::<Toml>::new(figment_directory::RootPath::new("foo"));
/// let json_directory = Toml::directory("foo");
/// ```
///
/// # Provider Details
///
///   * **Profile**
///
///     This provider does not set a profile.
///
///   * **Metadata**
///
///     This provider is named `${NAME} directory`, where `${NAME}` is [`Format::NAME`].
///     The directories file's paths are specified as file
///     [`Source`](crate::Source). Path interpolation is unchanged from the
///     default.
///
///   * **Data (Unnested, _default_)**
///
///     When nesting is _not_ specified, the source files in the given directory are read and
///     parsed, and the parsed dictionary is emitted into the profile
///     configurable via [`Directory::profile()`], which defaults to
///     [`Profile::Default`]. If the source dictionary is not present
///     an empty dictionary is emitted.
///
///   * **Data (Nested)**
///
///     When nesting is specified, the directory is expected to contain files and or subdirectories
///     named after your profiles. These subdirectories and files are parsed and emitted into the corresponding profiles.
///
///     /root
///     /root/default.toml              |
///     /root/default/foo.toml          |-- these get put into the "default" profile
///     /root/default/bar.toml          |
///  
///     /root/development.toml          |
///     /root/development/foo.toml      | -- these get put into the "development" profile
///
///   * **Conflict Resolution**
///     Per default, values in files that are higher up in the directory tree override values in deeply nested files.
///     As an example, take these two files:
///
///     ```toml
///     # /root/a.toml
///     [b]
///     c = 1
///     ```
///
///     ```toml
///     # /root/a/b.toml
///     c = 2
///     ```
///
///     The provider will prefer the value in `a.toml`, since it is higher up than `a/b.toml`.
///     Therefore, `c = 1` will "win".
///
///     This strategy corresponds to the "Join" strategy in the [figment docs on conflict resolution](https://docs.rs/figment/0.10.19/figment/struct.Figment.html#conflict-resolution).
///     The behaviour can be changed by using the methods on [`Directory`] corresponding to the
///     available strategies: [`Directory::merge`], [`Directory::adjoin`], [`Directory::admerge`] and [`Directory::join`] (if you like to be explicit).
pub struct Directory<F, FS = RootPath> {
    file_system: FS,
    conflict_resolution_strategy: ConflictResolutionStrategy,
    profile: Option<Profile>,
    format: PhantomData<F>,
}

pub trait FormatExt: Format {
    fn directory<P: Into<PathBuf>>(path: P) -> Directory<Self, RootPath>;
    #[cfg(feature = "include-dir")]
    fn included_directory<'a>(
        dir: &'a include_dir::Dir<'a>,
    ) -> Directory<Self, &'a include_dir::Dir<'a>>;
}

impl<F> FormatExt for F
where
    F: Format,
{
    fn directory<P: Into<PathBuf>>(path: P) -> Directory<Self, RootPath> {
        Directory::new(RootPath(path.into()))
    }

    #[cfg(feature = "include-dir")]
    fn included_directory<'a>(
        dir: &'a include_dir::Dir<'a>,
    ) -> Directory<Self, &'a include_dir::Dir<'a>> {
        Directory::new(dir)
    }
}

impl<F> Directory<F, RootPath> {}

impl<F, FS> Directory<F, FS> {
    pub fn new(file_system: FS) -> Self {
        Self {
            file_system,
            conflict_resolution_strategy: ConflictResolutionStrategy::Join,
            profile: Some(Profile::Default),
            format: PhantomData,
        }
    }
    /// Enables nesting on `self`, which results in top-level keys of the
    /// sourced data being treated as profiles.
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map};
    /// use figment_directory::FormatExt as _;
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     numbers: Vec<usize>,
    ///     untyped: Map<String, usize>,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.create_dir("cfg")?;
    ///     jail.create_file("cfg/default.toml", r#"
    ///         [untyped]
    ///         global = 0
    ///         hi = 7
    ///     "#)?;
    ///     jail.create_file("cfg/staging.toml", r#"
    ///         numbers = [1, 2, 3]
    ///     "#)?;
    ///     jail.create_file("cfg/release.toml", r#"
    ///         numbers = [6, 7, 8]
    ///     "#)?;
    ///
    ///     // Enable nesting via `nested()`.
    ///     let figment = Figment::from(Toml::directory("cfg").nested());
    ///
    ///     let figment = figment.select("staging");
    ///     let config: Config = figment.extract()?;
    ///     assert_eq!(config, Config {
    ///         numbers: vec![1, 2, 3],
    ///         untyped: figment::util::map!["global".into() => 0, "hi".into() => 7],
    ///     });
    ///
    ///     let config: Config = figment.select("release").extract()?;
    ///     assert_eq!(config, Config {
    ///         numbers: vec![6, 7, 8],
    ///         untyped: figment::util::map!["global".into() => 0, "hi".into() => 7],
    ///     });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn nested(mut self) -> Self {
        self.profile = None;
        self
    }

    /// Set the profile to emit data to when nesting is disabled.
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map, Profile};
    /// use figment_directory::FormatExt as _;
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config { nested: NestedConfig }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct NestedConfig { value: u8 }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.create_dir("cfg")?;
    ///     jail.create_file("cfg/nested.toml", r#"
    ///         value = 123
    ///     "#);
    ///     let provider = Toml::directory("cfg").profile("debug");
    ///     let figment = Figment::from(provider).select("debug");
    ///     let config: Config = figment.extract()?;
    ///     assert_eq!(config.nested, NestedConfig { value: 123 });
    ///     let result: Result<Config, _> = figment.select(Profile::Default).extract();
    ///     assert!(result.is_err(), "extract() should have errored but there was a value in the default profile");
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn profile<P: Into<Profile>>(mut self, profile: P) -> Self {
        self.profile = Some(profile.into());
        self
    }

    /// Set the conflict resolution strategy to
    ///   * prefer values in files that are lower down in the directory tree
    ///   * override conflicting arrays instead of appending
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map};
    /// use figment_directory::FormatExt as _;
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     numbers: Vec<usize>,
    ///     untyped: Map<String, usize>,
    /// }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct NestLevelOne {
    ///     one: Config,
    /// }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct NestLevelTwo {
    ///     two: NestLevelOne,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.create_dir("cfg")?;
    ///     jail.create_file("cfg/two.toml", r#"
    ///         [one.untyped]
    ///         global = 0
    ///         hi = 7
    ///         
    ///         [one]
    ///         numbers = [1, 2, 3]
    ///     "#)?;
    ///     jail.create_dir("cfg/two")?;
    ///     jail.create_file("cfg/two/one.toml", r#"
    ///         numbers = [6, 7, 8]
    ///
    ///         [untyped]
    ///         hi = 8
    ///         foo = 42
    ///     "#)?;
    ///
    ///     // Set conflict resolution strategy via `merge()`.
    ///     let figment = Figment::from(Toml::directory("cfg").merge());
    ///
    ///     let config: NestLevelTwo = figment.extract()?;
    ///     assert_eq!(config.two.one, Config {
    ///         numbers: vec![6, 7, 8],
    ///         untyped: figment::util::map!["global".into() => 0, "hi".into() => 8, "foo".into() => 42],
    ///     });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn merge(mut self) -> Self {
        self.conflict_resolution_strategy = ConflictResolutionStrategy::Merge;
        self
    }

    /// Set the conflict resolution strategy to
    ///   * prefer values in files that are higher up in the directory tree
    ///   * override conflicting arrays instead of appending
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map};
    /// use figment_directory::FormatExt as _;
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     numbers: Vec<usize>,
    ///     untyped: Map<String, usize>,
    /// }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct NestLevelOne {
    ///     one: Config,
    /// }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct NestLevelTwo {
    ///     two: NestLevelOne,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.create_dir("cfg")?;
    ///     jail.create_file("cfg/two.toml", r#"
    ///         [one.untyped]
    ///         global = 0
    ///         hi = 7
    ///         
    ///         [one]
    ///         numbers = [1, 2, 3]
    ///     "#)?;
    ///     jail.create_dir("cfg/two")?;
    ///     jail.create_file("cfg/two/one.toml", r#"
    ///         numbers = [6, 7, 8]
    ///
    ///         [untyped]
    ///         hi = 8
    ///         foo = 42
    ///     "#)?;
    ///
    ///     // Set conflict resolution strategy via `join()`.
    ///     let figment = Figment::from(Toml::directory("cfg").join());
    ///
    ///     let config: NestLevelTwo = figment.extract()?;
    ///     assert_eq!(config.two.one, Config {
    ///         numbers: vec![1, 2, 3],
    ///         untyped: figment::util::map!["global".into() => 0, "hi".into() => 7, "foo".into() => 42],
    ///     });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn join(mut self) -> Self {
        self.conflict_resolution_strategy = ConflictResolutionStrategy::Join;
        self
    }

    /// Set the conflict resolution strategy to
    ///   * prefer values in files that are lower down in the directory tree
    ///   * append conflicting arrays instead of overriding
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map};
    /// use figment_directory::FormatExt as _;
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     numbers: Vec<usize>,
    ///     untyped: Map<String, usize>,
    /// }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct NestLevelOne {
    ///     one: Config,
    /// }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct NestLevelTwo {
    ///     two: NestLevelOne,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.create_dir("cfg")?;
    ///     jail.create_file("cfg/two.toml", r#"
    ///         [one.untyped]
    ///         global = 0
    ///         hi = 7
    ///         
    ///         [one]
    ///         numbers = [1, 2, 3]
    ///     "#)?;
    ///     jail.create_dir("cfg/two")?;
    ///     jail.create_file("cfg/two/one.toml", r#"
    ///         numbers = [6, 7, 8]
    ///
    ///         [untyped]
    ///         hi = 8
    ///         foo = 42
    ///     "#)?;
    ///
    ///     // Set conflict resolution strategy via `admerge()`.
    ///     let figment = Figment::from(Toml::directory("cfg").admerge());
    ///
    ///     let config: NestLevelTwo = figment.extract()?;
    ///     assert_eq!(config.two.one, Config {
    ///         numbers: vec![1, 2, 3, 6, 7, 8],
    ///         untyped: figment::util::map!["global".into() => 0, "hi".into() => 8, "foo".into() => 42],
    ///     });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn admerge(mut self) -> Self {
        self.conflict_resolution_strategy = ConflictResolutionStrategy::Admerge;
        self
    }

    /// Set the conflict resolution strategy to
    ///   * prefer values in files that are higher up in the directory tree
    ///   * append conflicting arrays instead of overriding
    ///
    /// ```rust
    /// use serde::Deserialize;
    /// use figment::{Figment, Jail, providers::{Format, Toml}, value::Map};
    /// use figment_directory::FormatExt as _;
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct Config {
    ///     numbers: Vec<usize>,
    ///     untyped: Map<String, usize>,
    /// }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct NestLevelOne {
    ///     one: Config,
    /// }
    ///
    /// #[derive(Debug, PartialEq, Deserialize)]
    /// struct NestLevelTwo {
    ///     two: NestLevelOne,
    /// }
    ///
    /// Jail::expect_with(|jail| {
    ///     jail.create_dir("cfg")?;
    ///     jail.create_file("cfg/two.toml", r#"
    ///         [one.untyped]
    ///         global = 0
    ///         hi = 7
    ///         
    ///         [one]
    ///         numbers = [1, 2, 3]
    ///     "#)?;
    ///     jail.create_dir("cfg/two")?;
    ///     jail.create_file("cfg/two/one.toml", r#"
    ///         numbers = [6, 7, 8]
    ///
    ///         [untyped]
    ///         hi = 8
    ///         foo = 42
    ///     "#)?;
    ///
    ///     // Set conflict resolution strategy via `adjoin()`.
    ///     let figment = Figment::from(Toml::directory("cfg").adjoin());
    ///
    ///     let config: NestLevelTwo = figment.extract()?;
    ///     assert_eq!(config.two.one, Config {
    ///         numbers: vec![1, 2, 3, 6, 7, 8],
    ///         untyped: figment::util::map!["global".into() => 0, "hi".into() => 7, "foo".into() => 42],
    ///     });
    ///
    ///     Ok(())
    /// });
    /// ```
    pub fn adjoin(mut self) -> Self {
        self.conflict_resolution_strategy = ConflictResolutionStrategy::Adjoin;
        self
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ConflictResolutionStrategy {
    Merge,
    Join,
    Adjoin,
    Admerge,
}

impl ConflictResolutionStrategy {
    fn resolve<P: Provider>(&self, figment: Figment, provider: P) -> Figment {
        let strategy = match self {
            ConflictResolutionStrategy::Merge => Figment::merge,
            ConflictResolutionStrategy::Join => Figment::join,
            ConflictResolutionStrategy::Adjoin => Figment::adjoin,
            ConflictResolutionStrategy::Admerge => Figment::admerge,
        };
        strategy(figment, provider)
    }
}

impl<F, FS> Provider for Directory<F, FS>
where
    F: Format,
    FS: Filesystem,
{
    fn metadata(&self) -> Metadata {
        Metadata::from(
            format!("{} Directory", F::NAME),
            Source::File(self.file_system.path().to_owned()),
        )
    }

    fn data(&self) -> Result<Map<Profile, Dict>, Error> {
        match &self.profile {
            Some(profile) => collect_dir::<F, FS>(
                &self.file_system,
                self.conflict_resolution_strategy,
                profile.clone(),
            )
            .data(),
            None => {
                collect_nested_dir::<F, FS>(&self.file_system, self.conflict_resolution_strategy)
            }
        }
    }
}

fn collect_nested_dir<F, FS>(
    file_system: &FS,
    strategy: ConflictResolutionStrategy,
) -> figment::Result<Map<Profile, Dict>>
where
    F: Format,
    FS: Filesystem,
{
    let Ok(dir_entries) = file_system.read_dir() else {
        return Ok(Map::new());
    };
    let mut map = Map::new();
    for entry in dir_entries {
        let Ok(entry) = entry else {
            continue;
        };
        let entry_path = entry.path();
        let Some(provider) = collect::<F, FS>(entry, strategy, Profile::Default) else {
            continue;
        };
        let Some(file_stem) = entry_path.file_stem().and_then(|stem| stem.to_str()) else {
            continue;
        };
        let data = provider.data()?.remove(&Profile::Default);
        println!("{file_stem}, {data:?}");
        if let Some(data) = data {
            for (profile, dict) in data.into_iter().filter_map(|(profile, value)| {
                let Value::Dict(_, dict) = value else {
                    return None;
                };
                Some((profile, dict))
            }) {
                map.insert(Profile::from(profile), dict);
            }
        }
    }
    Ok(map)
}

fn collect_dir<F, FS>(
    file_system: &FS,
    strategy: ConflictResolutionStrategy,
    profile: Profile,
) -> Figment
where
    F: Format,
    FS: Filesystem,
{
    let mut figment = Figment::new();
    let Ok(dir_entries) = file_system.read_dir() else {
        return figment;
    };
    for entry in dir_entries {
        if let Some(provider) = entry
            .ok()
            .and_then(|entry| collect::<F, FS>(entry, strategy, profile.clone()))
        {
            figment = strategy.resolve(figment, provider);
        }
    }
    figment
}

fn collect<F, FS>(
    entry: FS::DirEntry,
    strategy: ConflictResolutionStrategy,
    profile: Profile,
) -> Option<impl Provider>
where
    F: Format,
    FS: Filesystem,
{
    match entry.into_fs_entry() {
        FilesystemEntry::Invalid => None,
        FilesystemEntry::File { stem, file } => {
            let nested_provider = NestedProvider {
                inner: file.to_figment::<F>(profile),
                key: stem,
            };
            Some(nested_provider)
        }
        FilesystemEntry::Dir { dir: fs, name } => {
            let nested_figment = collect_dir::<F, _>(&fs, strategy, profile);
            Some(NestedProvider {
                inner: nested_figment,
                key: name.to_string(),
            })
        }
    }
}

struct NestedProvider<P> {
    inner: P,
    key: String,
}

impl<P> Provider for NestedProvider<P>
where
    P: Provider,
{
    fn metadata(&self) -> Metadata {
        self.inner.metadata()
    }

    fn data(&self) -> Result<Map<Profile, Dict>, Error> {
        let inner_data = self.inner.data()?;
        let data = inner_data
            .into_iter()
            .map(|(profile, inner_dict)| {
                let mut dict = Dict::new();
                dict.insert(self.key.clone(), Value::Dict(Tag::default(), inner_dict));
                (profile, dict)
            })
            .collect();
        Ok(data)
    }
}

trait Filesystem {
    type DirEntry: DirectoryEntry;
    type ReadDir: Iterator<Item = Result<Self::DirEntry, Self::Error>>;
    type Error: std::error::Error;

    fn read_dir(&self) -> Result<Self::ReadDir, Self::Error>;
    fn path(&self) -> &Path;
}

enum FilesystemEntry<F, D> {
    File { stem: String, file: F },
    Dir { name: String, dir: D },
    Invalid,
}

trait DirectoryEntry {
    type File: FilesystemFile;
    type Dir: Filesystem;
    fn path(&self) -> PathBuf;
    fn file_name(&self) -> Option<String>;
    fn into_fs_entry(self) -> FilesystemEntry<Self::File, Self::Dir>;
}

trait FilesystemFile {
    fn to_figment<F: Format>(self, profile: Profile) -> Figment;
}

#[derive(Debug, Clone)]
pub struct RootPath(PathBuf);

impl RootPath {
    pub fn new<P: Into<PathBuf>>(path: P) -> Self {
        Self(path.into())
    }
}

impl Filesystem for RootPath {
    type DirEntry = fs::DirEntry;
    type ReadDir = fs::ReadDir;
    type Error = std::io::Error;

    fn read_dir(&self) -> Result<Self::ReadDir, Self::Error> {
        fs::read_dir(&self.0)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

struct PathFile(PathBuf);

impl FilesystemFile for PathFile {
    fn to_figment<F: Format>(self, profile: Profile) -> Figment {
        Figment::from(F::file_exact(&self.0).profile(profile))
    }
}

impl DirectoryEntry for fs::DirEntry {
    type Dir = RootPath;
    type File = PathFile;
    fn path(&self) -> PathBuf {
        fs::DirEntry::path(self)
    }

    fn file_name(&self) -> Option<String> {
        fs::DirEntry::file_name(self).into_string().ok()
    }

    fn into_fs_entry(self) -> FilesystemEntry<Self::File, Self::Dir> {
        let Some(name) = DirectoryEntry::file_name(&self) else {
            return FilesystemEntry::Invalid;
        };
        let path = self.path();
        if path.is_dir() {
            FilesystemEntry::Dir {
                dir: RootPath(path),
                name,
            }
        } else {
            let Some((stem, _ext)) = name.rsplit_once('.') else {
                return FilesystemEntry::Invalid;
            };
            FilesystemEntry::File {
                file: PathFile(path),
                stem: stem.to_owned(),
            }
        }
    }
}

#[cfg(feature = "include-dir")]
impl<'a> Filesystem for &'a include_dir::Dir<'a> {
    type DirEntry = &'a include_dir::DirEntry<'a>;
    type ReadDir = InfallibleIter<core::slice::Iter<'a, include_dir::DirEntry<'a>>>;
    type Error = std::convert::Infallible;

    fn read_dir(&self) -> Result<Self::ReadDir, Self::Error> {
        Ok(InfallibleIter(self.entries().iter()))
    }

    fn path(&self) -> &Path {
        include_dir::Dir::path(self)
    }
}

#[cfg(feature = "include-dir")]
impl<'a> DirectoryEntry for &'a include_dir::DirEntry<'a> {
    type File = &'a include_dir::File<'a>;
    type Dir = &'a include_dir::Dir<'a>;

    fn path(&self) -> PathBuf {
        include_dir::DirEntry::path(self).to_owned()
    }

    fn file_name(&self) -> Option<String> {
        let os_str = include_dir::DirEntry::path(self).file_name()?;
        let str = os_str.to_str()?;
        Some(str.to_owned())
    }

    fn into_fs_entry(self) -> FilesystemEntry<Self::File, Self::Dir> {
        let Some(name) = DirectoryEntry::file_name(&self) else {
            return FilesystemEntry::Invalid;
        };
        match self {
            include_dir::DirEntry::Dir(fs) => FilesystemEntry::Dir { dir: fs, name },
            include_dir::DirEntry::File(file) => {
                let Some((stem, _ext)) = name.rsplit_once('.') else {
                    return FilesystemEntry::Invalid;
                };
                FilesystemEntry::File {
                    file,
                    stem: stem.to_owned(),
                }
            }
        }
    }
}

#[cfg(feature = "include-dir")]
impl<'a> FilesystemFile for &'a include_dir::File<'a> {
    fn to_figment<F: Format>(self, profile: Profile) -> Figment {
        let Some(contents) = self.contents_utf8() else {
            return Figment::new();
        };
        let data = figment::providers::Data::<F>::string(contents).profile(profile);
        Figment::from(data)
    }
}

#[cfg(feature = "include-dir")]
struct InfallibleIter<I>(I);

#[cfg(feature = "include-dir")]
impl<T, I> Iterator for InfallibleIter<I>
where
    I: Iterator<Item = T>,
{
    type Item = Result<T, std::convert::Infallible>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(Ok)
    }
}

#[cfg(test)]
mod tests {
    use figment::{providers::Toml, Figment, Jail};
    use serde::Deserialize;

    use super::*;

    #[test]
    fn directory_does_not_exist() {
        Jail::expect_with(|_jail| {
            let config: Dict = Figment::from(Toml::directory("cfg")).extract()?;

            assert_eq!(config, Dict::new());
            Ok(())
        })
    }

    #[test]
    fn handles_nested_directory() {
        Jail::expect_with(|jail| {
            jail.create_dir("root")?;
            jail.create_file(
                "root/basic.toml",
                r#"
                    int = 5
                    str = "string"
                "#,
            )?;
            jail.create_dir("root/basic")?;
            jail.create_file(
                "root/basic/nested.toml",
                r#"
                    bool = true
                    array = [1.5]
                    default = 2
                "#,
            )?;

            let config: NestedBasicConfig =
                Figment::new().merge(Toml::directory("root")).extract()?;

            assert_eq!(config.basic.int, 5);
            assert_eq!(&config.basic.str, "string");
            assert!(config.basic.nested.bool);
            assert_eq!(config.basic.nested.array, vec![1.5]);
            assert_eq!(config.basic.nested.default, 2);
            Ok(())
        })
    }

    #[test]
    #[cfg(feature = "include-dir")]
    fn handles_nested_directory_include_dir() {
        let basic_entries = [include_dir::DirEntry::File(include_dir::File::new(
            "nested.toml",
            r#"
bool = true
array = [1.5]
default = 2
                "#
            .as_bytes(),
        ))];
        let root_entries = [
            include_dir::DirEntry::File(include_dir::File::new(
                "basic.toml",
                r#"
int = 5
str = "string"
            "#
                .as_bytes(),
            )),
            include_dir::DirEntry::Dir(include_dir::Dir::new("basic", &basic_entries)),
        ];
        let dir = include_dir::Dir::new("root", &root_entries);

        let config: NestedBasicConfig = Figment::new()
            .merge(Toml::included_directory(&dir))
            .extract()
            .unwrap();

        assert_eq!(config.basic.int, 5);
        assert_eq!(&config.basic.str, "string");
        assert!(config.basic.nested.bool);
        assert_eq!(config.basic.nested.array, vec![1.5]);
        assert_eq!(config.basic.nested.default, 2);
    }

    #[derive(Debug, Deserialize)]
    struct NestedBasicConfig {
        basic: BasicConfig,
    }

    #[derive(Debug, Deserialize)]
    struct BasicConfig {
        str: String,
        int: i64,
        nested: NestedConfig,
    }

    #[derive(Debug, Deserialize)]
    struct NestedConfig {
        bool: bool,
        array: Vec<f64>,
        default: i64,
    }
}
