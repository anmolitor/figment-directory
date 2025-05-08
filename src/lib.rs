use std::{
    fs::{self, DirEntry},
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
/// let json_directory = Directory::<Toml>::new("foo");
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
pub struct Directory<F> {
    path: PathBuf,
    conflict_resolution_strategy: ConflictResolutionStrategy,
    profile: Option<Profile>,
    format: PhantomData<F>,
}

pub trait FormatExt: Format {
    fn directory<P: Into<PathBuf>>(path: P) -> Directory<Self>;
}

impl<F> FormatExt for F
where
    F: Format,
{
    fn directory<P: Into<PathBuf>>(path: P) -> Directory<Self> {
        Directory::new(path)
    }
}

impl<F> Directory<F> {
    pub fn new<P: Into<PathBuf>>(path: P) -> Self {
        Self {
            path: path.into(),
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

impl<F> Provider for Directory<F>
where
    F: Format,
{
    fn metadata(&self) -> Metadata {
        Metadata::from(
            format!("{} Directory", F::NAME),
            Source::File(self.path.clone()),
        )
    }

    fn data(&self) -> Result<Map<Profile, Dict>, Error> {
        match &self.profile {
            Some(profile) => collect_dir::<F>(
                &self.path,
                self.conflict_resolution_strategy,
                profile.clone(),
            )
            .data(),
            None => collect_nested_dir::<F>(&self.path, self.conflict_resolution_strategy),
        }
    }
}

fn collect_nested_dir<F>(
    path: &Path,
    strategy: ConflictResolutionStrategy,
) -> figment::Result<Map<Profile, Dict>>
where
    F: Format,
{
    let Ok(dir_entries) = fs::read_dir(path) else {
        return Ok(Map::new());
    };
    let mut map = Map::new();
    for entry in dir_entries {
        let Ok(entry) = entry else {
            continue;
        };
        let entry_path = entry.path();
        let Some(provider) = collect::<F>(entry, strategy, Profile::Default) else {
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

fn collect_dir<F>(path: &Path, strategy: ConflictResolutionStrategy, profile: Profile) -> Figment
where
    F: Format,
{
    let mut figment = Figment::new();
    let Ok(dir_entries) = fs::read_dir(path) else {
        return figment;
    };
    for entry in dir_entries {
        if let Some(provider) = entry
            .ok()
            .and_then(|entry| collect::<F>(entry, strategy, profile.clone()))
        {
            figment = strategy.resolve(figment, provider);
        }
    }
    figment
}

fn collect<F>(
    entry: DirEntry,
    strategy: ConflictResolutionStrategy,
    profile: Profile,
) -> Option<impl Provider>
where
    F: Format,
{
    let file_name = entry.file_name();
    let entry_path = entry.path();
    if entry_path.is_dir() {
        let Some(dirname) = file_name.to_str() else {
            // Ignore files and directories that are not valid UTF-8
            return None;
        };
        let nested_figment = collect_dir::<F>(&entry_path, strategy, profile);
        return Some(NestedProvider {
            inner: nested_figment,
            key: dirname.to_string(),
        });
    }

    let Some(file_stem) = entry_path.file_stem().and_then(|stem| stem.to_str()) else {
        // Ignore files that are not valid UTF-8
        return None;
    };
    let file = F::file_exact(&entry_path).profile(profile);

    let nested_provider = NestedProvider {
        inner: Figment::from(file),
        key: file_stem.to_string(),
    };
    Some(nested_provider)
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
