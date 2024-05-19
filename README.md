# Figment Directory &thinsp; [![ci.svg]][ci] [![crates.io]][crate] [![docs.rs]][docs]

[crates.io]: https://img.shields.io/crates/v/figment-directory.svg
[crate]: https://crates.io/crates/figment-directory
[docs.rs]: https://docs.rs/figment-directory/badge.svg
[docs]: https://docs.rs/figment-directory
[ci.svg]: https://github.com/anmolitor/figment-directory/workflows/CI/badge.svg
[ci]: https://github.com/anmolitor/figment-directory/actions

[Figment](https://docs.rs/figment/latest/figment/) provider for config values split into multiple files in a directory, working with any [Format](https://docs.rs/figment/latest/figment/providers/trait.Format.html).

```rust
use serde::Deserialize;
use figment::{Figment, providers::{Env, Format, Toml}};
use figment_directory::FormatExt as _;

#[derive(Deserialize)]
struct Config {
  database: DatabaseConfig,
  pubsub: PubsubConfig
}

#[derive(Deserialize)]
struct DatabaseConfig {
  url: String,
}

#[derive(Deserialize)]
struct PubsubConfig {
  url: String,
}

let config: Config = Figment::new()
    .merge(Toml::directory("config"))
    .extract()?;
```

Directory structure:
- config
  - database.toml
  - pubsub.toml

```toml
# database.toml
url = "some/url"
```

```toml
# pubsub.toml
url = "some/url"
```

# Overview

This crate contains the `Directory` provider for `Figment`, to allow loading
configuration values a directory containing (possibly nested) files in a consistent file format.
It is wrapped around a `Format` implementation like `figment::providers::Json` or `figment::providers::Toml`.

This might be helpful if you have a lot of configuration values and wish to organize it using 
the file system.

See the [documentation][docs] for a detailed usage guide and
more information.

# Usage

Add the following to your `Cargo.toml`:

```toml
[dependencies]
figment = { version = "0.10" }
figment-directory = { version = "0.1" }
```

## License

figment-directory is licensed under the [BSD-3-Clause License](https://opensource.org/license/BSD-3-Clause)
