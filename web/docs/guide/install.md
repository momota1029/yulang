# Installation

Yulang is still experimental. The playground is the easiest way to try the
language, and the local CLI is mainly for development and regression testing.

## Playground

Open the <a href="/" target="_self">Playground</a>. It runs in the browser with
the same standard-library examples used by this documentation.

## From source

Clone the repository and use Cargo:

```sh
git clone https://github.com/momota1029/yulang.git
cd yulang
cargo test
cargo run -p yulang -- path/to/file.yu
```

For local experimentation, `cargo run -p yulang -- path/to/file.yu` is the
important command. The web deployment steps below are only needed when updating
the hosted playground/docs site.

The repository is a Rust workspace. The main crates are:

| Crate | Purpose |
|-------|---------|
| `yulang-parser` | concrete syntax and operator parsing |
| `yulang-infer` | lowering, names, type inference, and core export |
| `yulang-runtime` | runtime lowering, monomorphization, VM compilation, VM evaluation |
| `yulang-wasm` | browser-facing wasm API used by the playground |

## Web build

The web UI lives under `web/`:

```sh
npm --prefix web install
npm --prefix web run build
```

For local deployment into a directory:

```sh
YULANG_DEPLOY_DIR=/path/to/site npm --prefix web run deploy:dir
```

The generated site uses `/` as the playground and `/guide/` / `/reference/` as
documentation paths.

## Current limitations

- The language and standard library are still changing.
- Filesystem APIs are native-host only; the playground leaves filesystem
  requests unresolved.
- The wasm bundle embeds standard-library artifacts but still keeps source
  compilation as a conservative fallback.
