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
cargo run -p yulang -- run path/to/file.yu
```

For local experimentation, `cargo run -p yulang -- run path/to/file.yu` is the
important command (use `check` instead of `run` to print inferred types). The web deployment steps below are only needed when updating
the hosted playground/docs site.

## Published CLI

Install the main CLI with Cargo, then install the embedded standard library:

```sh
cargo install yulang
yulang install std
```

After that, run or check programs directly:

```sh
yulang run examples/06_undet_once.yu
yulang check examples/08_types.yu
```

`yulang run` prints only program output such as `say` and `println`. Use
`yulang run --print-roots ...` when you want to inspect root expression values
from the CLI.

The language server ships in the same binary:

```sh
yulang server
```

The Zed extension is not in the public Zed extension registry yet. To use it
today, install `yulang-zed/` from this repository as a Zed dev extension. The
extension starts `yulang server` when the `yulang` binary is available in the
worktree environment or in `~/.cargo/bin`.

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
