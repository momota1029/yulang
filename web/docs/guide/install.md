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

## Binary release

Install the release archive for your OS. The binary contains the embedded
standard library and writes it to the user library directory on first use:

```sh
curl -fsSL https://yulang.momota.pw/install.sh | sh -s -- --version v0.1.0-alpha.1
```

The shell installer adds `~/.yulang/bin` to the relevant shell profile if it is
not already on `PATH`; restart the terminal before running `yulang`. Pass
`--no-modify-path` if you want to manage `PATH` yourself.

On Windows:

```powershell
Invoke-WebRequest https://yulang.momota.pw/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File .\install.ps1 -Version v0.1.0-alpha.1
```

The PowerShell installer adds the install `bin` directory to the user `PATH`.
Use `-NoModifyPath` to skip that step.

To remove a release install:

```sh
curl -fsSL https://yulang.momota.pw/uninstall.sh | sh
```

On Windows:

```powershell
Invoke-WebRequest https://yulang.momota.pw/uninstall.ps1 -OutFile uninstall.ps1
powershell -ExecutionPolicy Bypass -File .\uninstall.ps1
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

The Zed extension starts `yulang server` from the installed `yulang` binary.
It searches the worktree environment, `~/.yulang/bin`, and `~/.cargo/bin`.
The source copy is kept under `yulang-zed/` and mirrored to the separate
extension repository.

The repository is a Rust workspace. The main crates are:

| Crate | Purpose |
|-------|---------|
| `yulang-parser` | concrete syntax and operator parsing |
| `yulang-infer` | lowering, names, type inference, and core export |
| `yulang-runtime-ir` | runtime IR data structures and `RuntimeType` |
| `yulang-runtime-types` | runtime type representation and type-system helpers |
| `yulang-runtime-refine` | refine / validate / invariant / hygiene passes |
| `yulang-runtime-lower` | core IR → runtime IR lowering |
| `yulang-monomorphize` | type graph resolution and monomorphization |
| `yulang-vm` | VM compilation and evaluation |
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

The generated site uses `/` as the playground, `/guide/` and `/reference/`
for the English docs, and `/ja/guide/` and `/ja/reference/` for the Japanese
docs.

## Current limitations

- The language and standard library are still changing.
- Filesystem APIs are native-host only; the playground leaves filesystem
  requests unresolved.
- The wasm bundle embeds standard-library artifacts but still keeps source
  compilation as a conservative fallback.
