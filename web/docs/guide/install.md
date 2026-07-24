# Installation

Yulang is still experimental. If you want to follow the guide locally, install
the release CLI first, then run a tiny `.yu` file. The playground remains the
fastest way to try examples without installing anything.

## Binary release

Install the release archive for your OS. The binary contains the embedded
standard library and writes it to the user library directory on first use:

```sh
curl -fsSL https://yulang.momota.pw/install.sh | sh
```

The shell installer adds `~/.yulang/bin` to the relevant shell profile if it is
not already on `PATH`; restart the terminal before running `yulang`. Pass
`--no-modify-path` if you want to manage `PATH` yourself.

Without a version flag, the installer selects the newest published GitHub
release, including prereleases. To pin this release instead:

```sh
curl -fsSL https://yulang.momota.pw/install.sh | sh -s -- --version v0.1.0-alpha.10
```

On Windows:

```powershell
Invoke-WebRequest https://yulang.momota.pw/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File .\install.ps1
```

The PowerShell installer adds the install `bin` directory to the user `PATH`.
Use `-NoModifyPath` to skip that step.

To pin the current release, pass `-Version v0.1.0-alpha.10`.

## Check that a file runs

Create `hello.yu`:

```sh
cat > hello.yu <<'YU'
println "hello from Yulang"
1 + 2
YU
yulang run --print-roots hello.yu
```

Expected output:

```text
hello from Yulang
run roots [(), 3]
```

`yulang run` prints only program output such as `say` and `println`. Use
`yulang run --print-roots ...` when you want to inspect root expression values
from the CLI. Use `check` instead of `run` to print inferred types:

```sh
yulang check hello.yu
```

For one-line experiments, `run` also accepts source text from `-e`, explicit
stdin with `-`, or an implicit pipe:

```sh
yulang run -e "(each 1..20 + each 1..20).list.say"
echo "1 + 2" | yulang run --print-roots
echo "1" | yulang run --print-roots -
```

A bare `yulang run` in an interactive terminal still prints usage instead of
waiting for input.

To remove a release install:

```sh
curl -fsSL https://yulang.momota.pw/uninstall.sh | sh
```

On Windows:

```powershell
Invoke-WebRequest https://yulang.momota.pw/uninstall.ps1 -OutFile uninstall.ps1
powershell -ExecutionPolicy Bypass -File .\uninstall.ps1
```

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

For source-tree experimentation, `cargo run -p yulang -- run path/to/file.yu`
is the important command. The web deployment steps below are only needed when
updating the hosted playground/docs site.

The CLI caches compiler artifacts under the user cache root. See
[Cache](./cache) for `.yucu`, `.yuir`, `.yuvm`, and the route labels printed
by `--runtime-phase-timings`.

The language server ships in the same binary:

```sh
yulang server
```

The Zed extension starts `yulang server` from the installed `yulang` binary.
It searches the worktree environment, `~/.yulang/bin`, and `~/.cargo/bin`.
The source copy is kept under `yulang-zed/` and mirrored to the separate
extension repository.

### Zed development extension

Fetch the extension source from the repository submodule:

```sh
git submodule update --init yulang-zed
```

In Zed, open the command palette, run `zed: install dev extension`, and select
the `yulang-zed/` directory.

The extension requires `yulang server` to be discoverable on `PATH`. If the
binary is elsewhere, set `lsp.yulang.binary.path` in Zed settings as described
in the [extension README](https://github.com/momota1029/yulang-zed#language-server).

The repository is a Rust workspace. Its active compiler and runtime path is:

`source files → sources/parser → infer/poly → specialize/mono → control-ir → evidence-vm`

The main crates along that path are:

| Crate(s) | Purpose |
|----------|---------|
| `sources`, `parser` | collect source files and build concrete syntax/operator tables |
| `infer`, `poly` | infer types and produce the polymorphic IR |
| `specialize`, `mono` | specialize programs into monomorphic IR |
| `control-ir`, `evidence-vm` | lower to control IR and run the CLI's default backend |
| `mono-runtime` | directly interpret `mono` programs as the `--interpreter` oracle |
| `wasm` | expose the browser-facing WebAssembly API used by the playground |
| `yulang`, `yulang-editor` | provide the CLI/source pipeline and editor-facing integration |

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
