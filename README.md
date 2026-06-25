# Yulang

Yulang is an experimental programming language that makes algebraic effects
and handlers feel like ordinary control flow.

The surface looks like a small expression-oriented scripting language: it has
method syntax, compact block notation, structs, enums, roles, user-defined
operators, loops, early return, and references. The unusual part is that many
features usually fixed in the core language are expressed through effects,
handlers, roles, and standard-library code.

Yulang is alpha-stage research software. The current implementation lives in
the `yulang` pipeline; syntax, type display, effect semantics, runtime IR,
and library APIs may still change.

Japanese: [README.ja.md](README.ja.md)

## A First Look

```yulang
// nondeterministic search: every Pythagorean triple under 15
{
    my a = each 1..15
    my b = each a..15
    my c = each b..15
    guard: a * a + b * b == c * c
    (a, b, c)
}.list  // => [(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]
```

`each` returns a nondeterministic value, `guard:` prunes branches where the
condition fails, and `.list` reifies the search into a concrete list. The
block is an ordinary expression with the `undet` effect; nothing in this
syntax is special-cased.

The same shape lifts over comparisons:

```yulang
// junction lifts a comparison over many choices at once
if all [1, 2, 3] < any [3, 4, 5]:
    "every left dominated"
else:
    "no"
```

`all` and `any` are library functions that produce nondeterministic values.
Lowering inserts `junction::junction` so the surrounding `if` receives a real
`bool` after every left/right pair has been considered.

Mutable state, early return, loops, and effectful conditions use the same
basic idea: familiar notation on the surface, typed effects and small library
abstractions underneath.

## Try It

To use the CLI from a release build, install the binary archive for your OS
and let the binary place the embedded standard library in the user library
directory:

```bash
curl -fsSL https://yulang.momota.pw/install.sh | sh -s -- --version v0.1.0-alpha.3
```

The installer adds `~/.yulang/bin` to your shell profile when it is not already
on `PATH`; restart the terminal before running `yulang`. Pass
`--no-modify-path` if you want to manage `PATH` yourself.

In the current terminal, use the installed binary path directly:

```bash
~/.yulang/bin/yulang run examples/06_undet_once.yu
```

On Windows, download and run the PowerShell installer:

```powershell
Invoke-WebRequest https://yulang.momota.pw/install.ps1 -OutFile install.ps1
powershell -ExecutionPolicy Bypass -File .\install.ps1 -Version v0.1.0-alpha.3
```

The PowerShell installer adds the install `bin` directory to the user `PATH`.
Pass `-NoModifyPath` to skip that update.

To uninstall a release install:

```bash
curl -fsSL https://yulang.momota.pw/uninstall.sh | sh
```

On Windows:

```powershell
Invoke-WebRequest https://yulang.momota.pw/uninstall.ps1 -OutFile uninstall.ps1
powershell -ExecutionPolicy Bypass -File .\uninstall.ps1
```

For development, build `yulang` and install the embedded standard library when
you want a user cache copy:

```bash
cargo build -p yulang
./target/debug/yulang install std
```

Run a file:

```bash
./target/debug/yulang run examples/06_undet_once.yu
```

The smallest complete program prints a user-facing string with `say`:

```yulang
say "Hello, World"
```

`run` executes the program through the current control VM and only prints
output produced by the program itself, such as `say` / `println`. To inspect
root expression values while experimenting, add `--print-roots`. To run
through the mono runtime instead of the control VM, pass `--interpreter`.
The control VM route caches compiled-unit `.yuunit` artifacts, principal
`.yuir` poly artifacts, and `.yuvm` VM artifacts under the user cache root;
use `yulang cache path`, `yulang cache stats`, and `yulang cache clear` to
inspect or clear it, or pass `--no-cache` to bypass cache read/write for one
command. Local source sets can also reuse cached compiled source-unit prefixes
when only a suffix of the module tree changed. When `--runtime-phase-timings` is
enabled, `run.cache` reports the route used for the current run, such as
`control-hit`, `poly-hit`, `compiled-unit-hit`, `source-unit-prefix-hit`, or
`full-miss`.

Check a file:

```bash
./target/debug/yulang check examples/08_types.yu
```

The standard library is normally installed to
`~/.yulang/lib/yulang-0.1.4/std`. `yulang run`, `yulang check`, and
`yulang server` can also install the embedded standard library automatically
on first use when neither `YULANG_STD` nor a nearby `lib/std` is available.

To use a different standard-library checkout:

```bash
export YULANG_STD=/path/to/yulang/lib/std
```

Parser-combinator helpers and parser-sugar syntax such as `rule { ... }` and
`~"..."` are experimental. They are useful for trying the direction of the
language, but their public API and diagnostics are not a compatibility promise.

## Where To Read Next

- [docs/language/overview.md](docs/language/overview.md):
  the main language overview.
- [docs/language/overview.ja.md](docs/language/overview.ja.md):
  Japanese language overview.
- [docs/status.md](docs/status.md):
  support status across parser, inference, runtime, and archived surfaces.
- [web/docs/reference/type-theory.md](web/docs/reference/type-theory.md):
  public reference for effect rows, handler hygiene, and hidden handler
  evidence.
- [docs/hidden-effect-evidence.ja.md](docs/hidden-effect-evidence.ja.md):
  implementation notes for hidden effect evidence.
- [examples/](examples):
  runnable Yulang examples.
- [lib/std/](lib/std):
  the standard library written in Yulang.

Good first examples:

- `examples/showcase.yu`: broad syntax and library tour.
- `examples/06_undet_once.yu`: nondeterminism through library effects.
- `examples/10_effect_handler.yu`: algebraic effect handlers.
- `examples/04_sub_return.yu`: local early return through `sub:`.
- `examples/11_attached_impl.yu`: attached role implementations.

## Language Server

Start the language server with:

```bash
./target/debug/yulang server
```

Current language-server support includes:

- semantic tokens;
- full-document sync;
- current lowering diagnostics.

Zed support lives in [yulang-zed/](yulang-zed). The extension starts the
language server through the installed `yulang` binary as `yulang server`, so
the release archive and the editor integration use the same executable. The
source copy in this repository is the version to keep in sync with the
separate `momota1029/yulang-zed` extension repository.

## Execution Backend

Yulang currently executes through the new mono runtime or the lighter control
VM built from the specialized mono IR. An earlier Cranelift/MMTk native backend
was explored in the old implementation and has been retired.

Background notes on the experiment and the optimizer plans that grew out of
it still live in:

- [docs/native-experimental-release.md](docs/native-experimental-release.md):
  release-gate notes for the retired opt-in native subset.
- [docs/native-backend.md](docs/native-backend.md):
  archived native backend support notes and historical limits.
- [archive/notes/design/cps-optimization-pass-plan.md](archive/notes/design/cps-optimization-pass-plan.md):
  CPS optimizer and algebraic-effect rewrite plan.

## Development

Run representative Rust test suites:

```bash
cargo test -p sources -p infer -p poly -p specialize -p yulang
```

Run an inline Yulang program:

```bash
printf '1\n' >/tmp/yulang-main.yu
./target/debug/yulang run --print-roots /tmp/yulang-main.yu
```

## Repository Layout

- `crates/yulang`: current CLI and language-server entry point.
- `crates/sources`: source collection, CST input, std install support, and realm freeze.
- `crates/infer`: CST → `poly` lowering and type inference.
- `crates/poly`: inferred polymorphic program representation.
- `crates/specialize`: principal monomorphization.
- `crates/mono`: monomorphic IR.
- `crates/mono-runtime`: oracle-style mono interpreter.
- `crates/control-vm`: lightweight control VM IR and runtime.
- `crates/parser`: parser and syntax tree support.
- `crates/list-tree`: shared persistent list implementation.
- `archive/crates`: old `yulang` implementation, retained as reference-only code outside the workspace.
- `examples`: executable examples for the current language implementation.
- `lib/std`: standard library written in Yulang.
- `web/playground`: legacy Vite-based browser playground sources; the active workspace does not build through it.
- `web/docs`: reference documentation.
- `notes`: bug, refactor, and progress notes.

## Status

Yulang is pre-release research software. Syntax, type output, runtime IR, the
VM, and the standard library may change without compatibility promises.
[docs/status.md](docs/status.md) describes the current support matrix.

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
