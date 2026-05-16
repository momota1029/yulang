# Yulang

Yulang is an experimental programming language that makes algebraic effects
and handlers feel like ordinary control flow.

The surface looks like a small expression-oriented scripting language: it has
method syntax, compact block notation, structs, enums, roles, user-defined
operators, loops, early return, and references. The unusual part is that many
features usually fixed in the core language are expressed through effects,
handlers, roles, and standard-library code.

Yulang is alpha-stage research software. The interpreter, playground, standard
library, and language server are usable enough to try real examples, but syntax,
type display, effect semantics, native lowering, and library APIs may still
change.

Japanese: [README.ja.md](README.ja.md)

## Try It

The fastest way to try Yulang is the browser playground:

<https://yulang.momota.pw>

To use the CLI locally, install the binary and the embedded standard library:

```bash
cargo install yulang
yulang install std
```

Run a file with the interpreter:

```bash
yulang run examples/06_undet_once.yu
```

The smallest complete program prints a user-facing string with `say`:

```yulang
say "Hello, World"
```

`run` executes the program and only prints output produced by the program
itself, such as `say` / `println`. To inspect root expression values while
experimenting, add `--print-roots`.

Check a file and print inferred public types:

```bash
yulang check examples/08_types.yu
```

Try the native backend:

```bash
yulang run --native examples/06_undet_once.yu
```

The standard library is normally installed to
`~/.yulang/lib/yulang-0.1.0/std`. `yulang run`, `yulang check`, and
`yulang server` can also install the embedded standard library automatically
on first use when neither `YULANG_STD` nor a nearby `lib/std` is available.

To use a different standard-library checkout:

```bash
export YULANG_STD=/path/to/yulang/lib/std
```

## A First Look

```yulang
use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

if all [1, 2, 3] < any [2, 3, 4]:
    point { x: 3, y: 4 } .norm2
else:
    0
```

The condition `all [1, 2, 3] < any [2, 3, 4]` is not special syntax.
`all` and `any` are ordinary library functions that produce nondeterministic
values. Lowering inserts `junction::junction` so the surrounding `if` receives
a real `bool`.

Mutable state, early return, loops, and effectful conditions use the same
basic idea: familiar notation on the surface, typed effects and small library
abstractions underneath.

## Where To Read Next

- [docs/language/overview.md](docs/language/overview.md):
  the main language overview.
- [docs/language/overview.ja.md](docs/language/overview.ja.md):
  Japanese language overview.
- [docs/status.md](docs/status.md):
  support status across parser, inference, interpreter, playground, and native
  backend.
- [docs/native-backend.md](docs/native-backend.md):
  native backend support, CLI notes, and current limits.
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
yulang server
```

Current language-server support includes:

- hover for inferred values, locals, methods, and many type references;
- semantic tokens;
- document symbols;
- parser, lowering, and type diagnostics;
- `relatedInformation` on many type errors.

Zed support lives in [yulang-zed/](yulang-zed). The extension is not published
through the Zed extension registry yet; install it as a dev extension and
select the `yulang-zed` directory. When a `yulang` binary is available in the
worktree environment or in `~/.cargo/bin`, the extension starts
`yulang server` automatically.

The old `yulang-ls` binary is a deprecated stub that delegates to
`yulang server`.

## Native Backend

Native execution is a prototype with an explicit subset. The normal
user-facing entrypoint is:

```bash
yulang run --native path/to/file.yu
```

`yulang native` remains available for artifact generation and backend
debugging. The interpreter is still the semantic reference; the native backend
is catching up feature by feature. See
[docs/native-backend.md](docs/native-backend.md) for the supported programs,
CLI details, and known limits.
The current native effects path covers string/list/bytes/path/range primitives via
runtime helper symbols. CPS repr native also preserves handler prompt exits across
effectful call return frames, so `Display`/`Debug` list construction, `loop with`
if results, `for` body `if` var writes, and range iteration with console effects
match the interpreter in the covered regression cases. Captured resumptions also
rebase handler return-frame thresholds, covering indexed ref update continuations
in CPS repr native. Unit-typed scalar roots display as `()` in the JIT display
helper even though the scalar ABI carries them as `0`.

## Development

Run representative Rust test suites:

```bash
cargo test -p yulang-runtime -p yulang-infer --lib
```

Build the playground locally:

```bash
cd web/playground
npm ci
npm run build
```

Run an inline Yulang program:

```bash
yulang run --print-roots <<'YU'
use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).once
YU
```

## Repository Layout

- `crates/yulang`: CLI.
- `crates/yulang-parser`: parser and syntax tree support.
- `crates/yulang-sources`: source sets, realms, compilation units, and syntax artifacts.
- `crates/yulang-typed-ir`: typed intermediate representation and principal-type evidence.
- `crates/yulang-infer`: type inference and principal-type export.
- `crates/yulang-runtime`: runtime IR, monomorphization, and interpreter.
- `crates/yulang-native`: native backend.
- `crates/yulang-wasm`: WebAssembly API used by the playground.
- `examples`: executable examples for the current language implementation.
- `lib/std`: standard library written in Yulang.
- `web/playground`: Vite-based browser playground.
- `web/docs`: reference documentation.
- `notes`: bug, refactor, and progress notes.

## Status

Yulang is pre-release research software. Syntax, type output, runtime IR, the
interpreter, and the standard library may change without compatibility
promises. [docs/status.md](docs/status.md) describes the current support
matrix; broader limitations are noted there and in
[docs/native-backend.md](docs/native-backend.md).

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
