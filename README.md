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

## Try It

To use the CLI locally, build `yulang` and install the embedded standard
library when you want a user cache copy:

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

Check a file:

```bash
./target/debug/yulang check examples/08_types.yu
```

The standard library is normally installed to
`~/.yulang/lib/yulang-0.1.3/std`. `yulang run`, `yulang check`, and
`yulang server` can also install the embedded standard library automatically
on first use when neither `YULANG_STD` nor a nearby `lib/std` is available.

To use a different standard-library checkout:

```bash
export YULANG_STD=/path/to/yulang/lib/std
```

Parser-combinator helpers and parser-sugar syntax such as `rule { ... }` and
`~"..."` are experimental. They are useful for trying the direction of the
language, but their public API and diagnostics are not a compatibility promise.

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

Zed support lives in [yulang-zed/](yulang-zed). The extension is not published
through the Zed extension registry yet; install it as a dev extension and
select the `yulang-zed` directory. The extension should start `yulang server`
from the worktree environment or from the installed binary path.

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
- [notes/design/cps-optimization-pass-plan.md](notes/design/cps-optimization-pass-plan.md):
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
