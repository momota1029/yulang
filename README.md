# Yulang

Yulang is an experimental programming language that tries to make algebraic
effects and handlers the ordinary control mechanism of the language, without
making the surface feel like a special-purpose effect calculus.

The language looks like a small, expression-oriented scripting language: it
has receiver-oriented method syntax, compact block/application notation,
structs, enums, roles, user-defined operators, loops, early return, and
references. The unusual part is that features that would usually be built
into the core language are mostly expressed through effects, handlers,
roles, and standard library code.

Under the hood, Yulang integrates algebraic effects and handlers into a
Simple-Sub-style subtyping inference engine. Effect rows are represented and
solved in the same constraint system as value types, role constraints, and
subtyping, so handlers can remove consumed effects while the remaining
effects still flow through inferred types.

The implementation is still changing quickly. The repository is public so
the current compiler, standard library, tests, and WebAssembly playground
can be read together, not because the language is stable.

## Playground

The browser playground runs the current WebAssembly build and shows both
evaluated results and inferred public types:

<https://yulang.momota.pw>

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

The condition `all [1, 2, 3] < any [2, 3, 4]` is not a special syntactic
form. `all` and `any` are ordinary library functions that produce
nondeterministic values; the lowering inserts `junction::junction` so the
condition becomes a real `bool` for the surrounding `if`. Mutable state,
early return, loops, and effectful conditions are handled by the same kind
of mechanism — typed effects plus a small library, surfaced through
familiar notation.

For a longer guided tour:

- [docs/language/overview.md](docs/language/overview.md) — English overview.
- [docs/language/overview.ja.md](docs/language/overview.ja.md) — Japanese overview.

## Where to Read Next

- **What works where** — [docs/status.md](docs/status.md) tracks each
  feature across parser, inference, the VM, the playground, and the native
  backend. It is the right place to check before depending on a feature.
- **Native backend** — [docs/native-backend.md](docs/native-backend.md)
  describes the native pipeline: which programs run natively today, the
  CLI commands, and the value / CPS representation status in detail.
- **Examples** — [`examples/`](examples) holds runnable Yulang programs
  exercising specific features. `examples/showcase.yu` is a broader tour.
- **Standard library** — [`lib/std/`](lib/std) is the in-progress standard
  library written in Yulang.

## Quick Start

Run a file on the interpreter (the semantic oracle for everything else):

```bash
cargo run -q -p yulang -- run examples/06_undet_once.yu
```

Print inferred public types:

```bash
cargo run -q -p yulang -- check examples/08_types.yu
```

Install the language server (it ships with the main `yulang` binary):

```bash
cargo install yulang
yulang install-std
yulang server
```

The standard library is installed to
`~/.yulang/lib/yulang-0.1.0/std`. `yulang server` also installs this embedded
standard library automatically on first use if neither `YULANG_STD` nor a
nearby `lib/std` is available. The legacy `yulang-ls` binary is now a
deprecated stub that delegates to `yulang server`.

To use a different standard library checkout:

```bash
export YULANG_STD=/path/to/yulang/lib/std
```

Run an inline program:

```bash
RUSTC_WRAPPER= cargo run -q -p yulang --release -- run <<'YU'
use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).once
YU
```

Native execution is a prototype with an explicit subset; see
[docs/native-backend.md](docs/native-backend.md) for the supported
programs and the CLI reference.

Run the test suites:

```bash
cargo test -p yulang-runtime -p yulang-infer --lib
```

Build the playground locally:

```bash
cd web/playground
npm ci
npm run build
```

## Repository Layout

- `crates/yulang-parser`: parser and syntax tree support.
- `crates/yulang-sources`: source-set collection, realms, compilation units, and syntax artifacts.
- `crates/yulang-typed-ir`: typed intermediate representation and principal-type evidence.
- `crates/yulang-infer`: type inference and principal-type export.
- `crates/yulang-runtime`: runtime IR, monomorphization, and interpreter.
- `crates/yulang-wasm`: WebAssembly API used by the playground.
- `examples`: executable examples for the current language implementation.
- `lib/std`: standard library written in Yulang.
- `web/playground`: Vite-based browser playground.

## Status

Yulang is pre-release research software. Syntax, type output, runtime IR,
the interpreter, and the standard library may change without compatibility
promises. [docs/status.md](docs/status.md) describes the current support
matrix; broader limitations are noted there and in
[docs/native-backend.md](docs/native-backend.md).

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
