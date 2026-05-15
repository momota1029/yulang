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

Yulang is currently best read as an alpha-stage research language. The
interpreter, playground, standard library, and language server are usable
enough to try real examples, but syntax, type display, effect semantics,
native lowering, and library APIs may still move.

The current language server reports parse/lowering/type errors with source
ranges, and many type errors include related locations such as the literal,
annotation, application argument, or inferred origin that contributed to the
mismatch. The diagnostics are intended to make experimentation practical, but
they are not yet a complete UX contract.

## Playground

The browser playground runs the current WebAssembly build and shows both
evaluated results and inferred public types:

<https://yulang.momota.pw>

The playground uses the same in-progress WebAssembly pipeline as the repository.
It may briefly show an empty page while the bundle and standard-library state
load; this is a loading-state limitation, not part of the language semantics.

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
  CLI commands, and the value / CPS representation status in detail. The
  native direction is optimized CPS first, then shared Cranelift codegen for
  JIT and object / executable output. The CPS representation path now covers
  effect hygiene regressions, finite nondeterminism, open-range guarded
  `.once` search, `sub` / `return` through loop-shaped standard-library
  control, recursive handler tuple results, and first-class closures / stored
  callbacks selected from records or lists. The default CLI also routes known
  structural-binding shapes away from the value backend instead of producing a
  crashing executable.
- **Language server** — `yulang server` provides hover, document symbols,
  semantic tokens, and diagnostics. Error reporting is now source-based enough
  for day-to-day exploration, including LSP `relatedInformation` for many type
  errors, but not every diagnostic has perfect provenance yet.
- **Type inference theory** — [web/docs/reference/type-theory.md](web/docs/reference/type-theory.md)
  and [web/docs/ja/reference/type-theory.md](web/docs/ja/reference/type-theory.md)
  introduce effect rows, handler hygiene, and hidden handler evidence from
  the public reference side. Implementation details live in
  [docs/hidden-effect-evidence.ja.md](docs/hidden-effect-evidence.ja.md).
- **Examples** — [`examples/`](examples) holds runnable Yulang programs
  exercising specific features. `examples/showcase.yu` is a broader tour.
- **Standard library** — [`lib/std/`](lib/std) is the in-progress standard
  library written in Yulang.

Useful examples to try when evaluating the current implementation:

- `examples/showcase.yu` — broad syntax and library tour.
- `examples/06_undet_once.yu` — nondeterminism through library effects.
- `examples/10_effect_handler.yu` — algebraic effect handlers.
- `examples/04_sub_return.yu` — local early return through `sub:`.
- `examples/11_attached_impl.yu` — attached role implementations.

## Quick Start

Install the CLI and embedded standard library:

```bash
cargo install yulang
yulang install std
```

Run a file on the interpreter (the semantic oracle for everything else):

```bash
yulang run examples/06_undet_once.yu
```

Print inferred public types:

```bash
yulang check examples/08_types.yu
```

The standard library is installed to
`~/.yulang/lib/yulang-0.1.0/std`. `yulang run`, `yulang check`, and
`yulang server` can also install this embedded standard library automatically
on first use if neither `YULANG_STD` nor a nearby `lib/std` is available.
The legacy `yulang-ls` binary is now a deprecated stub that delegates to
`yulang server`.

Start the language server directly:

```bash
yulang server
```

Zed support lives in [`yulang-zed/`](yulang-zed). The extension is not published
through the Zed extension registry yet; install it as a dev extension from Zed
and select the `yulang-zed` directory. When a `yulang` binary is available in
the worktree environment or in `~/.cargo/bin`, the extension starts
`yulang server` automatically.

The language server currently supports:

- hover for inferred values, locals, methods, and many type references;
- semantic tokens and document symbols;
- diagnostics for parser/lowering/type errors;
- `relatedInformation` on many type errors, for example pointing from an
  application error back to the literal or annotation that supplied a type.

Known LSP limits:

- diagnostic wording is still compiler-oriented in places;
- some related locations are approximate when inference keeps only a broad
  application or adapter span;
- hidden handler evidence is intentionally not shown in normal hover/type
  display, even when it distinguishes two internal principal schemes.

To use a different standard library checkout:

```bash
export YULANG_STD=/path/to/yulang/lib/std
```

Run an inline program:

```bash
yulang run <<'YU'
use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).once
YU
```

Native execution is a prototype with an explicit subset; see
[docs/native-backend.md](docs/native-backend.md) for the supported
programs and the CLI reference. The CPS representation backend currently
covers algebraic handlers, nondeterministic finite-list choices, `sub` /
`return`, open-range guarded `.once` search, and finite/open-range `for`
loop control for the documented regression set. CPS repr ABI modules now pass
through a shared optimization entrypoint before both JIT and object codegen;
the first pass rewrites explicit calls through empty forwarding continuations
and empty return continuations, reifies direct calls to structural primitive
wrappers, reifies local partial-application closure calls back to direct calls,
inlines small single-use one-shot continuations, removes dead pure value
statements, then prunes unreachable continuations while recording profiling
data for later thunk/handler simplification.

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
