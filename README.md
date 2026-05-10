# Yulang

Yulang is an experimental programming language that tries to make algebraic
effects and handlers the ordinary control mechanism of the language, without
making the surface feel like a special-purpose effect calculus.

The language looks like a small, expression-oriented scripting language: it has
receiver-oriented method syntax, compact block/application notation, structs,
enums, roles, user-defined operators, loops, early return, references, and
library-defined control abstractions. The unusual part is that features that
would usually be built into the core language are mostly expressed through
effects, handlers, roles, and standard library code.

Under the hood, Yulang integrates algebraic effects and handlers into a
Simple-Sub-style subtyping inference engine. Effect rows are represented and
solved in the same constraint system as value types, role constraints, and
subtyping, so handlers can remove consumed effects while the remaining effects
still flow through inferred types.

The implementation is still changing quickly. The repository is public so the
current compiler, standard library, tests, and WebAssembly playground can be
read together, not because the language is stable.

## GitHub About

Suggested short description:

> Experimental language where everyday control flow is built from algebraic
> effects, handlers, roles, and Simple-Sub-style inference.

## What Makes It Different

Yulang is not mainly an "algebraic effects demo language." The goal is closer
to replacing the usual built-in control machinery of a lightweight language with
algebraic effects and handlers, then exposing that machinery through syntax that
still feels close to ordinary code.

For example, `return`, `for`, `last`, `next`, `redo`, local references,
nondeterministic choice, and effectful boolean conditions are not isolated
experimental features. They are examples of the same design rule: the language
surface may give them direct syntax, but their behavior is mostly supplied by
typed effects, handlers, roles, and library definitions.

This matters for library authors. A handler in Yulang only handles effects that
are explicit in the inferred effect type of the computation it receives. In
other words, handlers are hygienic with respect to type inference: they do not
silently catch unrelated operations just because those operations have the same
shape somewhere else in the program. Consumed effects are removed from the type,
and residual effects remain visible to callers.

The ambition is therefore not that Yulang has a uniquely powerful individual
effect feature. It is that ordinary language features can be factored into a
small typed effect core while staying usable through familiar notation.

## Playground

The browser playground is available at:

<https://yulang.momota.pw>

It runs the current WebAssembly build and shows both evaluated results and
inferred public types.

## Language Highlights

- Simple-Sub-style type inference with subtyping and row-like effect types.
- Algebraic effects and handlers whose residual effects are inferred.
- `for` loops built on effects, with `last`, `next`, and `redo`.
- Nondeterministic computation through `std::undet`.
- Structs, enums, roles, implementations, methods, and user-defined operators.
- Reference syntax with explicit read/write forms such as `$x` and `&x = value`.
- Receiver-oriented selection where `x.foo` may resolve to a field, method,
  role method, reference receiver method, or effect-oriented method.
- A `:` block/application form that reduces parentheses in nested calls.

For a broader user-facing introduction, see the language overview:

- [English](docs/language/overview.md)
- [日本語](docs/language/overview.ja.md)

Example:

```yulang
use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

my inflate({base = 1, extra = base + 1}) = base + extra

inflate { base: 3 }

{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}

sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0

({
    my y = if all [1, 2, 3] < any [2, 3, 4]:
        each [3, 4, 5]
    else:
        2

    point { x: 3, y: y } .norm2
}).once
```

## Repository Layout

- `crates/yulang-parser`: parser and syntax tree support.
- `crates/yulang-source`: source loading and module handling.
- `crates/yulang-infer`: type inference and principal-type export.
- `crates/yulang-runtime`: runtime IR, monomorphization, and interpreter.
- `crates/yulang-wasm`: WebAssembly API used by the playground.
- `examples`: executable examples for the current language implementation.
- `lib/std`: standard library written in Yulang.
- `web/playground`: Vite-based browser playground.

## Commands

```bash
cargo test -p yulang-runtime -p yulang-infer --lib

RUSTC_WRAPPER= cargo run -q -p yulang --release -- \
  --run <<'YU'
use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).once
YU

cargo run -q -p yulang -- --run examples/06_undet_once.yu
cargo run -q -p yulang -- --infer examples/08_types.yu

cd web/playground
npm ci
npm run build

YULANG_PLAYGROUND_DEPLOY_DIR=~/www/yulang-playground npm run deploy:dir
```

## Native Backend Progress

The native backend is under active development. The interpreter remains the
semantic oracle; native paths are enabled only for the subset listed here.

Public CLI status:

- [x] `--native-run` links and runs a native executable.
- [x] `--native-run` prefers the value backend for ordinary values.
- [x] `--native-run` falls back to the CPS representation backend only for
      explicit "unsupported by value backend" cases.
- [x] `--native-run-value-exe` exposes the value backend directly for debugging.
- [x] `--native-run-cps-repr-exe` exposes the CPS representation backend
      directly for debugging.
- [x] Default native artifacts are written under `target/yulang`.

Value backend status:

- [x] Source-to-runtime lowering can feed the value backend.
- [x] Native value object generation works.
- [x] Generated executables can print native value results.
- [x] `int`, `float`, `bool`, `unit`, and `str` literals are represented as
      opaque runtime values.
- [x] Basic numeric and boolean primitives run through runtime helper symbols:
      `+`, `-`, `*`, `/`, comparisons, equality, and `not`.
- [x] Basic conversion/string primitives are wired through helpers:
      integer/float/bool to string, string length, and string index.
- [x] Local `my` bindings and top-level non-function bindings can be evaluated
      by the value backend.
- [x] String concatenation works.
- [x] List literals, list merge, list length, and list index work.
- [x] Tuple, record, record field selection, and variant construction work.
- [ ] Record spread is not supported.
- [ ] General pattern matching is not supported in the value backend.
- [ ] General multi-block control flow is not supported in the value backend.
- [ ] Closure allocation, closure environments, and indirect closure calls are
      not supported in the value backend.
- [ ] Generic runtime value layout is still backed by `VmValue`; compact native
      representations are not finalized.

CPS representation backend status:

- [x] Pure scalar CPS programs can be compiled with Cranelift.
- [x] Small source-defined algebraic effects can be lowered through CPS.
- [x] Multi-shot resumption prototypes work for scalar programs.
- [x] Simple handler arms, value arms, primitive calls, direct calls, and
      conditional control are covered by regression tests.
- [x] `sub`/`return`-style control has a small CPS repr regression path.
- [x] Tuple, record, variant, and record selection can be lowered and evaluated
      in the CPS/CPS-repr interpreters.
- [x] Handler entry continuations receive captured environments in the
      Cranelift CPS repr path.
- [x] Lazy branch conditions that flow through thunk-valued continuation params
      are forced before the Cranelift branch condition is tested.
- [x] CPS repr Cranelift has a small thunk trampoline helper for `ThunkPtr`
      values used by lazy conditions and root wrappers.
- [x] CPS/CPS-repr interpreters can rebase a captured continuation under a
      freshly installed handler.
- [x] CPS repr evaluator carries handler-frame guard snapshots and skips a
      blocked handler frame when resolving `Perform`.
- [x] `LocalPushId`, `PeekId`, and `FindId` have native CPS guard statements in
      the CPS/CPS-repr interpreter paths.
- [x] CPS repr Cranelift has scalar guard-stack helper symbols for
      `FreshGuard`, `PeekGuard`, and `FindGuard`.
- [x] CPS repr Cranelift resumptions and thunks carry handler-stack and
      guard-stack snapshots in the scalar prototype.
- [x] CPS repr Cranelift thunks snapshot handler arm environments for handler
      frames whose captures are available at thunk creation time.
- [x] CPS repr Cranelift can rebase a resumption with `ResumeWithHandler` and
      skip a blocked handler frame for scalar handler tests.
- [x] CPS repr Cranelift can select handler arms across function boundaries
      through globally numbered handler ids and the dynamic handler stack.
- [x] CPS lowering carries `AddId` blocked guards into `Perform` in the
      CPS/CPS-repr interpreter paths.
- [x] Mutable reference edit/update runs through effect-aware CPS and the
      Cranelift CPS repr scalar path with VM comparison.
- [x] A minimal `once`-style branch handler can resume the first branch from
      tail and boolean-match condition effect operations in the Cranelift CPS
      repr scalar path.
- [x] `std::undet` `.once` over a finite list compiles through the CPS repr
      object/executable path.
- [x] First-class lambda values can be created and applied through the
      Cranelift CPS repr scalar path for pure higher-order calls.
- [ ] General thunk values are only partially represented; thunk roots can be
      forced only while they stay in the scalar CPS repr subset.
- [ ] General closures and heap value lanes are not complete.
- [ ] Non-scalar CPS return values can flow through the prototype as opaque
      `i64` heap pointers, but generated CPS executables do not yet print them
      as Yulang values.
- [ ] This path is still a prototype, not the default full-language runtime.

Cache and package/build status:

- [x] `target/yulang` is used for local native experiment outputs.
- [x] Persistent cache paths exist for compiled unit artifacts.
- [x] Realm/band source identity is documented as the direction for package-like
      source boundaries.
- [ ] Compiled unit artifact cache is not yet wired into the main lowering
      pipeline.
- [ ] `realm.toml` / `yulang.lock` are planned but not complete as a full
      package/build workflow.
- [ ] Native executable layout and install/build commands are still prototypes.

## Status

Yulang is pre-release research software. Syntax, type output, runtime IR, the
interpreter, and the standard library may change without compatibility promises.

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
