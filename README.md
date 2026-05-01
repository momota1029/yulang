# Yulang

Yulang is an experimental language that integrates algebraic effects and
handlers into a Simple-Sub-style subtyping inference engine. Effect rows are
represented and solved in the same constraint system as value types, role
constraints, and subtyping, so handlers can remove consumed effects while the
remaining effects still flow through inferred types.

At the surface level, Yulang aims to put an OCaml-like typed expression core
behind Ruby-style receiver-oriented syntax and Perl/Raku-style pragmatic
notation. Features that often look like built-in control flow or mutation are
mostly expressed through effects, handlers, roles, and standard library code.

The implementation is still changing quickly. The repository is public so the
current compiler, standard library, tests, and WebAssembly playground can be
read together, not because the language is stable.

## GitHub About

Suggested short description:

> Experimental language with Simple-Sub-style inference, algebraic effects,
> effect rows, roles, and Ruby/Perl/Raku-inspired syntax.

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

## Status

Yulang is pre-release research software. Syntax, type output, runtime IR, the
interpreter, and the standard library may change without compatibility promises.

## License

Licensed under either of:

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE))
- MIT License ([LICENSE-MIT](LICENSE-MIT))

at your option.
