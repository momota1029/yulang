# Yulang

Yulang is an experimental programming language focused on type inference,
subtyping, algebraic effects, and compact syntax for small DSL-like programs.

The implementation is still changing quickly. The repository is public so the
current compiler, standard library, tests, and WebAssembly playground can be
read together, not because the language is stable.

## Playground

The browser playground is available at:

<https://yulang.momota.pw>

It runs the current WebAssembly build and shows both evaluated results and
inferred public types.

## Language Highlights

- Simple-sub-inspired type inference with subtyping.
- Algebraic effects and handlers, including `sub:` / `return x` for early
  return-like control flow.
- `for` loops built on effects, with `last`, `next`, and `redo`.
- Nondeterministic computation through `std::undet`.
- Structs, enums, roles, implementations, methods, and user-defined operators.
- Reference syntax with explicit read/write forms such as `$x` and `&x = value`.
- A `:` block/application form that reduces parentheses in nested calls.

For a broader user-facing introduction, see the language overview:

- [English](docs/language/overview.md)
- [日本語](docs/language/overview.ja.md)

Example:

```yulang
use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2

sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0

({
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
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
