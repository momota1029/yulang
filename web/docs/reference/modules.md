# Modules

## `use`

```yulang
use std::undet::*
use std::list::map
```

`use` brings names from a module into scope. `*` imports everything visible.

## Companion modules

Every `struct`, `enum`, `act`, `error`, and `role` declaration creates a companion module of the same name. `our` and `pub` bindings inside the body live there:

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point::norm2 (point { x: 3, y: 4 })
// or equivalently:
point { x: 3, y: 4 } .norm2
```

For `enum` and `error`, the variants are members of the companion (`opt::just 1`, `fs_err::not_found "p"`). For `act`, the operations are members (`console::println "hi"`).

## Dot selection

`expr.method` resolves through the type's companion module. This works for:

- Structs: field accessors and methods declared in `with:`
- Effect operations and other companion entries
- Anything with an `our` binding in the value's companion

Selection on a record (anonymous, structural) instead pulls the field by name.

## Standard library modules

| Module | Highlights |
|--------|------------|
| `std::prelude` | Auto-imported core: `Add`, `Eq`, `Ord`, `Display`, `len`, `id`, `compose`, `for ... in ...`, `last`/`next`/`redo`, `return`, `..`, `..<`, `<..`, `<..<` |
| `std::ops` | Operator definitions: `+`, `-`, `*`, `/`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `and`, `or`, `not` |
| `std::list` | List operations: `map`, `filter`, `fold`, `sort`, `cons`, `uncons`, `rev`, `append`, … |
| `std::range` | Range constructors and `Fold` impl |
| `std::opt` | `enum opt 'a = nil | just 'a` |
| `std::result` | `enum result 'ok 'err`, `map`, `and_then`, `unwrap_or` |
| `std::str` | `str` type, `Index` impls |
| `std::var` | `ref 'e 'a` and update helpers |
| `std::flow` | `sub`, `loop`, label-loop primitives |
| `std::fold` | `Fold` role and helpers (`find`, `contains`) |
| `std::undet` | `each`, `guard`, `list`, `once`, `logic` |
| `std::junction` | `all`, `any` for effectful comparisons |
| `std::console` | `print`, `println` (host-handled) |
| `std::fs` | `read_text`, `write_text`, `exists`, `is_file`, `is_dir`, plus `fs_err` errors |
| `std::error` | `Throw` role |
| `std::index` | `Index` role |
