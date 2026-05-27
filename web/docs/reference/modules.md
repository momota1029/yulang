# Modules

## `use`

```yulang
use std::undet::*
use std::list::map
use std::ops::{(+), (-)}
use my_module::old_name as new_name
use noisy::* without debug
```

`use` brings names from a module into scope. `*` imports everything visible.
Imports may be grouped with `{...}`, renamed with `as`, and filtered with
`without`. Operator names can be imported with parentheses, such as `(+)`.

## Companion modules

Every `struct`, `type ... with:`, `enum`, `act`, `error`, and `role` declaration
creates a companion module of the same name. `our` and `pub` bindings inside
the body live there:

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point::norm2 (point { x: 3, y: 4 })
// or equivalently:
point { x: 3, y: 4 } .norm2
```

For `enum` and `error`, the variants are members of the companion (`opt::just 1`, `fs_err::not_found "p"`). Prelude reexports make common variants such as `just`, `nil`, `ok`, and `err` available without qualification. For `act`, the operations are members (`console::println_native "hi"` in `std::console`).

## Dot selection

`expr.method` first selects fields or methods associated with the receiver's
type, then can resolve role methods and effect-row methods. This works for:

- Structs: field accessors and methods declared in `with:`
- `type ... with:` methods, such as methods on standard-library `list` or `str`
- Role methods, such as `.add`, `.index`, or `.show`
- Effect-row methods, such as nondeterminism collectors `.list`, `.logic`, and
  `.once`

Selection on a record (anonymous, structural) instead pulls the field by name.
Act operations themselves are normally reached by path, for example
`console::println_native "hi"`.

## Standard library modules

| Module | Highlights |
|--------|------------|
| `std::prelude` | Entry files normally import this: `Add`, `Eq`, `Ord`, `Display`, `len`, `id`, `compose`, `last`/`next`/`redo`, `return`, `fail`, range operators, and core std reexports |
| `std::ops` | Operator definitions: `+`, `-`, `*`, `/`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `and`, `or`, `not` |
| `std::list` | List operations: `map`, `filter`, `fold`, `sort`, `cons`, `uncons`, `rev`, `append`, … |
| `std::range` | Range constructors and `Fold` impl |
| `std::opt` | `opt 'a`, with prelude-reexported `nil` and `just` |
| `std::result` | `result 'ok 'err`, with prelude-reexported `ok` and `err`, plus `map`, `and_then`, `unwrap_or` |
| `std::str` | `str` type, `Index` impls |
| `std::var` | `ref 'e 'a` and update helpers |
| `std::flow` | `sub`, `loop`, label-loop primitives |
| `std::fold` | `Fold` role with `.fold` plus default `.find` and `.contains` methods |
| `std::undet` | `each`, `guard`, `list`, `once`, `logic` |
| `std::junction` | `all`, `any` for effectful comparisons |
| `std::console` | `say`, `println`, `print`, plus host-handled `print_native` / `println_native` |
| `std::fs` | `read_text`, `read_at`, `open`, `write_text`, `exists`, `is_file`, `is_dir`, plus `fs_err` errors |
| `std::error` | `Throw` role |
| `std::index` | `Index` role |
