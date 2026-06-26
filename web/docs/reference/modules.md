# Modules

## `use`

```yulang
use std::control::nondet::*
use std::data::list::map
use std::core::ops::{(+), (-)}
use my_module::old_name as new_name
use noisy::* without debug
```

`use` brings names from a module into scope. `*` imports everything visible.
Imports may be grouped with `{...}`, renamed with `as`, and filtered with
`without`. Operator names can be imported with parentheses, such as `(+)`.

## Realm and band paths

A realm is a versioned resolution space. A band is an import/build island inside
one realm. A module path lives inside one band.

For local files, a directory with `realm.toml` is an explicit editable realm. If
there is no `realm.toml`, the entry file's parent directory is an implicit
editable realm. The entry file is the root module, but its band path comes from
the file path relative to the realm root:

```text
main.yu          band main
tools/parser.yu  band tools/parser
```

Bare paths stay inside the current band:

```yulang
use helper::answer
```

The compiler does not retry `helper::answer` as a sibling band if same-band
lookup fails. To import another band from the current realm, use `realm/`:

```yulang
use realm/helper::answer
use realm/tools/parser::json::value
```

The separator before the band boundary is `/`; after the band root it is `::`.
The reserved `band::` qualifier starts at the current band root:

```yulang
use band::inner::value
```

In an entry file named `main.yu`, `realm/main::value` aliases the entry root
module. It does not load `main.yu` a second time and is not a cross-band cycle.

`std::...` is a prebound standard-library alias, not a generic fallback from a
bare first segment to a same-realm band.

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

For `enum` and `error`, the variants are members of the companion (`opt::just 1`, `io_err::not_found "p"`). Prelude reexports make common variants such as `just`, `nil`, `ok`, and `err` available without qualification. For `act`, the operations are members (`out::write "hi"` in `std::io::console`).

## `act copy`

`act copy = source` creates a new effect family by copying another `act`. It is
not an alias: operations emitted through the copied family are distinct from
operations emitted through the source family.

Only the source act's `pub` and `our` surface is inherited. Source `my`
operations and helper members remain private to the source act and are not
visible in the destination companion or its `with:` body.

```yulang
act source:
    my hidden = 1
    our visible = 2

act copy = source with:
    my local = 3
    our own = local
```

`copy` contains `visible`, `local`, and `own`, but not `hidden`. If an exported
source member depends on a source-private helper, that copied act may be
ill-formed; the private helper is intentionally not smuggled through the copy.

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
`out::write "hi"`.

## Standard library modules

| Module | Highlights |
|--------|------------|
| `std::prelude` | Entry files normally import this: `Add`, `Eq`, `Ord`, `Display`, `len`, `id`, `compose`, `last`/`next`/`redo`, `return`, `fail`, range operators, and core std reexports |
| `std::core::ops` | Operator definitions: `+`, `-`, `*`, `/`, `==`, `!=`, `<`, `<=`, `>`, `>=`, `and`, `or`, `not` |
| `std::data::list` | List operations: `map`, `filter`, `fold`, `sort`, `cons`, `uncons`, `rev`, `append`, … |
| `std::data::range` | Range constructors and `Fold` impl |
| `std::data::opt` | `opt 'a`, with prelude-reexported `nil` and `just` |
| `std::data::result` | `result 'ok 'err`, with prelude-reexported `ok` and `err`, plus `map`, `and_then`, `unwrap_or` |
| `std::text::str` | `str` type, `Index` impls |
| `std::control::var` | `ref 'e 'a`, local mutable binding support, and update helpers |
| `std::control::flow` | `sub`, `loop`, label-loop primitives |
| `std::data::fold` | `Fold` role with `.fold` plus default `.find` and `.contains` methods |
| `std::control::nondet` | `each`, `guard`, `list`, `once`, `logic` |
| `std::control::junction` | `all`, `any` for effectful comparisons |
| `std::io::console` | `say`, `println`, `print`, `note`, `eprint`, `warn`, `die`, backed by the `out` / `err` / `warn` / `die` effects |
| `std::io::file` | `read_text`, `read_at`, `open`, `write_text`, `exists`, `is_file`, `is_dir`, plus `io_err` errors |
| `std::control::throw` | `Throw` role and `fail` support |
| `std::data::index` | `Index` role |
