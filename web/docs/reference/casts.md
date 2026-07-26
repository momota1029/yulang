# Casts

Yulang inserts implicit casts at expected-type boundaries. Casts come from two
sources: explicit `cast` declarations and `from`-marked variants on `enum` or
`error`.

## Explicit casts

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }
```

A `cast(x: A): B = body` declaration registers an implicit conversion rule
from `A` to `B`. The body computes the target value. This declaration does not
implement the standard `Cast` role.

## Where casts are inserted

The compiler applies registered conversion rules at the boundary between an
inferred value type and a known expected type, including:

- Type annotations on bindings and parameters
- Function arguments
- Branch joins where two arms must agree on a type
- Effect arm result types

```yulang
my id: user_id = 1
my back: int = id

my use_int(n: int) = n + 1
use_int id   // user_id implicitly cast to int
```

The selected `cast` declaration supplies the conversion body; the compiler
does not insert the role method `x.cast`. The standard library does define a
separate `std::core::convert::Cast` role with a `.cast` method, but a `cast`
declaration neither implements nor calls it. The compiler never inserts a cast
in expression position with no expected type, so `id` on its own is still
`user_id`.

## Diagnostics

```yulang
my use_bool(x: bool) = x
use_bool 42
// error: no implicit cast from int to bool
```

If no conversion rule exists for the specific source/target pair, the compiler
reports a missing implicit cast. If more than one declaration matches, the cast
is reported as ambiguous and the program is rejected — Yulang does not
silently pick one.

## `from`-marked variants

```yulang
enum app_err:
    path from path_err
    parse from parse_err
```

`from` on an `enum` (or `error`) variant generates two things:

- the variant itself — `app_err::path` wraps a `path_err`
- a conversion rule from `path_err` to `app_err` that maps `e` to
  `app_err::path e`

The source type must be a single payload, and both the source and target are
nominal.

For `error` declarations, the `from` machinery also expands `wrap` and `up` to
catch the linked narrower errors; see [Errors](./errors) for that path.

## Working with newtype wrappers

A common pattern is wrapping a primitive in a struct to add type-level
distinction:

```yulang
struct seconds { value: int }

cast(x: seconds): int = x.value
cast(x: int): seconds = seconds { value: x }

my one_minute: seconds = 60
my doubled: seconds = one_minute.value * 2
```

The wrapper carries its identity through the type system, but ordinary
arithmetic still works through the casts.

## Limits

The current cast declaration machinery targets nominal source and target
types. It is best used for small wrapper types and error aggregation; it is
not a general-purpose structural conversion system.

Casts are not lazy: the cast body runs as soon as the boundary is reached. A
cast that is expensive should be written as a regular function instead, so
the call site is explicit.

## See also

- [Structs & Roles](./structs) — declaring nominal wrapper types
- [Errors](./errors) — `from`-based error aggregation
- [Values & Types](./types) — how nominal types interact with inference
