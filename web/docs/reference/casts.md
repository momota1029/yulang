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

A `cast(x: A): B = body` declaration lowers to an implementation of the
standard `Cast A` role with associated type `to = B`. The body computes the
target value.

## Where casts are inserted

The compiler inserts `Cast` calls at the boundary between an inferred value
type and a known expected type, including:

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

The inserted cast is the role method `x.cast` on the value being converted.
The compiler never inserts a cast in expression position with no expected
type, so `id` on its own is still `user_id`.

## Diagnostics

```yulang
my n: int = "abc"
// missing Cast str -> int impl
```

If no candidate impl exists, the compiler reports a missing `Cast` for the
specific source/target pair. If more than one impl could apply, the cast is
reported as ambiguous and the program is rejected — Yulang does not silently
pick one.

## `from`-marked variants

```yulang
enum app_err:
    path from path_err
    parse from parse_err
```

`from` on an `enum` (or `error`) variant generates two things:

- the variant itself — `app_err::path` wraps a `path_err`
- a `Cast path_err -> app_err` impl that maps `e` to `app_err::path e`

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

- [Structs & Roles](./structs) — the underlying role machinery
- [Errors](./errors) — `from`-based error aggregation
- [Values & Types](./types) — how nominal types interact with inference
