# Casts

Yulang has an explicit `cast` declaration plus generated casts from `from`
variants.

## Explicit Casts

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }
```

A `cast(x: A): B = body` declaration lowers to an implementation of the
standard `Cast A` role with associated type `to = B`.

Implicit casts are inserted at expected-type boundaries, such as annotations,
function arguments, and branch joins:

```yulang
my id: user_id = 1
```

If no `Cast` impl is available, the compiler reports a missing impl. If more
than one candidate applies, it reports an ambiguous cast.

## `from` Variants

```yulang
enum app_err:
    fs from fs_err
```

`from` on an `enum` or `error` variant generates a `Cast` impl from the source
type to the surrounding enum/error type. For `error`, the declaration also
generates throwing operations and a `Throw` impl.

## Limits

The current cast declaration machinery is intended for nominal source and
target types. It is best used for small wrapper types and error aggregation,
not as a general-purpose structural conversion system.
