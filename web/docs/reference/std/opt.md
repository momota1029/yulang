# `std::data::opt`

`opt 'a` represents an optional value. It has two variants:

```yulang
pub enum opt 'a = nil | just 'a
```

The prelude re-exports `opt`, `just`, and `nil`, so user code normally writes
them unqualified.

## Constructing

```yulang
nil
just 42
just "hello"
```

## Pattern-matching

```yulang
case maybe_text:
    just text -> text.len
    nil       -> 0
```

The compiler does not check `case` expressions for exhaustiveness. A matching
single arm is accepted:

```yulang
case just 1:
    just x -> x
```

This expression returns `1` without a `nil` arm. Cover both variants or add a
wildcard when the code needs to handle either value.

## Common shapes

```yulang
// Default value
case maybe_text:
    just text -> text
    nil       -> "(no file)"

// Chain through a fallible step
case parse_int s:
    just n  -> just (n * 2)
    nil     -> nil
```

For richer combinators on optional values, lift them into `result` (see
[std::data::result](./result)) or write the few helpers your project needs.

## Quick reference

| Operation | Signature |
|---|---|
| `nil` | `opt 'a` |
| `just(x)` | `'a -> opt 'a` |

## See also

- [`std::data::result`](./result) — when failure carries information
- [Patterns → Enum patterns](../patterns) — variants in patterns
- [Errors](../errors) — typed failures expressed as effects
