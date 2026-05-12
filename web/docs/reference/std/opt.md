# `std::opt`

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

The `opt` variants are exhaustive: every `case` on an `opt 'a` needs both
arms (or a wildcard) for the inference to settle.

## Common shapes

```yulang
// Default value
case fs::read_text path:
    just text -> text
    nil       -> "(no file)"

// Chain through a fallible step
case parse_int s:
    just n  -> just (n * 2)
    nil     -> nil
```

For richer combinators on optional values, lift them into `result` (see
[std::result](./result)) or write the few helpers your project needs.

## Quick reference

| Operation | Signature |
|---|---|
| `nil` | `opt 'a` |
| `just(x)` | `'a -> opt 'a` |

## See also

- [`std::result`](./result) — when failure carries information
- [Patterns → Enum patterns](../patterns) — variants in patterns
- [Errors](../errors) — typed failures expressed as effects
