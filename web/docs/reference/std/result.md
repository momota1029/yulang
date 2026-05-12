# `std::result`

`result 'ok 'err` is the value-level form of a fallible computation. Use it
when you want to close an error effect into a value that can be stored,
returned, or pattern-matched on.

```yulang
pub enum result 'ok 'err:
    ok 'ok
    err 'err
```

The prelude re-exports `result`, `ok`, and `err`.

## Constructing

```yulang
ok 1
ok "yes"
err "missing config"
err fs_err::not_found "p"
```

## Pattern-matching

```yulang
case maybe_n:
    ok n  -> n + 1
    err e -> 0
```

## Combinators

```yulang
my doubled = (ok 21).map (\x -> x * 2)       // ok 42

(ok 1).and_then (\x -> ok (x + 1))           // ok 2
(ok 1).and_then (\_ -> err "stop")           // err "stop"
(err "stop").and_then (\x -> ok x)           // err "stop"

(ok 1).unwrap_or 0                            // 1
(err "boom").unwrap_or 0                      // 0
```

| Helper | Behavior |
|---|---|
| `r.map f` | apply `f` to the `ok` value, leave `err` unchanged |
| `r.and_then f` | run `f` on the `ok` value (which itself returns a `result`) |
| `r.unwrap_or fallback` | get the `ok` value, or `fallback` on `err` |

## Relationship with `error E:` and `wrap`

```yulang
case fs_err::wrap: read_text_or_throw path
of
    ok text -> use text
    err e   -> e.show
```

`E::wrap` runs a thunk, catches the matching error effect, and returns a
`result 'ok E`. This is the standard bridge between effect-based errors and
value-form results.

`from`-aggregating errors extend `wrap` to also catch linked narrower errors;
see [Errors](../errors).

## Quick reference

| Operation | Signature |
|---|---|
| `ok(x)` | `'a -> result 'a 'err` |
| `err(e)` | `'err -> result 'ok 'err` |
| `r.map f` | `result 'a 'err -> ('a -> 'b) -> result 'b 'err` |
| `r.and_then f` | `result 'a 'err -> ('a -> result 'b 'err) -> result 'b 'err` |
| `r.unwrap_or fallback` | `result 'a 'err -> 'a -> 'a` |

## See also

- [Errors](../errors) — `error E:` and the catch-by-name story
- [`std::opt`](./opt) — when the error side carries no information
- [Casts](../casts) — converting between result-shaped wrappers
