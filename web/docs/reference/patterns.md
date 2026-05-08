# Pattern Matching

## `case`

Yulang's pattern-matching keyword is `case`:

```yulang
case value:
    0 -> "zero"
    n -> "other"
```

Each arm is `pattern -> body`. Arms are tried top-to-bottom; the first that matches wins.

## Patterns

| Pattern | Matches |
|---------|---------|
| `_` | anything (wildcard) |
| `x` | binds to name `x` |
| `42`, `"hi"`, `true`, `false` | literals |
| `(a, b)` | tuple |
| `{ x, y }` | record fields named `x` and `y` |
| `[]`, `[1, 2]`, `[x, ..rest]` | list patterns |
| `just x`, `nil` | enum variants reexported by the prelude |
| `opt::just x`, `opt::nil` | enum variants by qualified path |
| `tag x` | enum variant by short name (when unambiguous) |

A list pattern `[x, ..rest]` binds the head to `x` and the tail to `rest`.
Spreads can also appear in the middle or at the head of list patterns.
In record patterns, a listed field is required unless it has a default.
Record patterns also support spread forms for the remaining fields.

## Guards

A pattern arm may carry a guard with `if`:

```yulang
case n:
    0 -> "zero"
    x if x < 0 -> "negative"
    _ -> "positive"
```

## Record patterns with defaults

In function arguments, record patterns can have defaults — a missing field uses the default:

```yulang
my f {x = 0, y = 0} = x + y
```

This is Yulang's optional argument mechanism. Defaults are evaluated left-to-right and may reference earlier fields.

## Enum patterns

```yulang
enum color = red | green | blue

case c:
    color::red   -> 0
    color::green -> 1
    color::blue  -> 2
```

Enum variants live in a companion module of the enum, so they are normally written `color::red`, etc. After `use color::*` the unqualified form is available.
