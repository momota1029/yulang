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
| `{ x, y }` | record (partial ok) |
| `[]`, `[1, 2]`, `[x, ..rest]` | list patterns |
| `opt::just x`, `opt::nil` | enum variant by qualified path |
| `tag x` | enum variant by short name (when unambiguous) |

A list pattern `[x, ..rest]` binds the head to `x` and the tail to `rest`.

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
my f({x = 0, y = 0}) = x + y
```

This is Yulang's optional argument mechanism. Defaults are evaluated left-to-right and may reference earlier fields.

## `if`

`if` is a regular expression:

```yulang
if x > 0: "positive" else: "non-positive"
```

It also accepts brace bodies and indented bodies:

```yulang
if cond { a } else { b }

if cond:
    a
else:
    b
```

The condition is a `bool` (or any expression whose type unifies with `bool`); `if` desugars to a `case` on its value.

## Enum patterns

```yulang
enum color = red | green | blue

case c:
    color::red   -> 0
    color::green -> 1
    color::blue  -> 2
```

Enum variants live in a companion module of the enum, so they are normally written `color::red`, etc. After `use color::*` the unqualified form is available.
