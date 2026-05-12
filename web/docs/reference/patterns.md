# Pattern Matching

Patterns appear wherever Yulang binds a value to a name: `case` arms, `catch`
arms, function arguments, `my` bindings, and lambdas.

## `case`

```yulang
case value:
    0 -> "zero"
    n -> "other"
```

Each arm is `pattern -> body`. Arms are tried top-to-bottom; the first that
matches wins. Bodies can be a single expression, a colon block, or a brace
block.

```yulang
case n:
    0 -> "zero"
    x ->
        my doubled = x * 2
        doubled.show
```

## Pattern forms

| Pattern | Matches |
|---------|---------|
| `_` | anything (wildcard) |
| `x` | binds to name `x` |
| `42`, `"hi"`, `true`, `false`, `()` | literals |
| `(a, b)` | tuple |
| `{ x, y }` | record with fields named `x` and `y` |
| `{ x = 0, y }` | record with default for `x` |
| `{ x: name }` | record field `x` renamed to `name` |
| `[]`, `[1, 2]`, `[x, ..rest]` | list patterns |
| `[..init, last]` | list with spread at head |
| `just x`, `nil` | enum variants re-exported by the prelude |
| `opt::just x`, `opt::nil` | enum variants by qualified path |
| `tag x` | enum variant by short name (unambiguous case) |

## Guards

A pattern arm can carry a guard with `if`:

```yulang
case n:
    0 -> "zero"
    x if x < 0 -> "negative"
    _ -> "positive"
```

The guard is evaluated only when the pattern matches. If the guard fails, the
next arm is tried.

## Literal patterns

```yulang
case msg:
    "" -> "empty"
    "hello" -> "greeting"
    _ -> "other"
```

Literal patterns match values that are structurally equal.

## Tuple patterns

```yulang
case point:
    (0, 0) -> "origin"
    (x, 0) -> "on x axis at " + x.show
    (0, y) -> "on y axis at " + y.show
    (x, y) -> "(" + x.show + ", " + y.show + ")"
```

Tuple patterns nest. `((a, b), c)` matches a pair whose first element is itself
a pair.

## Record patterns

```yulang
case shape:
    { kind: "circle", radius } -> 3.14 * radius * radius
    { kind: "square", side }   -> side * side
    _                           -> 0
```

A listed field is required unless it has a default. Fields can be renamed with
`{ field: bound_name }`.

### Renaming and defaults

```yulang
case config:
    { host: h = "localhost", port = 80 } -> h + ":" + port.show
```

`host: h` renames the bound name to `h`. `port = 80` provides a default.

### Spread

```yulang
case rec:
    { x, .._ }    -> x
    { ..tail, y } -> y
```

Use `..name` to capture remaining fields into a residual record, or `.._` to
ignore them. The spread can appear at the head or tail.

## List patterns

```yulang
case xs:
    []              -> "empty"
    [only]          -> "single: " + only.show
    [first, second] -> "pair"
    [head, ..tail]  -> "head: " + head.show
    [..init, last]  -> "ends with: " + last.show
```

Spread `..rest` captures the unmatched portion. A list pattern can have at most
one spread.

## Enum patterns

```yulang
enum color = red | green | blue

case c:
    color::red   -> 0
    color::green -> 1
    color::blue  -> 2
```

Variants live in the enum's companion module, so the usual spelling is
`color::red`. After `use color::*`, unqualified `red` also works.

Variants with payload bind the payload:

```yulang
enum tree 'a:
    leaf
    node 'a (tree 'a) (tree 'a)

case t:
    tree::leaf -> 0
    tree::node value left right -> value + sum left + sum right
```

## Patterns in function arguments

```yulang
my add (x, y) = x + y
my translate { dx = 0, dy = 0 } point = point.move dx dy
```

Top-level binding patterns, lambda arguments, and `my` destructurings share the
same pattern grammar.

## Patterns in `catch`

```yulang
catch action:
    log::put msg, k ->
        my logged = msg + "\n"
        k ()
    fs_err::not_found path, _ -> "(missing) " + path
    value -> value
```

Effect arms write the operation name as a pattern; the trailing `k` (or `_`)
binds the continuation. A value arm `v -> ...` handles normal completion.

## Patterns in `my`

```yulang
my (a, b) = (1, 2)
my { x, y } = some_point
my [first, ..rest] = some_list
```

These are irrefutable patterns — the compiler assumes they will match. A
non-exhaustive pattern in a `my` binding is a type error.

## See also

- [Functions → Record patterns as optional arguments](./functions)
- [Control Flow → catch](./control-flow)
- [Errors → Catching by name](./errors)
