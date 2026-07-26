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
| `"yes" \| "y"` | either alternative (OR pattern) |
| `pat as value` | `pat`, while also binding the whole value |
| `(a, b)` | tuple |
| `{ x, y }` | record with fields named `x` and `y` |
| `{ x = 0, y }` | record with default for `x` |
| `{ x: name }` | record field `x` renamed to `name` |
| `[]`, `[1, 2]`, `[x, ..rest]` | list patterns |
| `[..init, last]` | list with spread at head |
| `:ready` | symbol |
| `:some value` | polyvariant with a payload |
| `just x`, `nil` | enum variants re-exported by the prelude |
| `opt::just x`, `opt::nil` | enum variants by qualified path |
| `tag x` | enum variant by short name (after `use enum::*`) |

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

## OR patterns

An OR pattern `left | right` tries its alternatives from left to right and
matches when either one matches.

```yulang
my affirmative answer = case answer:
    "yes" | "y" -> true
    _ -> false

say (affirmative "y")
```

OR alternatives do not merge their bindings. The checker currently accepts
different binding names, and even the same spelling in both alternatives
creates separate bindings. If the body refers to a binding that the selected
alternative did not create, execution fails with an unbound-local runtime
error. Keep OR alternatives free of bindings, or alias the whole OR pattern.

## `as` aliases

An `as` pattern `pattern as name` matches the inner pattern and also binds the
whole input value to `name`.

```yulang
my normalize answer = case answer:
    ("yes" | "y") as matched -> matched
    _ -> "no"

say (normalize "y")
```

The parentheses put the alias outside the whole OR pattern, so either
alternative creates `matched`.

## Type patterns are not available

The parser accepts `pattern: type`, but the checker does not currently enforce
the annotation in a `case` pattern. It is not a runtime type test: `text: str`
below still matches the `int` value as an ordinary name binding.

```yulang
my result = case 41:
    text: str -> "annotation ignored"
    _ -> "fallback"

say result
```

This prints `annotation ignored`. Do not use pattern annotations to test or
constrain a value's type.

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
my rec = { x: 1, y: 2 }

case rec:
    { x, .._ }    -> x
    { ..tail, y } -> y    // `tail` binds the whole record, not the leftover
```

`..name` binds the **entire** input record (record subtraction is not provided
as a stable feature, since record difference is not fully expressible in the
type system). The spread can appear at either side of the field list, but in
both positions `name` ends up with every field from the input — including the
ones listed by name. Use `.._` when you only need to assert "and any other
fields", without binding them.

## List patterns

```yulang
case xs:
    []              -> "empty"
    [only]          -> "single: " + only.show
    [first, second] -> "pair"
    [head, ..tail]  -> "head: " + head.show
    [..init, end]   -> "ends with: " + end.show
```

Spread `..rest` captures the unmatched portion. A list pattern can have at most
one spread.

## Symbol patterns

A symbol pattern `:name` matches the symbol value with the same name. Symbols
have no payload.

```yulang
my state_name state = case state:
    :ready -> "ready"
    :waiting -> "waiting"

say (state_name :ready)
```

## Polyvariant patterns

A polyvariant pattern `:name payload ...` matches the named tag and applies its
payload patterns in order.

```yulang
my unwrap option = case option:
    :some value -> value
    :none -> 0

say (unwrap (:some 42))
```

Unlike enum variants, symbols and polyvariants need no declaration or
qualified companion-module path.

## Enum patterns

```yulang
enum color = red | green | blue

case c:
    color::red   -> 0
    color::green -> 1
    color::blue  -> 2
```

Variants live in the enum's companion module, so the usual spelling is
`color::red`. **Unqualified `red` requires `use color::*`** — without the
`use`, plain `red` in expression position is a name error, and in pattern
position it silently becomes a fresh binding (an unrelated variable named
`red` that matches anything). The latter is dangerous:

```yulang
enum color = red | green | blue
case c:
    red -> "r"      // `red` is a fresh variable that matches every value;
                    // the `green` and `blue` arms below become unreachable.
    green -> "g"
    blue -> "b"
```

To pattern-match against the variant, either qualify (`color::red`) or import
with `use color::*` first.

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
    path_err::not_found _, _ -> "(missing)"
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

`my` destructuring assumes that its pattern matches. The binding does not
perform an exhaustiveness check.

## See also

- [Functions → Record patterns as optional arguments](./functions)
- [Control Flow → catch](./control-flow)
- [Errors → Catching by name](./errors)
