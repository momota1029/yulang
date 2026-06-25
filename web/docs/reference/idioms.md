# Idioms

Yulang code is often shorter than the equivalent in C-style languages because
the language gives several ways to drop punctuation. This page collects the
idioms that make Yulang code read naturally.

## Bare application

```yulang
// Idiomatic
add 1 2
greet name
read_text path

// Less idiomatic in Yulang (still legal)
add(1, 2)
greet(name)
read_text(path)
```

`f x y` is the everyday call form. Reach for `f(x, y)` only when you need to
group arguments visually or when an argument is a literal that would otherwise
chain into the next token (`f(-1)` is sometimes clearer than `f -1`).

## Colon application for big tails

When the final argument is a block or another long expression, use `:` to push
it to the right.

```yulang
catch action:
    log::put msg, k -> handle msg
    v -> v

run_console:
    my answer = ask()
    say answer

io_err::wrap:
    read_text path
```

`f x: body` reads "apply `f` to `x` and then to the colon body". This is the
canonical way to invoke handler-like and block-shaped APIs.

## Method dot chains

```yulang
xs.map double .filter (\x -> x > 0) .len
```

`.method` is selection plus application. Methods are first-class — `xs.map`
returns a function expecting the closure. Notice the explicit spaces before
`.filter` and `.len`: inside a bare-application chain, a space closes the
current argument so the next dot lands on the outer expression. Here that
means `(xs.map double) .filter ...` rather than `xs.map (double.filter ...)`.

At the top level both spellings work — `xs.map` and `xs .map` resolve to the
same field selection. The difference only matters when the dotted expression
sits inside an ML-style argument list. See
[Application](./application#whitespace-is-significant) for the precise rule.

## `with:` blocks for companion methods

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
    our p.scale n = point { x: p.x * n, y: p.y * n }
```

A struct or `type` declaration's `with:` opens the companion module. Method
headers `our recv.name args = body` make `value.name args` resolve to the
method, without an extra `self` parameter declaration.

## Attached `impl` inside `with:`

```yulang
struct box 'a { value: 'a } with:
    impl Index int:
        type value = 'a
        our b.index _ = b.value
```

Attached `impl` blocks save you from spelling the struct name twice. The
enclosing type is prepended as the role's first argument; remaining role
arguments are written after the role name.

## Receiver style in roles

```yulang
role Eq 'a:
    our a.eq: 'a -> bool

role Add 'a:
    our a.add: 'a -> 'a
```

The `our a.method: T` form reads as "implementors gain `value.method` of type
`T`". The receiver name is informational — pick whatever makes the role read
nicely.

## `error E:` over hand-rolled enums

```yulang
pub error path_err:
    not_found path
    denied path
```

A line of `error E:` is the same as writing the `enum`, the `act`, the
`Throw` impl, the `Display` impl, and the `wrap` / `up` helpers by hand.
Reach for the sugar; only drop to the long form when you need to deviate.

## `fail e` over `e.throw`

```yulang
fail path_err::not_found path
```

`fail` is the prefix operator that surfaces an error value into the effect
row. Using `fail` makes the throw site easy to spot when scanning a function.

## `sub:` / `return` over deep nesting

```yulang
sub:
    if not config.valid: return default
    my parsed = parse config
    if parsed.empty: return default
    process parsed
```

`sub:` opens an early-return scope. Use it to keep the happy path flat
instead of nesting conditionals.

## `$x` / `&x` for local mutability

```yulang
my $count = 0
&count = $count + 1
```

When you really do want a mutable cell, use the explicit reference syntax.
The compiler turns it into a handled `var` effect, so the mutation is still
visible to the type system.

## Effectful `if`

```yulang
if all xs < any ys:
    "overlap"
else:
    "no overlap"
```

Effectful boolean conditions go through `std::control::junction`. Use them when the
condition itself is non-deterministic; ordinary `bool` conditions still work
plainly.

## Lean on inference, annotate at boundaries

```yulang
pub our_pipeline = read_text "data.txt" | parse | render

pub our_pipeline_typed(path: path): [file, io_err] str =
    read_text path | parse | render
```

`x | f` feeds the left-hand value to the right-hand expression — the same
shape as F#'s `|>` or Elixir's `|>`, written with a single bar.

Inference recovers most types. Annotate when the type would document an API
boundary, when you want to constrain a generic, or when the inferred shape
includes residual variables you want pinned.

## See also

- [Syntax Style](./syntax-style) — the precise whitespace and colon rules
- [Cookbook](../guide/cookbook) — task-oriented recipes
- [Pitfalls](../guide/pitfalls) — common gotchas
