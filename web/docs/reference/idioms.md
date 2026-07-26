# Idioms

Use the forms on this page as the defaults for ordinary Yulang code. They keep
calls and control flow readable while taking advantage of the language's
punctuation-free forms.

## Bare application

Use `f x y` as the everyday call form. Reach for `f(x, y)` only to group
arguments visually or when an argument is a literal that would otherwise chain
into the next token; for example, `f(-1)` can be clearer than `f -1`.

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

Keep the dot tight for the first selection, and put a space before later dots
that should land on the outer bare-application expression. Selection itself is
not application: `xs.map` selects a function, and the following argument
applies it. The space before `.filter` below closes the current argument, so the
chain means `(xs.map double) .filter ...`, not `xs.map (double.filter ...)`.

```yulang
xs.map double .filter (\x -> x > 0) .len
```

At the top level both spellings work — `xs.map` and `xs .map` resolve to the
same field selection. The difference only matters when the dotted expression
sits inside an ML-style argument list. See
[Application](./application#whitespace-is-significant) for the precise rule.

## `with:` blocks for companion methods

Put companion methods in the declaration's `with:` block. Method headers
`our recv.name args = body` make `value.name args` resolve to the method without
an extra `self` parameter declaration.

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
    our p.scale n = point { x: p.x * n, y: p.y * n }
```

## Attached `impl` inside `with:`

Use an attached `impl` to avoid spelling the enclosing struct name twice. The
enclosing type is prepended as the role's first argument; write the remaining
role arguments after the role name.

```yulang
struct box 'a { value: 'a } with:
    impl Index int:
        type value = 'a
        our b.index _ = b.value
```

## Receiver style in roles

Write role methods in receiver form. `our a.method: T` gives implementors
`value.method` of type `T`; the receiver name is informational, so choose one
that makes the role read clearly.

```yulang
role Eq 'a:
    our a.eq: 'a -> bool

role Add 'a:
    our a.add: 'a -> 'a
```

## `error E:` over hand-rolled enums

Use `error E:` instead of writing the enum, effect, `Throw` and `Display`
implementations, and `wrap` helper by hand. An `up` helper is also generated
when the declaration has `from` entries. Use the long form only when the
generated surface does not fit.

```yulang
pub error path_err:
    not_found path
    denied path
```

## `fail e` over `e.throw`

Use `fail` to surface an error value into the effect row. The prefix form makes
the throw site easy to spot while scanning a function.

```yulang
fail path_err::not_found path
```

## `sub:` / `return` over deep nesting

Use `sub:` and `return` to keep the successful path flat instead of nesting
conditionals. `sub:` opens the early-return scope.

```yulang
sub:
    if not config.valid: return default
    my parsed = parse config
    if parsed.empty: return default
    process parsed
```

## `$x` / `&x` for local mutability

Use explicit reference syntax when a local mutable cell is needed. The compiler
turns it into a handled `var` effect, so mutation remains visible to the type
system.

```yulang
my incremented =
    my $count = 0
    &count = $count + 1
    $count
```

## Effectful `if`

Use an effectful condition when the condition itself is nondeterministic.
`std::control::junction` supplies the effectful boolean operations accepted by
`if`; ordinary `bool` conditions follow the usual path.

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    "overlap"
else:
    "no overlap"
```

## Lean on inference, annotate at boundaries

Let inference recover local types, and annotate public API boundaries, generic
constraints, or residual variables that need to be fixed. The pipeline `x | f`
feeds the left-hand value to the right-hand expression, like F# or Elixir's
`|>`, but with one bar.

```yulang
my parse text = text
my render text = text
pub our_pipeline = "data" | parse | render

pub our_pipeline_typed(value: str): str =
    value | parse | render
```

## See also

- [Syntax Style](./syntax-style) — the precise whitespace and colon rules
- [Cookbook](../guide/cookbook) — task-oriented recipes
- [Pitfalls](../guide/pitfalls) — common gotchas
