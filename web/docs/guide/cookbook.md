# Cookbook

Short task-oriented recipes for everyday Yulang. Each recipe shows the idiomatic
shape and a one-line note. For deeper background, follow the cross-references
into the language reference.

The examples lean on Yulang's parens-light style — bare application `f x y`,
colon application `f: ...`, and indented blocks — rather than C-style calls.

## Define a value and a function

```yulang
my answer = 42
my greet name = "hello, " + name
greet "Yulang"
```

`my` makes a private binding. Arguments after the name become curried function
parameters.

[Functions](../reference/functions)

## Make a function public

```yulang
pub double x = x + x
```

`pub` exports the binding from the current module. `our` exposes it through
the containing companion (typical for methods).

[Modules](../reference/modules)

## Pattern-match with `case`

```yulang
my describe n =
    case n:
        0 -> "zero"
        x if x < 0 -> "negative"
        _ -> "positive"
```

Arms are tried top-to-bottom. A guard uses `if` after the pattern.

[Pattern Matching](../reference/patterns)

## Attach a method to a struct

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

`with:` opens the struct's companion module. The receiver `p` stands for the
value `.norm2` is called on.

[Structs & Roles](../reference/structs)

## Implement a role for a type

```yulang
impl Add point:
    our a.add b = point { x: a.x + b.x, y: a.y + b.y }
```

A role declares an interface; an `impl` provides the methods for a specific
type. The receiver `a` (and second argument `b` here) match the role's
method signatures.

[Structs & Roles](../reference/structs)

## Loop with an early break

```yulang
sub:
    for x in 0..:
        if x == 5: return x
    0
```

`sub:` opens an early-return scope. `return value` exits the innermost `sub:`.
Inside `for`, `last`, `next`, and `redo` control the loop itself.

[Control Flow](../reference/control-flow)

## Use a mutable local with `$x` / `&x`

```yulang
{
    my $count = 0
    &count = $count + 1
    &count = $count + 1
    $count
}
```

`my $x = …` introduces a local mutable binding. `$x` reads, `&x = value`
writes. Internally these compile to a small handled `var` effect, so they fit
the effect system rather than escaping it.

[Control Flow → References](../reference/control-flow)

## Read a text file

```yulang
my text = read_text "data.txt"
text.say
```

`str` widens to `path`, so a string literal is enough for ordinary paths.
Filesystem errors are raised as `fs_err` in the effect row. Wrap them only
when the caller needs a value-level `result`.

```yulang
case fs_err::wrap: read_text "data.txt":
    result::ok text -> text
    result::err _ -> ""
```

[std::fs](../reference/std/fs)

## Set up optional arguments

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area { width: 3, height: 4 }
area {}
```

A record pattern with defaults gives every field optional behavior at the call
site. Defaults evaluate left-to-right and may reference earlier fields.

[Functions](../reference/functions)

## Raise and catch a typed error

```yulang
my path = std::path::of_bytes (std::str::to_bytes "/tmp/data")

catch fs::read_text path:
    fs_err::not_found _, _ -> "(missing)"
    value -> value
```

`fail e` is short for `e.throw`. `catch` arms name the operation directly, so
errors are always caught by their concrete name.

[Errors](../reference/errors)

## Close an error effect into a `result`

```yulang
my path = std::path::of_bytes (std::str::to_bytes "/tmp/data")

case fs_err::wrap: fs::read_text path:
    result::ok text -> text
    result::err err -> err.show
```

`E::wrap` runs the thunk, catches the matching error effect, and returns a
`result` value. The `err` side is `Display`-able through the auto-generated
impl.

[Errors → wrap](../reference/errors)

## Aggregate several errors into one

```yulang
pub error io_err:
    fs from fs_err
    parse from parse_err

my read_and_parse path =
    io_err::up:
        my text = fs::read_text path
        parse_json text
```

`from` makes a wider error type wrap narrower ones. `io_err::up` lifts the
narrower errors into `io_err` inside the block.

[Errors → from aggregation](../reference/errors)

## Handle a custom effect

```yulang
pub act log:
    pub put: str -> ()

my run_into_strings(action: [log; _] _): (_, list str) =
    my $entries = []
    my result = catch action:
        log::put msg, k ->
            &entries = $entries + [msg]
            k ()
        v -> v
    (result, $entries)
```

`catch` removes the handled operation from the row. Each arm receives the
payload and a continuation `k`. Calling `k value` resumes the captured
computation.

[Effects](../reference/effects)

## Search nondeterministically

```yulang
use std::undet::*

(each [1, 2, 3] + each [10, 20]).list
```

`each xs` picks one element of `xs` nondeterministically. `.list` runs the
computation and collects every result. `.once`, `.logic`, and friends produce
other shapes.

[std::undet](../reference/std/undet)

## Effectful boolean conditions

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    "found at least one"
else:
    "no overlap"
```

Yulang's `if` accepts an `effectful` boolean condition through
`std::junction`. `all xs` and `any xs` express "every / some element of `xs`".

## Define a cast between two types

```yulang
struct user_id { raw: int }

cast(x: user_id): int = x.raw
cast(x: int): user_id = user_id { raw: x }

my id: user_id = 7
my raw: int = id
```

`cast(x: A): B = body` lowers to a `Cast A` impl with `type to = B`. The
compiler inserts the cast at expected-type boundaries such as annotations and
function arguments.

[Casts](../reference/casts)

## Larger examples

Combining the recipes above, you can already write small but real programs.
Every one of these runs in the Playground as-is.

### A tiny expression evaluator

`enum` plus a recursive function is enough for a calculator:

```yulang
enum expr =
    num int
    | add (expr, expr)
    | mul (expr, expr)

my eval e =
    case e:
        expr::num n -> n
        expr::add (a, b) -> eval a + eval b
        expr::mul (a, b) -> eval a * eval b

eval (expr::add (expr::num 2, expr::mul (expr::num 3, expr::num 4)))
// → 14
```

Carrying a tuple as a variant payload (`add (expr, expr)`) is the
straightforward way to express multi-argument constructors.

### Filtering a list with recursion

List spread patterns plus recursion give you a natural `filter`:

```yulang
my is_even n =
    std::int::eq (std::int::sub n (std::int::mul (std::int::div n 2) 2)) 0

my keep_evens xs =
    case xs:
        [] -> []
        [x, ..rest] ->
            my r = keep_evens rest
            if is_even x:
                [x] + r
            else:
                r

keep_evens [1, 2, 3, 4, 5, 6, 7, 8]
// → [2, 4, 6, 8]
```

### Aggregating in a loop

A local `my $x = ...` is the natural way to thread a value through a loop:

```yulang
{
    my $best = 0
    for y in [3, 1, 4, 1, 5, 9, 2, 6, 5, 3]:
        if y > $best: &best = y
    $best
}
// → 9
```

`$best` does not escape the block — the type system makes sure mutable state
stays in the scope where it was introduced.

### Nondeterministic search

`each` plus `guard` lets you describe what you want and have the runtime
find it:

```yulang
use std::undet::*

{
    my a = each 1..20
    my b = each a..20
    my c = each b..20
    guard: a * a + b * b == c * c
    (a, b, c)
}.list
// → [(3, 4, 5), (5, 12, 13), (6, 8, 10), (8, 15, 17), ...]
```

Swap `.list` for `.once` to stop after the first success. Passing each
choice into the range of the next prunes the search early.

## See also

- [Tour](./tour) — a walk through the same features in narrative form.
- [Reference](../reference/) — the full language reference.
- [Syntax Style](../reference/syntax-style) — when and how to drop
  parentheses.
