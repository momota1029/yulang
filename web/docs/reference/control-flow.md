# Control Flow

Control-flow forms are expressions unless noted otherwise.

## `if`

```yulang
if x > 0: "positive" else: "non-positive"

if cond:
    a
else:
    b

if cond { a } else { b }
```

`if` expects a `bool` condition. An `if` without `else` uses `()` as the false
branch.

## `case`

```yulang
case value:
    0 -> "zero"
    n if n < 0 -> "negative"
    _ -> "other"
```

`case` arms are tried top-to-bottom. Guards use `if` after the pattern.

## `catch`

```yulang
catch action:
    console::read(), k -> k "42"
    value -> value
```

An operation arm receives the operation payload and a continuation `k`. Calling
`k value` resumes the computation. A value arm handles normal completion.

## `for`

```yulang
for x in 0..10:
    println x.show
```

`for x in xs:` iterates over a value implementing `Fold`. The body is lowered to
a function, and a plain `for` expression returns `()`.

Loop control comes from the prelude:

```yulang
for x in 0..:
    if x == 10: last
    else: ()
```

`last`, `next`, and `redo` break, skip, or restart the current iteration.

## Labels

```yulang
for 'outer x in 0..:
    for y in 0..:
        if y == 3: last 'outer
        else: ()
```

Labelled loops pass a label value to the body. Prefix forms such as
`last 'outer`, `next 'outer`, and `redo 'outer` target that labelled loop.

## `sub` And `return`

```yulang
sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

`sub:` creates an early-return scope. `return value` exits the innermost `sub:`.
The nullfix form `return` returns `()`.

Labelled `sub` works similarly:

```yulang
sub 'done:
    'done.return 42
    0
```

`sub`, `return`, `last`, `next`, and `redo` are standard-library/prelude
surface forms, not parser-only keywords.

## Blocks And Lambdas

```yulang
{
    my x = 1
    x + 1
}

\x -> x + 1
\x y -> x + y
```

Blocks evaluate statements in order and return the final expression. Lambdas
use `\` and may take multiple curried arguments.
