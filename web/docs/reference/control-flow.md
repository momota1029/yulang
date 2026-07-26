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

`if` expects a `bool` condition. An `if` without `else` is statement-like: the
then-branch is evaluated for its effects, its value is discarded, and the whole
expression returns `()`.

## `elsif`

`elsif` adds another condition between `if` and `else`. Conditions are tried
from left to right; the first true branch wins, and `else` handles the case
where every condition is false.

```yulang
my size n =
    if n < 0: "negative"
    elsif n == 0: "zero"
    elsif n < 10: "small"
    else: "large"

say (size 7)
```

## `case`

```yulang
case value:
    0 -> "zero"
    n if n < 0 -> "negative"
    _ -> "other"
```

`case` arms are tried top-to-bottom. Guards use `if` after the pattern.

### Guards

A `case` guard follows the pattern with `if` or `where`. The guard can use
names bound by the pattern. It runs only after that pattern matches; when it
returns false, matching continues with the next arm.

```yulang
my sign n = case n:
    value if value < 0 -> "negative"
    value if value == 0 -> "zero"
    _ -> "positive"

say (sign 3)
```

## `catch`

```yulang
catch action:
    console::read(), k -> k "42"
    value -> value
```

An operation arm receives the operation payload and a continuation `k`. Calling
`k value` resumes the computation. A value arm handles normal completion.

### Guards

A `catch` guard follows the operation pattern and continuation with `if` or
`where`. A false guard leaves that arm unselected and tries the next matching
arm.

```yulang
act signal:
    our ask: () -> int

my result = catch signal::ask():
    signal::ask(), k if false -> 0
    signal::ask(), k -> k 42
    value -> value

say result
```

## Labels on `case` and `catch`

`case 'label value:` and `catch 'label action:` give the entire arm set a
recursive name. The label belongs to the arm set, not to an individual arm.
Calling `'label next` from a body applies the same `case` or `catch` arms to
`next`.

```yulang
my result = case 'count 3:
    0 -> "done"
    n -> 'count (n - 1)

say result
```

The same spelling re-enters a labelled `catch`:

```yulang
my result = catch 'again 3:
    n if n > 0 -> 'again (n - 1)
    n -> n

say result
```

## `for`

```yulang
for x in 0..10:        // 11 iterations: 0..10 is inclusive (0..<10 is half-open)
    say x
```

`for x in xs:` iterates over a value implementing `Fold`. The body is lowered to
a function, and a plain `for` expression returns `()`.

Loop control comes from the prelude:

```yulang
for x in 0..:
    if x == 10: last
```

`last`, `next`, and `redo` break, skip, or restart the current iteration.

## Labels

```yulang
for 'outer x in 0..:
    for y in 0..:
        if y == 3: last 'outer
```

Labelled loops pass a label value to the body. Prefix forms such as
`last 'outer`, `next 'outer`, and `redo 'outer` target that labelled loop.

## `sub` and `return`

```yulang
sub:
    for x in 0..:
        if x == 5: return x
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

## Blocks and Lambdas

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
