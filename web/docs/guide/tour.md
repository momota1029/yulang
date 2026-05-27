# Tour

A compact walkthrough of Yulang's key features. You can run all examples in the <a href="/" target="_self">Playground</a>.

## Basics

```yulang
1 + 2
```

Every top-level expression is evaluated and its result is shown. Functions are declared with `my`:

```yulang
my double x = x + x
double 21
```

## Structs

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

The `with:` block attaches methods to the struct. `our` makes them part of the public companion module.

## Optional arguments

Record patterns with defaults act like optional named arguments:

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area {}
area { width: 3, height: 4 }
```

Defaults are evaluated left-to-right and may reference earlier fields:

```yulang
my f {a = 1, b = a + 1, c = b + 1} = (a, b, c)
f {}             // (1, 2, 3)
f { a: 10 }      // (10, 11, 12)
```

## Mutable bindings

A binding declared with `my $x = ...` is mutable. `$x` reads it, and `&x = v` writes it:

```yulang
my $x = 10
&x = $x + 1
$x
```

The same `&` form also works for fields and indexed elements:

```yulang
my $xs = [2, 3, 4]
&xs[1] = 6
$xs
```

## Nondeterminism

`each` makes a choice; `.list` collects all results:

```yulang
(each [1, 2, 3] + each [4, 5, 6]).list
```

`.once` returns the first useful result as `opt`. With infinite choices, constrain later choices from earlier ones so the search reaches a result quickly:

```yulang
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once
```

## Junctions

`all` and `any` make comparisons effectful. They lift comparisons over a collection so a single `if` covers every pair:

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

## Effects

Effects are declared, called, and handled:

```yulang
act console:
    our read: () -> int

our ask() = console::read()

our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k 42)

run_console:
    ask()
```

The type of `run_console` removes the `console` effect from its argument. The handler arm receives the operation arguments and a continuation `k`; calling `k value` resumes the computation.

## Loops and early exit

`for x in xs:` iterates over anything that implements `Fold` (lists, ranges, …). `last`, `next`, `redo` control the loop. `sub:` introduces an early-return scope, and `return value` exits it:

```yulang
sub:
    for x in 0..:
        if x == 5: return x
    0
```
