# Functions

## Declaration

```yulang
my add x y = x + y
```

`my` declares a private binding. `our` and `pub` expose a binding from the
current module; in generated companion modules, `our` is the usual way to expose
methods and operations.

The left-hand side of a binding is a pattern. When the pattern is a direct name,
additional patterns after the name become function arguments:

```yulang
my x = 1
my add x y = x + y
my (a, b) = (1, 2)
```

Multiple arguments are curried left-to-right.

## Calling

```yulang
add 1 2
add(1, 2)
```

Yulang supports both whitespace application and tight C-style call syntax.
`add 1 2` and `add(1, 2)` both lower to curried application. Parentheses are
also used for grouping, tuples, and the unit value `()`, so whitespace matters:
`f(x)` is a call, while `f (x)` is whitespace application of the grouped
expression `(x)`.

## Lambdas

```yulang
\x -> x + 1
\x y -> x + y
```

Lambdas start with `\`. Multi-argument lambdas are written `\x y -> ...`.

## Record patterns as optional arguments

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }            // height defaults to 2
area {}                      // both default
area { width: 3, height: 4 }
```

Field patterns with defaults let callers omit any subset of arguments. Defaults are evaluated left-to-right, so a later default may reference an earlier field:

```yulang
my f {a = 1, b = a + 1} = (a, b)
```

## Type annotations

A parameter or result type can be written explicitly:

```yulang
my double(x: int): int = x + x
```

Type annotations are optional — Simple-Sub inference fills them in — but they help with documentation and ambiguity resolution.

For effectful arguments or returns, see [Effects](./effects) and
[Values & Types](./types).
