# Functions

## Declaration

```yulang
my add x y = x + y
```

`my` declares a private binding. `our` makes it part of the enclosing module's companion. `pub` exports it.

A binding without arguments is a value; with arguments, it's a function curried left-to-right.

## Calling

```yulang
add 1 2
```

Function application is juxtaposition, left-associative. Parentheses are used for grouping and for tuples, not for invocation.

## Lambdas

```yulang
\x -> x + 1
\x y -> x + y
```

Lambdas start with `\`. Multi-argument lambdas are written `\x y -> ...`.

## Record patterns as optional arguments

```yulang
my area({width = 1, height = 2}) = width * height

area { width: 3 }            // height defaults to 2
area {}                      // both default
area { width: 3, height: 4 }
```

Field patterns with defaults let callers omit any subset of arguments. Defaults are evaluated left-to-right, so a later default may reference an earlier field:

```yulang
my f({a = 1, b = a + 1}) = (a, b)
```

## Type annotations

A parameter or result type can be written explicitly:

```yulang
my double (x: int): int = x + x
```

Type annotations are optional — Simple-Sub inference fills them in — but they help with documentation and ambiguity resolution.

## Effect annotations

A function's effect row appears in brackets between the arrow and the parameter type:

```yulang
my echo(s: str): [console] () = println s
```

A wildcard `[_]` stands for "any effects":

```yulang
my run(action: [_] _) = catch action:
    ...
```

## `sub:` and early return

`sub:` introduces an early-return scope. `return value` exits the innermost `sub:`:

```yulang
my f() = sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

Both `sub` and `return` are defined in `std::flow`, exposed through the prelude.

## `for` loops

```yulang
for x in 0..10:
    println x.show
```

`for x in xs:` works on any value implementing `Fold` — lists, ranges, and user types that provide a `fold` method. `for` is an expression that yields `()`.

Inside a `for` body you can use `last`, `next`, and `redo` (from the prelude) to break out of, skip, or restart the current iteration.
