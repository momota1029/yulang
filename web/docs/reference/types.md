# Values & Types

## Primitive types

| Type    | Examples              |
|---------|-----------------------|
| `int`   | `0`, `42`, `-7`       |
| `float` | `3.14`, `-0.5`        |
| `bool`  | `true`, `false`       |
| `str`   | `"hello"`, `"world"`  |
| `()`    | `()` (unit)           |
| `never` | uninhabited; the type of expressions that don't return |

## Tuples

```yulang
(1, "hello", true)
```

Tuples are positional products. Their elements can be destructured with patterns, e.g. `my (a, b, c) = triple`.

## Lists

```yulang
[1, 2, 3]
```

A list of `'a` values has type `list 'a`. Index with `xs[i]` (the `Index` role on `list 'a`).

## Records

```yulang
{ x: 3, y: 4 }
```

Anonymous products with named fields. Field access uses `.field`.

## Optional

```yulang
opt::just 42
opt::nil
```

`opt 'a` is the standard library type `enum opt 'a = nil | just 'a`.

## Result

```yulang
result::ok 1
result::err "bad"
```

`result 'ok 'err` is the standard library type for fallible computations.

## Ranges

```yulang
0..<10  // 0 to 9 (exclusive)
0..10   // 0 to 10 (inclusive)
0..     // 0 upward (unbounded)
```

`..`, `..<`, `<..`, `<..<` are range operators in `std::range`. Ranges implement `Fold`, so they work with `for x in r:` and the nondeterminism `each` collector.

## Type variables

Type variables use the `'a` prefix:

```yulang
my id('a x: 'a): 'a = x
```

Type inference fills in type variables automatically in most cases — annotations are only needed for clarity or for resolving ambiguity.

## Function types

```yulang
int -> int
[console] str -> ()
```

Arrow types may carry an effect row `[...]` between the arrow and parameter type. `->` is plain ASCII.

## Effect rows

Effect rows appear in type signatures with `[...]`:

```
[console; r] str -> ()
```

A row lists the named effects, optionally followed by `; r` (a row variable) to indicate "any other effects." A function that performs no effects has an empty row `[]` (or simply uses a row variable that solves to empty).

## Role constraints

Constraints are introduced with `where`:

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

The same form works inside a `role`/`impl` body and inside a binding body. `where` clauses constrain a type variable to implement one or more roles.
