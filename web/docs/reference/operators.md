# Operator Declarations

Operators are ordinary exported definitions that also contribute syntax to the
parser table. A downstream file can only parse an operator after importing the
syntax that defines it.

## Fixities

```yulang
pub nullfix(return) = std::flow::sub::return ()
pub prefix(return) 1.0.0 = std::flow::sub::return

pub prefix(not) 8.0.0 = std::bool::not

pub infix (+) 5.0.0 5.0.0 = \x -> \y -> x.add y
pub suffix (..) 8.0.0 = std::range::from_included
```

Supported fixities are:

| Fixity | Example use |
|--------|-------------|
| `nullfix` | `return` |
| `prefix` | `not x`, `return x` |
| `infix` | `x + y` |
| `suffix` | `0..` |

Binding powers are written as dot-separated numbers such as `5.0.0`. Infix
operators take left and right binding powers.

## Lazy Operators

```yulang
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b ->
    if a: b() else: false
```

`lazy` operators receive the right-hand side as delayed computation. The
standard `and` and `or` operators use this to short-circuit.

## Importing Operators

```yulang
use std::ops::*
use my_ops::(+)
use my_ops::* without (+), debug
```

Operator syntax can be imported directly, through glob imports, or excluded
with `without`. This matters because the parser needs operator syntax before it
can parse later expressions.

## Prelude Operators

The standard prelude exports arithmetic, comparison, boolean, range, loop, and
return operators. They are still normal exported syntax; user code can define
similar operators in modules and import them explicitly.
