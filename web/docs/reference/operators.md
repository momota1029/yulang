# Operator Declarations

Operators in Yulang are ordinary exported definitions that also contribute
syntax to the parser table. A downstream file can only parse an operator
after importing the syntax that defines it.

## Fixities

```yulang
pub nullfix(return) = std::flow::sub::return ()
pub prefix(return) 1.0.0 = std::flow::sub::return

pub prefix(not) 8.0.0 = std::bool::not

pub infix (+) 5.0.0 5.0.0 = \x -> \y -> x.add y
pub suffix (..) 8.0.0 = std::range::from_included
```

| Fixity | Use site | Notes |
|---|---|---|
| `nullfix` | `return` | A keyword-like operator that takes no operands |
| `prefix` | `not x`, `return x`, `fail e` | One right-hand operand |
| `infix` | `x + y`, `xs ++ ys` | Two operands; takes left and right binding powers |
| `suffix` | `0..`, `x?` | One left-hand operand |

The operator name in `prefix(...)`, `infix (...)`, etc. uses parentheses when
the name is symbolic; ordinary identifier names like `not` and `return` go
in plain parentheses.

## Binding power

Binding powers are written as dot-separated decimal numbers such as `5.0.0`.
Larger numbers bind more tightly. Infix operators take a pair of binding
powers `<left>.<right>`, splitting in the middle to control associativity:

- `5.0.0 5.0.0` — left-associative at level 5 (the standard for `+` and `-`)
- `4.0.0 4.0.1` — slight bias to the right (right-associative)

A small reference of the prelude's choices:

| Operator | Binding |
|---|---|
| `or` | `1.0.0` (lazy) |
| `and` | `2.0.0` (lazy) |
| `==`, `!=`, `<`, `<=`, `>`, `>=` | `3.0.0` |
| `..`, `..<`, `<..`, `<..<` | `4.0.0` |
| `+`, `-` | `5.0.0` |
| `*`, `/` | `6.0.0` |
| `not` (prefix) | `8.0.0` |

When you introduce new operators in user code, try to fit between the prelude
levels rather than overlapping them.

## Lazy operators

A `lazy infix` body receives **both** operands as thunks (`() -> value`).
Force whichever side you need; the call site `a and b` looks like the eager
form and never has to introduce its own thunk. The prelude's `and` / `or` use
this to short-circuit:

```yulang
pub lazy infix(and) 2.0.0 2.0.0 = \a -> \b ->
    if a():
        b()
    else:
        false

pub lazy infix(or) 1.0.0 1.0.0 = \a -> \b ->
    if a():
        true
    else:
        b()
```

## Calling an operator like a function

The right-hand side of an operator declaration is just a binding, so you can
call the underlying function by path:

```yulang
1 + 2
std::ops::add 1 2     // explicit form (less idiomatic)
```

This is mostly useful when you want a first-class reference to the operator
implementation.

## Importing operators

```yulang
use std::ops::*
use my_ops::(+)
use my_ops::* without (+), debug
```

Operator syntax can be imported wholesale, by name (with parentheses for
symbolic operators), or with `without` to exclude specific names from a glob
import. This matters because the parser needs the operator definition in
scope before it can parse later expressions.

## Defining a new operator

```yulang
pub infix (++) 4.0.0 4.0.0 = \xs -> \ys -> xs.append ys

[1, 2] ++ [3, 4]   // [1, 2, 3, 4]
```

The body is an ordinary curried function. Pick a binding power that fits
where the operator belongs in the precedence hierarchy.

## Pitfalls

- A symbolic operator must be imported before its first use, or the parser
  rejects the expression with a parse error (not a name-resolution error).
- Both `pub prefix(name) ...` and the imported alias such as `use foo::(+)`
  pull the syntax into scope. They are not redundant; the path import does
  not bring the syntax with it.
- When two glob imports both expose the same operator name, use `without` on
  one of them to disambiguate.

## See also

- [Application & Operators](./application) — how parsed operators interact
  with bare application
- [Syntax Style](./syntax-style) — whitespace rules around symbol use
- [`std::ops`](./std/core) — prelude operator definitions
