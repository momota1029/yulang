# Yulang Language Overview

This page is a user-facing overview of Yulang as it exists today. The language is still experimental, so this document describes the current implementation rather than a stability promise.

For a Japanese version, see [overview.ja.md](overview.ja.md).

## What Yulang Is

Yulang is an expression-oriented programming language built around type inference, structural types, roles, and algebraic effects.

It aims to keep everyday code compact while still making advanced control flow visible in the type system. Features such as early return, loops, local references, nondeterministic search, and effectful boolean conditions are not special runtime hacks; they are mostly expressed through effects, handlers, roles, and standard library definitions, with a few syntax rules that connect those pieces.

Current highlights:

- indentation and brace blocks
- local and public bindings
- structs, enums, nominal `type` declarations, and companion methods
- record, tuple, list, and enum patterns
- Simple-sub-inspired type inference with subtyping
- role-based ad-hoc polymorphism
- user-defined operators
- algebraic effects and `catch` handlers
- `sub:` / `return` for early-exit control flow
- `for` loops with `last`, `next`, and `redo`
- explicit reference syntax with `$x` and `&x = value`
- nondeterminism through `std::undet`
- effectful boolean conditions through `std::junction`

## A Small Program

```yulang
struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2
```

This defines a nominal `point` type with fields `x` and `y`, adds a method through `with:`, constructs a value, and calls the method with `.norm2`.

The compiler registers:

- `point` as a type
- `point` as a constructor
- `point::x` and `point::y` as field accessors
- `point::norm2` as a companion method

The surface expression `.norm2` is resolved after type inference has enough information about the receiver.

## Running Code

Use `--run` to execute a file:

```bash
cargo run -q -p yulang -- --run examples/01_struct_with.yu
```

Use `--infer` to print inferred public bindings:

```bash
cargo run -q -p yulang -- --infer examples/08_types.yu
```

Example output:

```text
answer : int
twice : Add<α> => α -> α
```

The `Add<α>` part is a role requirement. It says `twice` works for any type `α` that has an `Add` implementation.

## Source Files and Modules

Yulang source files are modules. Imports use `use`:

```yulang
use std::undet::*
use std::list::{map, filter}
```

The compiler implicitly imports the prelude for ordinary entry files:

```yulang
use std::prelude::*
```

The standard library lives in `lib/std`, but its module path is `std::...`.

## Blocks and Bindings

Yulang is expression-oriented. Blocks evaluate their statements in order and return the last expression.

```yulang
{
    my x = 1
    my y = 2
    x + y
}
```

Bindings can be local or exported:

```yulang
my local_value = 1
our shown_by_infer = 2
pub exported = 3
```

Function arguments can be written directly in a binding header:

```yulang
our twice x = x + x
```

This behaves like a function value:

```yulang
our twice = \x -> x + x
```

## Layout

Blocks can use indentation:

```yulang
if x == 0:
    1
else:
    2
```

or braces:

```yulang
if x == 0 { 1 } else { 2 }
```

The colon form is also used as a compact application/block syntax:

```yulang
sub:
    return 1
```

## Data Types

### Structs

`struct` defines a nominal record-like type.

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
```

Construction uses record syntax:

```yulang
point { x: 3, y: 4 }
```

Fields are available through generated accessors and through selection syntax:

```yulang
my p = point { x: 3, y: 4 }
p.x
p.norm2
```

### Enums

`enum` defines a nominal variant type.

```yulang
enum opt 'a = nil | just 'a
```

Patterns can match variants:

```yulang
case value:
    opt::just x -> x
    opt::nil -> 0
```

### Nominal `type`

`type` declares a nominal type and opens a companion module.

```yulang
type list 'a with:
    our xs.append ys = std::list::append xs ys
```

In the current implementation, `type` is not a type alias. It is used for opaque, primitive, or self-structured nominal types and their companion methods.

A `type` can define its internal field shape with `struct self`:

```yulang
type ref 'e 'a with:
    struct self:
        get: () -> ['e] 'a
        update_effect: () -> [ref_update 'a; 'e] ()
```

## Patterns

Patterns appear in function arguments, `case`, `catch`, and local bindings.

```yulang
my area({width = 1, height = 2}) = width * height
```

This is a record pattern with default values. It makes both fields optional for callers:

```yulang
area { width: 3 }
area {}
area { width: 3, height: 4 }
```

Defaults are evaluated when the field is missing. Later defaults can refer to earlier fields:

```yulang
my next_area({width = 2, height = width + 1}) = width * height
```

List patterns support prefix, spread, and suffix:

```yulang
case xs:
    [] -> 0
    [head, ..tail] -> head
```

## Roles and Operators

Roles are Yulang's ad-hoc polymorphism mechanism.

```yulang
role Add 'a:
    our a.add: 'a -> 'a

impl Add int:
    our x.add y = std::int::add x y
```

Operators are ordinary bindings connected to roles or functions by the prelude.

```yulang
our twice x = x + x
```

The inferred type is:

```text
twice : Add<α> => α -> α
```

This means `+` is not fixed to `int`; it resolves through the `Add` role.

Users can also define operators with fixity and binding power:

```yulang
pub infix (++) 4.0.0 4.0.0 = append
```

## Effects and Handlers

Yulang has algebraic effects. An `act` declares operations:

```yulang
act console:
    pub read: () -> str
    pub write: str -> ()
```

`catch` handles computations that may perform effects:

```yulang
catch action:
    some_effect payload, k -> k payload
    value -> value
```

An effect arm receives the operation payload and a continuation. Calling the continuation resumes the computation.

## `sub:` and `return`

Early return is implemented with effects.

```yulang
sub:
    return 1
```

The standard library defines a `sub` effect with a `return` operation. The `sub:` syntax applies the standard handler, so code can be written in a direct style.

This also works with loops:

```yulang
sub:
    for x in 0..:
        if x == 5: return x
        else: ()
    0
```

## `for`, `last`, `next`, and `redo`

`for` has dedicated syntax, but iteration is based on the standard `Fold` role.

```yulang
for x in 0..:
    if x == 5: last
    else: ()
```

The lowerer turns a loop into a call similar to:

```text
std::flow::loop::for_in xs (\x -> body)
```

The `last`, `next`, and `redo` operations are loop effects exposed through prelude operators.

## References

References are explicit.

```yulang
{
    my $x = 10
    &x = $x + 1
    $x
}
```

`$x` reads the current value. `&x = value` writes a new value.

Internally, this is implemented with a local synthetic effect based on `std::var::var`, not as an ordinary mutable slot. This matters because reference behavior participates in the effect system.

## Nondeterminism

The `std::undet` module defines nondeterministic computation.

```yulang
use std::undet::*

(each [1, 2, 3] + each [4, 5, 6]).list
```

`each` chooses one value from a collection. `.list` runs the computation and collects every result.

```yulang
use std::undet::*

{
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
}.once
```

`.once` returns the first result as an `opt` value.

## Effectful Conditions

Yulang's `if` can work with effectful boolean conditions through `std::junction`.

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

When an `if` condition is pure, it is checked as a normal `bool`. When the condition is effectful, the lowerer inserts `junction::junction` so the standard library can interpret the condition.

This is one of the places where syntax and the standard library deliberately meet.

## Type Inference

Every expression has both a value type and an effect type. Most programs do not need explicit annotations, but annotations can be used to constrain or document a binding:

```yulang
our p.norm2: int = p.x * p.x + p.y * p.y
```

The inference engine supports:

- structural records and tuples
- nominal types
- function types
- row-like effect types
- role requirements
- subtyping

Use `--infer` to inspect public inferred types.

## What Is Still Experimental

The current implementation contains some parser-level features that are not yet full language features. In particular, rule and mark syntax can be parsed, but it is not currently meaningful as ordinary Yulang expressions.

There are also runtime-lowering and monomorphization limitations. Some examples infer successfully but do not currently run in the dirty development workspace because residual polymorphic runtime IR remains.

This overview should therefore be read as "how the current language works" rather than "what will remain stable."

## Where to Read Next

- `examples/*.yu` shows small executable programs.
- `lib/std/*.yu` shows how much of the language behavior is expressed in the standard library.
- `notes/design/yulang-language-report.md` is a deeper implementation-derived report.
