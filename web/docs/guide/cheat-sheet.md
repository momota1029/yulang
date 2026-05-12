# Cheat Sheet

A one-page overview of Yulang's syntax. Each section is a quick reminder; the
language reference has the full story.

## Bindings

```yulang
my x = 1                       // private
our exposed = 2                // companion-visible
pub exported = 3               // top-level export

my add x y = x + y             // arguments after the name
my (a, b) = (1, 2)             // destructure
\x -> x + 1                    // lambda
\x y -> x + y                  // curried lambda
```

## Application forms

```yulang
f x y                          // bare application
f(x, y)                        // C-style call (curried under the hood)
f: x                           // colon application
f.method                       // dot selection (apply by following with args)
xs[0]                          // index
```

Whitespace matters: `f(x)` is a call; `f (x)` is bare application of `f` to
`(x)`; `f: x` is colon application; `f :x` would be bare application of `f` to
the symbol `:x`.

## Blocks and layout

```yulang
{ my x = 1; x + 1 }            // brace block
my big =
    my x = 1                   // indented block continues a binding
    x + 1
```

`:` introduces a layout block at the end of a statement-like form.

## Conditionals

```yulang
if cond: a else: b
if cond { a } else { b }

case value:
    0 -> "zero"
    x if x > 0 -> "positive"
    _ -> "other"
```

## Loops and early exit

```yulang
for x in 0..10:
    println x.show

for x in xs:
    if pred x: last
    else: next

sub:
    for x in xs:
        if x == target: return x
        else: ()
    default
```

## Data types

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

enum opt 'a = nil | just 'a

type ref 'e 'a with:
    struct self:
        get: () -> ['e] 'a
```

## Patterns

```yulang
case v:
    0 -> ...                   // literal
    x -> ...                   // bind
    _ -> ...                   // wildcard
    (a, b) -> ...              // tuple
    { x, y = 1 } -> ...        // record with default
    [head, ..tail] -> ...      // list spread
    just x -> ...              // enum variant (prelude)
    color::red -> ...          // enum variant (qualified)
```

## Effects

```yulang
act log:
    pub put: str -> ()

catch action:
    log::put msg, k -> k ()
    v -> v
```

Function types carry an effect row: `path -> [fs; e] str`.

## Errors

```yulang
error fs_err:
    not_found path
    denied path

fail fs_err::not_found "x"

catch read_or_throw:
    fs_err::not_found p, _ -> recover p
    v -> v

fs_err::wrap: read_or_throw
```

## References

```yulang
my $count = 0
&count = $count + 1
$count
```

## Roles and impls

```yulang
role Add 'a:
    our a.add: 'a -> 'a

impl Add int:
    our x.add y = std::int::add x y

my twice x = x.add x           // inferred: Add<α> => α -> α
```

## Operators

```yulang
pub prefix(not) 8.0.0 = std::bool::not
pub infix (+) 5.0.0 5.0.0 = \x -> \y -> x.add y
pub suffix (..) 8.0.0 = std::range::from_included
pub lazy infix(or) 1.0.0 1.0.0 = \a -> \b -> if a(): true else: b()
```

## Modules and imports

```yulang
use std::undet::*
use std::list::{map, filter}
use std::ops::* without (+), debug
```

## Comments

```yulang
// line comment
/* block comment */
-- single-line doc
---
multi-line doc
---
```

## Print inferred types

```bash
cargo run -q -p yulang -- --infer examples/showcase.yu
```

## See also

- [Tour](./tour) — narrative walkthrough
- [Cookbook](./cookbook) — task-oriented recipes
- [Reference](../reference/) — full language reference
- [Idioms](../reference/idioms) — the Yulang style
