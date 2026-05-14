# Functions

## Declaration

```yulang
my add x y = x + y
our greet name = "hello, " + name
pub double x = x + x
```

The left-hand side of a binding is a pattern. When the pattern is a direct
name, additional patterns after the name become function arguments.

| Keyword | Where the binding lives |
|---|---|
| `my` | Private to the current module / block |
| `our` | Visible through the enclosing companion (the usual choice for methods) |
| `pub` | Exported across module boundaries |

## Arguments and currying

```yulang
my add x y = x + y
my add' = \x -> \y -> x + y
```

Multi-argument bindings are curried left-to-right. `add 1` yields a function
expecting `y`. Apply with bare application (`add 1 2`) or with C-style
parentheses (`add(1, 2)`); both lower to curried application.

```yulang
my inc = add 1
inc 41                 // 42
```

## Calling forms

```yulang
add 1 2                // bare application
add(1, 2)              // C-style call
add: 1                 // colon application (rare for two-arg fns)
```

Bare application is the idiomatic form. Use C-style parentheses to group
visually or when bare application would chain too far across tokens.

## Lambdas

```yulang
\x -> x + 1
\x y -> x + y
```

Lambdas start with `\`. Multi-argument lambdas are written `\x y -> ...` and
are curried like binding heads.

A lambda's argument is itself a pattern:

```yulang
\(x, y) -> x + y
\{ name } -> "hello, " + name
```

## Type annotations

```yulang
my double(x: int): int = x + x
my mark(label: str, value: 'a): 'a = value
```

Annotations on parameters and the return type are optional. Inference fills
them in when omitted. Use annotations to document an API boundary, to pin a
generic that would otherwise stay open, or to resolve an ambiguous overload.

## Effectful annotations

```yulang
my ask(): [console] str = console::read()
my run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console (k "42")
```

The square-bracket form in the return type is the effect row. `[console] str`
means "this returns `str` while requiring the `console` effect". A row tail
variable such as `[console; e] 'a` keeps other effects open.

## Record patterns as optional arguments

```yulang
my area {width = 1, height = 2} = width * height

area { width: 3 }
area { width: 3, height: 4 }
area {}
```

A record pattern with defaults makes every field optional at the call site.
Defaults evaluate left-to-right and may reference earlier fields:

```yulang
my f {a = 1, b = a + 1} = (a, b)
```

## Methods via `with:`

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
    our p.scale n = point { x: p.x * n, y: p.y * n }
```

Inside a `with:` block, `our recv.name args = body` defines a method that
becomes `value.name args` for any `value` of the surrounding type. The
receiver `recv` is just a name — pick whatever reads naturally.

## Role methods

```yulang
role Add 'a:
    our a.add: 'a -> 'a

impl Add int:
    our x.add y = std::int::add x y
```

Role method headers use the same receiver-name shape as `with:` methods. The
type after `:` is the method's type after the receiver is applied — for
`Add`, that means `a.add` is a function taking the other operand.

## Where clauses

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

`where 'a: Role` adds a role constraint to the binding's type variable. The
binding's inferred type carries the constraint forward — calling `twice 1`
requires `Add int`.

`where` clauses also live in role and impl bodies. In a role body, the
constraint is inherited by every method. In an impl body, it becomes a
prerequisite for that impl candidate.

## Inference output

```bash
yulang check examples/showcase.yu
# or, when running from the repo
cargo run -q -p yulang -- check examples/showcase.yu
```

`check` prints the inferred public types. The output may show residual
type variables (`α`, `β`, …) and role constraints (`Add<α> => ...`); these
are expected for polymorphic bindings.

## See also

- [Patterns](./patterns) — the pattern grammar shared with `my`, lambdas, and
  arguments
- [Structs & Roles](./structs) — companion methods and role impls
- [Effects](./effects) — effect rows in argument and return positions
- [Cookbook](../guide/cookbook) — recipes that combine these pieces
