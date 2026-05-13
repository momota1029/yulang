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
{ ..base, x: 3 }
{ x: 3, ..rest }
```

Anonymous products with named fields. Field access uses `.field`.

Record patterns can make fields optional with defaults:

```yulang
my width_or_default { width = 1 } = width
my keep_rest { ..rest, width = 1 } = rest
```

The type printer marks optional record fields with `?`, for example
`{width?: α} -> α | int`. A spread pattern that keeps the rest may render an
intersection such as `α & {width?: ⊤}`.

## Optional

```yulang
just 42
nil
```

`opt 'a` is the standard library type `enum opt 'a = nil | just 'a`.
The prelude reexports both the type and its variants, so ordinary code writes
`opt`, `just`, and `nil` without `std::opt::` or `opt::` qualification.

## Result

```yulang
ok 1
err "bad"
```

`result 'ok 'err` is the standard library type for fallible computations.
The prelude reexports `result`, `ok`, and `err`; qualify them only when a local
name would be ambiguous.

## Ranges

```yulang
0..<10  // 0 to 9 (exclusive)
0..10   // 0 to 10 (inclusive)
0..     // 0 upward (unbounded)
```

`..`, `..<`, `<..`, `<..<` are range operators in `std::range`. Ranges implement `Fold`, so they work with `for x in r:` and the nondeterminism `each` collector.

## Type variables

Type variables use the `'a` prefix. They appear directly inside type
annotations; there is no separate type-parameter binder on ordinary function
bindings.

```yulang
my id(x: 'a): 'a = x
```

Type inference fills in type variables automatically in most cases — annotations are only needed for clarity or for resolving ambiguity.

## Function and computation types

```yulang
int -> int
() -> [console] str
[console] str
```

`A -> B` is a function type. If the result may perform effects, the result side
can carry an effect row:

```yulang
() -> [console] str
```

`[console] str` by itself is an effectful computation value: it may perform the
`console` effect and returns a `str`. This form is useful for
handlers and control abstractions:

```yulang
our run_console(action: [console] 'a): 'a = catch action:
    console::read(), k -> run_console(k "42")
```

The type printer may also show an effect row on a function argument, e.g.
`α [io; β] -> [β] α`. That means the argument is an effectful computation.
Source annotations usually write that argument type with a concrete value type
or a type variable, such as `[io; e] 'a`.

`_` can appear in annotations as a placeholder to ask inference to fill a type
hole. It is not a type constructor and should not be read as part of the
underlying type syntax.

## Effect rows

Effect rows appear in type signatures with `[...]`:

```yulang
[console; e] str
() -> [console; e] str
```

A row lists the named effects, optionally followed by a row variable such as
`; e` to indicate "any other effects." A wildcard row such as `[_]` is an
annotation placeholder for inference; it is not the canonical form of an effect
row type.

## Role constraints

Constraints are introduced with `where`:

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

The same form works inside a `role`/`impl` body and inside a binding body. `where` clauses constrain a type variable to implement one or more roles.

## Inferred unions and intersections

Yulang's inferred types may contain unions and intersections even though there
is not yet a stable source annotation syntax for writing them directly.

```text
α | int
α & {width?: ⊤}
```

You will usually see these in the Types pane when a branch, default value, or
pattern spread leaves more than one possible shape. Adding an annotation can
often collapse the displayed type to the intended public shape.

## See also

- [Effects](./effects) — declaring, calling, and handling effects.
- [Type Inference Theory](./type-theory) — subtyping, effect rows, and handler hygiene.
