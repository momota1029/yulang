# Structs & Roles

## Structs

```yulang
struct point { x: int, y: int }
```

Structs are nominal record types. Construct one with `point { x: 3, y: 4 }`.

## Type parameters

Structs can have type parameters:

```yulang
struct pair 'a 'b { fst: 'a, snd: 'b }
struct box 'a { value: 'a }
```

## Methods via `with:`

```yulang
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y
    our p.scale n = point { x: p.x * n, y: p.y * n }
```

`with:` attaches definitions to the struct's companion module. Methods use a
receiver name — here `p` — that stands for the value being called on. Receiver
style bindings are registered as methods; examples conventionally use `our`
when the method should be visible from outside the companion body.

The same `with:` machinery also works for `type` declarations, so standard
types such as `list`, `str`, and `ref` can define methods in their companion
modules.

## Roles

A role is an interface — a set of methods (and optionally associated types) that a type can implement. Roles are declared with the role name first, then the type variable they parameterize:

```yulang
role Add 'a:
    our a.add: 'a -> 'a

role Eq 'a:
    our a.eq: 'a -> bool
```

Each method header `our a.method: <type>` uses a receiver name (`a`) for the implementing type.

A role may also declare an associated type and span multiple type parameters:

```yulang
role Index 'container 'key:
    type value
    our container.index: 'key -> value
```

## `impl`

Implement a role for a concrete type:

```yulang
impl Add int:
    our x.add y = std::int::add x y

impl Index str int:
    type value = str
    our s.index i = std::text::str::index_raw s i
```

The first type after the role name fills the role's first type variable; further types fill the rest.

A struct can attach an `impl` inside its `with:` block. The enclosing struct is
prepended as the role's first type argument; any role arguments written after
the role name fill the remaining role inputs:

```yulang
struct box 'a { value: 'a } with:
    impl Index int:
        type value = 'a
        our b.index i = b.value
```

## Constraints with `where`

Constrain a function's type variables with a `where` clause inside the body:

```yulang
my twice(x: 'a) =
    where 'a: Add
    x.add x
```

`where` clauses also work inside `role` bodies and `impl` bodies. In a role
body, the constraint is inherited by the role methods. In an impl body, the
constraint becomes a prerequisite for that impl candidate.
