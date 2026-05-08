# std::undet

The `undet` module provides nondeterminism through the `undet` algebraic effect.

```yulang
use std::undet::*
```

## The effect

```yulang
act undet:
    pub branch: () -> bool
    pub reject: () -> never
```

`branch` makes a binary choice; `reject` prunes the current branch. Higher-level helpers below are built on top of these.

## `each`

```yulang
each [1, 2, 3]   // chooses one value nondeterministically
each 1..         // chooses from an infinite range
```

`each xs` returns one element of `xs`, signalling its choice through the `undet` effect. `xs` can be any value implementing `Fold` (lists, ranges, …).

## `guard`

```yulang
guard: condition
guard (a == b)
```

When the condition is false, `guard` calls `reject` and prunes the current branch.

## Collectors

Collectors are written as method calls on a nondeterministic expression:

| Method | Result type | Description |
|--------|-------------|-------------|
| `.list` | `list 'a` | All results, in branch order |
| `.logic` | `list 'a` | All results with breadth-first scheduling (suitable for infinite branches) |
| `.once` | `opt 'a` | First result if any, otherwise `nil` |

Each collector handles `branch` and `reject`, removing the `undet` effect from the type.

## Example: Pythagorean triples

```yulang
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once
```

The same program can be written with independent infinite choices and `guard: a <= b` / `guard: b <= c`, but the bounded form above is friendlier to the current VM and to browser Wasm stacks.

## Junctions

The companion module `std::junction` exposes `all xs` and `any xs`. They are not part of `undet`, but they share the same theme — they wrap a collection so a single comparison covers every element via the `junction` effect:

```yulang
if all [1, 2, 3] < any [2, 3, 4]:
    1
else:
    0
```

`all`/`any` are reachable through the prelude.
