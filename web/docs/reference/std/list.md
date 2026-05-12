# `std::list`

Immutable lists, with `Index`, `Fold`, and `+` (concatenation) support.

## Construction

```yulang
[]
[1, 2, 3]
[head, ..tail]

std::list::empty()              // []
std::list::singleton 1          // [1]
std::list::cons(0, [1, 2])      // [0, 1, 2]
```

The `[ ... ]` literal is the everyday form. `cons` and `singleton` are useful
when working with type variables that would otherwise lose information.

## Indexing and slicing

```yulang
my xs = [10, 20, 30, 40]

xs[0]            // 10
xs[xs.len - 1]   // 40
xs[1..<3]        // [20, 30]
xs[..2]          // [10, 20]
xs[1..]          // [20, 30, 40]
```

`list 'a` implements `Index` for both `int` and `range`. An out-of-range index
fails at runtime; a range slice that runs off the end is clamped.

## Predicates and length

```yulang
xs.len              // 4
std::list::is_empty xs    // false
```

`Len` is exposed through `xs.len`.

## Iteration

```yulang
for x in xs:
    println x.show

xs.fold 0 (\acc x -> acc + x)
```

`list 'a` implements `Fold`, so `for` and `fold` both work. The body of a
`for` loop is a function applied to each element.

## Transformations

```yulang
xs.map double                          // [20, 40, 60, 80]
xs.filter (\x -> x > 15)               // [20, 30, 40]
xs.rev                                 // [40, 30, 20, 10]
xs.sort                                // [10, 20, 30, 40]
xs.append [50, 60]                     // [10, 20, 30, 40, 50, 60]
xs + [50, 60]                          // same — list implements Add
```

`map`, `filter`, `rev`, `sort`, and `append` return new lists; the original
is untouched.

## Head/tail access

```yulang
xs.first    // opt::just 10
xs.last     // opt::just 40

case std::list::uncons xs:
    opt::just (head, tail) -> head
    opt::nil               -> default
```

`first`, `last`, and `uncons` return `opt` so they handle empty lists
cleanly.

## Mutable list references

```yulang
my $xs = [1, 2, 3]
&xs[1] = 99
$xs                  // [1, 99, 3]

&xs.push 4           // [1, 99, 3, 4]  (through Index ref impl)
```

When `xs` is held in a reference (`my $xs = ...`), the `Index` impl for
`ref _ (list _)` lets you write `&xs[i] = value`. Lists pushed through
`&xs.push v` go through the matching ref method.

## Nondeterminism

```yulang
use std::undet::*

(each xs).list
(each xs).once
```

`each` picks one element nondeterministically. `.list` collects every choice
into a fresh list, `.once` returns the first as `opt`.

## Quick reference

| Operation | Signature |
|---|---|
| `empty()` | `() -> list 'a` |
| `singleton(x)` | `'a -> list 'a` |
| `cons(x, xs)` | `'a -> list 'a -> list 'a` |
| `is_empty(xs)` | `list 'a -> bool` |
| `xs.len` | `list 'a -> int` |
| `xs.map f` | `list 'a -> ('a -> 'b) -> list 'b` |
| `xs.filter p` | `list 'a -> ('a -> bool) -> list 'a` |
| `xs.fold z f` | `list 'a -> 'b -> ('b -> 'a -> 'b) -> 'b` |
| `xs.rev` | `list 'a -> list 'a` |
| `xs.append ys` | `list 'a -> list 'a -> list 'a` |
| `xs.sort` | `list 'a -> list 'a` (requires `Ord 'a`) |
| `xs.first` / `xs.last` | `list 'a -> opt 'a` |
| `uncons(xs)` | `list 'a -> opt ('a, list 'a)` |

## See also

- [Patterns → List patterns](../patterns)
- [`std::range`](./core) — ranges for slicing and iteration
- [`std::undet`](./undet) — nondeterministic iteration
