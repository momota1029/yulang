# Yulang

```yulang
if all [1, 2, 3] < any [4, 5, 6]:
    "found a pair"
else:
    "nothing"
```

That `if` compares every element of one list against every element of another.
There is no loop, no comprehension, no helper — `all` and `any` are first-class
values, and the comparison lifts over them. The same machinery powers
nondeterministic search:

```yulang
{
    my candidate = each [(1, 2, 3), (3, 4, 5), (5, 12, 13)]
    case candidate:
        (a, b, c) -> {
            guard: a * a + b * b == c * c
            candidate
        }
} .once
```

`each` chooses a candidate; `guard` prunes invalid tuples; `.once` runs the
search and returns the first Pythagorean triple. The code reads top to bottom
like an imperative script, but underneath it is branching and backtracking.

Yulang is built on this principle: **control flow is library code.**
Mutation, nondeterminism, lifted comparison, early return, typed errors,
custom backtracking — none of them are parser builtins. They are all ordinary
functions sitting on top of an algebraic-effect machinery you can extend
yourself. Surface code stays short and straight-line; the shape underneath
can be anything you want.

## In the box

- **Algebraic effects with handlers.** `act` declares an operation, `catch op,
  k -> ...` handles it. The handler receives the captured continuation `k`,
  so resuming, retrying, and aborting are all just choices of what to do with
  `k`.
- **Roles instead of typeclasses.** `role Add 'a:` declares an interface,
  `impl Add int:` provides it. Methods read as ordinary dot calls.
- **Mutation that stays pure.** `my $x = 0`, read with `$x`, write with
  `&x = v`. Compiles down to a handled `var` effect — the semantics stays
  pure, the syntax stays familiar.
- **Patterns everywhere bindings live.** `my (a, b) = pair`. Optional named
  arguments fall out of record patterns: `my area {width = 1, height = 2} =
  width * height`.
- **A parens-light surface.** Bare application `f x y`, colon application
  `f: ...`, layout blocks driven by `:` and indentation.

::: tip Playground
Every example on this page runs in the <a href="/" target="_self">Playground</a>.
:::

## Where to go next

- [Tour](./tour) — a guided walkthrough of the language
- [Cookbook](./cookbook) — task-oriented recipes
- [Reference](/reference/) — syntax and feature details
