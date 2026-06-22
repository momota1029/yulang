# Type Inference Theory

This page explains the public model behind Yulang's type inference for effects
and handlers. It is not a full solver specification; the goal is to make the
types printed by the CLI, playground, and language server easier to read.

The current implementation represents handler hygiene inside the subtype solver
with **directed stack weights**. A handler can subtract only the effect families
that are visible through those weights.

## Expressions Have a Value Type and an Effect Row

Every Yulang expression has a value type and an effect row.

```text
e : A ! rho
```

Read this as: expression `e` returns a value of type `A`, and may perform the
effects in row `rho` while computing that value.

In surface type output, Yulang writes the two pieces together:

```text
[console] str
```

This is a computation value that may perform `console` and returns a `str`.

Function types put the effect row on the result side:

```text
() -> [console] str
```

This is a function that takes unit and, when called, may perform `console`
before returning a `str`.

## Ordinary Subtyping

Yulang's inference engine solves subtyping constraints, not just equalities.

```text
actual <: expected
```

Effect rows flow through the same graph:

```text
[console] str <: [console; e] str
```

The concrete `console` effect can flow into an open row. Residual effects left
after a handler consumes one effect also flow as ordinary rows.

## Why Plain Row Subtraction Is Not Enough

For direct code, it is tempting to say that `catch` simply subtracts an effect
from the inner row:

```yulang
act console:
    our read: () -> str

our run_console(action: [console; e] 'a): [e] 'a = catch action:
    console::read(), k -> run_console(k "42")
    v -> v
```

Informally, if `action` has row `[console; e]`, then outside the `catch` only
`[e]` remains.

Higher-order functions need one more distinction: where an effect came from.

```yulang
my compose f g x = f(g x)
```

If `g x` performs `last`, a `last` handler hidden inside `f` must not catch it
accidentally. The effect was supplied by the caller of `compose`, not by `f`.
Yulang calls this property **handler hygiene**.

## Directed Stack Weights

Internally, the solver can attach a stack wrapper to a type:

```text
stack(T, S)
```

This does not mean the source language has a `stack` type constructor. It is an
internal way to remember which handler boundary is allowed to subtract which
effect family.

Subtype constraints carry two directed weights:

```text
T @L <: @R U
```

- the left weight `L` can carry active `take(H)` entries;
- the right weight `R` carries only pure pops;
- `take(H); pop` cancels, but `pop; take(H)` does not;
- function arguments swap the two directions because they are contravariant.

This direction matters. The solver must not merge the left and right weights
before deciding which row head a handler may consume.

## How `catch` Subtracts an Effect

When `catch` handles a set of effects `H`, the solver may see a row constraint
like this:

```text
alpha @L <: @R [H; beta]
```

The row head that can actually be consumed is:

```text
J = H ∩ Common(L)
```

`Common(L)` is the intersection of the active `take(...)` families in the left
weight. Right-side pops do not make an effect visible to the handler. Filters
and legacy compatibility markers do not count as active pushes either.

If `J` is empty, the handler cannot consume anything from that row. The solver
does not invent a residual just because a handler exists.

If `J` is non-empty, the solver splits the row:

```text
alpha <: [J; gamma]
gamma @(L - J) <: NWeight(R, beta)
```

`NWeight(R, beta)` is an internal wrapper saying that the right-side pop
evidence stays on the residual tail. It is not used to expose the row head.

The same subtraction slot reuses the same residual variable `gamma`, so
recursive handlers do not create fresh tails forever.

Effect families with type arguments are matched by family path, but their
arguments are not discarded. When `ref_update int` meets `ref_update alpha`, the
family match also generates ordinary type constraints that make the arguments
compatible.

## What Effect Annotations Mean

Effect annotations do two jobs: they describe the public row and they decide
which effects are visible across higher-order boundaries.

| Annotation slot | Internal meaning |
| --- | --- |
| omitted or `[_]` in a contravariant slot | Expose the currently visible surface effects, as `take(All)`. |
| `[console]` in a contravariant slot | Expose only `console` to an inner handler. |
| omitted or `[_]` in a covariant slot | Leave the row open without adding a filter. |
| `[console]` in a covariant slot | Check that only `console` escapes. |

The wildcard row `[_]` is an annotation placeholder. It is not the canonical
syntax of the row type itself, and it does not erase a boundary.

Covariant concrete annotations are **filters**. A filter is a static check, not
a runtime marker and not a residual row. Once the check has been recorded, it is
erased from the stored solver weight.

Fresh internal residuals that must not be consumed are protected by an empty
visibility budget, conceptually `take(Empty)`. There is no separate "protected
variable set" in the inference core.

## Public Types Do Not Print Stack Weights

Stack ids and pop counts are inference evidence, not source-level type syntax.
Normal hovers and the Types pane print ordinary value types and ordinary effect
rows.

```text
alpha [undet; beta] -> [beta] alpha
```

This means: the argument computation may perform `undet` plus some residual
effects `beta`; after the handler consumes the visible `undet`, only `beta`
remains. The residual `beta` is a real part of the public type. It is not noise
to erase.

What stays hidden is the weighted evidence explaining why the handler was
allowed to consume `undet` at that boundary.

## Runtime View

After specialization, the runtime cannot recover hygiene by guessing from a row
string. Function values, thunks, and structural values may cross boundaries
before they are executed.

The runtime therefore carries guard markers with values. Conceptually, those
markers are the execution counterpart of the inference weights:

- inference decides which handler boundary may consume which effect family;
- runtime markers make handler search respect the same boundary when the effect
  is eventually performed.

Filters do not become runtime markers. They are checked statically by the
solver.

## Summary

Yulang's current effect inference works like this:

- ordinary value types and effect rows are inferred through subtyping;
- handler hygiene is represented by directed weighted inequalities `T @L <: @R U`;
- `catch` subtracts only `H ∩ Common(L)` from a row head;
- right-side pops are carried to the residual tail, not used to expose the head;
- unknown rows are not opened just because a handler exists;
- residual row variables are part of the public type and should not be silently
  erased;
- runtime guard markers preserve the same hygiene after specialization.

This keeps printed types relatively ordinary while still preventing inner
handlers from stealing effects that belong to a caller.
