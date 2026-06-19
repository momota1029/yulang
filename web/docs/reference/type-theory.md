# Type Inference Theory

This page explains the current public model behind Yulang's type inference for
effects and handlers. It is not a full solver specification; the goal is to make
the types printed by the CLI, playground, and language server less mysterious.

The important shift is that handler hygiene is no longer described as a
separate hidden `handler_match` relation. The implementation represents the same
idea inside the subtype solver by carrying **stack weights** through type
inequalities.

## Expressions Have a Value Type and an Effect Row

Every Yulang expression has a value type and an effect row.

```text
e : A ! ρ
```

Read this as: expression `e` returns a value of type `A`, and may perform the
effects in row `ρ` while computing that value.

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

If a position expects `int` and the actual expression is `int`, the constraint is
straightforward. If multiple shapes remain possible, inferred output may show a
union such as `α | int`.

Effect rows are part of the same graph:

```text
[console] str <: [console; e] str
```

The concrete `console` effect can flow into an open row. Residual effects left
after a handler has consumed one effect also flow as ordinary rows.

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

## Stack-Weighted Rows

Internally, the solver can attach a stack weight to a type:

```text
stack(T, @S)
```

This does not mean the source language has a `stack` type constructor. It is an
internal way to remember which handler boundary is allowed to subtract which
effect family.

You can read a stack entry as a small budget:

```text
pop(n)[H1, H2, ...]
```

- a pushed set such as `[console]` says "this boundary may expose `console` to
  a handler";
- `pop(n)` moves the budget across function or thunk boundaries;
- a `floor` records effects that have already been consumed, so the solver does
  not rediscover and subtract them again later.

The order matters. A later `pop` can consume earlier pushed entries, but a push
that happens after an unmatched `pop` does not cancel that older pop. This is
why the solver keeps weights as ordered stack entries instead of treating them
as a plain set.

## Weighted Inequalities

The subtype solver compares types with weights on both sides:

```text
T @L <: @R U
```

When a `stack(T, @S)` wrapper is encountered, the wrapper is removed from the
type and moved into the weight:

```text
stack(T, @S) @L <: @R U
=> T @(@S + @L) <: @R U

T @L <: @R stack(U, @S)
=> T @L <: @(@S + @R) U
```

Ordinary variance still applies. Function arguments are contravariant, so the
left and right weights are swapped when the solver enters an argument position.
Function results are covariant, so the weights keep their direction.

For concrete terminal types such as `int` or `bool`, the weight has no observable
effect and can be dropped. For function types, records, tuples, effect rows, and
type arguments, the weight must keep flowing because a nested row may still be
subtracted later.

## How `catch` Subtracts an Effect

When `catch` handles a set of effects `H`, the solver asks whether the
scrutinee's row can be seen as:

```text
α @L <: @R [H; β]
```

If both weights are empty, this is just an ordinary row constraint. The solver
does not invent a subtraction budget.

If a weight is present, the solver computes the part that is actually visible:

```text
W = L + R
U = H ∩ common_stack(W)
```

- If `U` is empty, the handler is not allowed to consume anything from this row,
  so the residual row is left alone.
- If `U` is non-empty, the solver records that `α` may have `[U; γ]`, subtracts
  `U` from the weight, and sends the residual variable `γ` onward to `β`.

That residual variable is reused for the same subtraction slot. This prevents a
recursive handler from creating a fresh tail forever.

Effect families with type arguments are matched by family path, but their
arguments are not discarded. When `ref_update int` meets `ref_update α`, the
family match also generates ordinary type constraints that make the arguments
compatible.

## What Effect Annotations Mean

Effect annotations do two jobs: they describe the public row and they decide
which effects are visible across higher-order boundaries.

| Annotation | Internal visibility |
| --- | --- |
| no effect annotation | Do not give inner handlers a budget to consume caller-supplied effects. |
| `[_]` | Give a budget for the effects already visible on the surface row. |
| `[console]` | Give a budget only for `console`. |

The wildcard row `[_]` is an annotation placeholder. It is not the canonical
syntax of the row type itself, and it does not remove the boundary. It only says
that the currently visible surface effects may be exposed.

This is why two higher-order functions can print very similar public types while
still differing in what their inner handlers may catch.

## Public Types Do Not Print Stack Weights

Stack ids, floors, and pop counts are inference evidence, not source-level type
syntax. Normal hovers and the Types pane print ordinary value types and ordinary
effect rows.

```text
α [undet; β] -> [β] α
```

This means: the argument computation may perform `undet` plus some residual
effects `β`; after the handler consumes the visible `undet`, only `β` remains.
The residual `β` is a real part of the public type. It is not noise to erase.

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

This is why handler hygiene affects both type inference and VM lowering.

## Summary

Yulang's current effect inference works like this:

- ordinary value types and effect rows are inferred through subtyping;
- handler hygiene is represented by `stack(T, @S)` and weighted inequalities
  `T @L <: @R U`;
- `catch` subtracts only the effect families visible in the current stack
  weight;
- unknown rows are not opened just because a handler exists;
- residual row variables are part of the public type and should not be silently
  erased;
- stack weights themselves remain internal evidence;
- runtime guard markers preserve the same hygiene after specialization.

This keeps printed types relatively ordinary while still preventing inner
handlers from stealing effects that belong to a caller.
