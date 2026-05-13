# Type Inference Theory

This page explains how Yulang's type inference treats effects and handlers.

It is not a full implementation note. It is meant to answer the questions a
reader of the reference is likely to have:

- How do effect rows relate to ordinary subtyping?
- Why can a handler remove an effect?
- Why does a handler inside a higher-order function not accidentally catch
  effects produced by another argument?
- Why is some of the evidence for that behavior hidden from hovers and the
  Types pane?

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

Yulang's inference engine does not only solve equalities. It builds subtyping
constraints.

```text
actual <: expected
```

If a position expects `int` and the actual expression is `int`, the constraint
is straightforward. If multiple shapes remain possible, inferred output may
show a union such as `α | int`.

Effect rows flow through the same constraint graph.

```text
[console] str <: [console; e] str
```

The concrete `console` effect can flow into an open row. The residual effects
left after a handler removes one effect also flow as ordinary rows in this
graph.

## Handlers Remove Effects From Rows

`catch` removes the effects handled by its operation arms from the inner
computation's row.

```yulang
act console:
    our read: () -> str

our run_console(action: [console; e] 'a): [e] 'a = catch action:
    console::read(), k -> run_console(k "42")
    v -> v
```

Informally, if `action` has effect row `[console; e]`, then outside the
`catch`, the `console` effect has been handled and only `[e]` remains.

That explanation is enough for direct code. Higher-order functions need one
more distinction: where an effect came from.

## The Hygiene Problem

Consider this function:

```yulang
my compose f g x = f(g x)
```

`g x` may perform effects. If `g` performs `last`, a `last` handler inside
`f` must not catch it accidentally.

The intuition is that `g`'s effects are supplied by the caller of `compose`.
A handler inside `f` should not silently absorb effects produced by a different
argument. If it did, higher-order functions would become unstable under
ordinary refactoring.

Yulang calls this property handler hygiene.

## Boundaries: What a Handler Can See

When a computation coming from a function argument or thunk is evaluated inside
a handler, Yulang places a boundary around it.

The boundary records which surface effects should remain visible to the current
handler.

| Annotation | Boundary meaning |
| --- | --- |
| no annotation | Show nothing. Effects from the argument are hidden from the inner handler. |
| `[_]` | Show effects that are already on the surface. |
| `[console]` | Show only surface `console`. |

The implementation calls this visibility choice `keep`.

The important point is that `[_]` does not erase the boundary. It means "keep
the effects that are already on the surface visible." It does not bring effects
that were already hidden back to the surface.

## Handler Matching Lives Beside Subtyping

The rule for removing effects with a handler is not encoded as ordinary row
subtyping.

The reason is that, when `actual` is still an unknown row variable, inference
must not guess that a handled effect exists on its surface.

```text
handler_match(ε, Surface, {console}, ρ)
```

Here `ε` is an unknown effect row. At this point, nothing proves that `console`
is present on its surface.

So inference must not invent this shape:

```text
ε = [console; rest]
ρ = [rest]
```

Instead, the solver records a hidden constraint beside the ordinary subtyping
graph:

```text
handler_match(actual, keep, handled, residual)
```

Read it as: remove from `actual` only the effects that are visible through
`keep` and are also listed in `handled`; the result is `residual`.

When the surface of `actual` later becomes concrete, the constraint can be
solved.

```text
actual   = [console, state]
keep     = Surface
handled  = {console}

residual = [state]
```

If `actual` remains unknown, the `handler_match` relation remains as hidden
evidence.

## Why It Is Hidden From Type Output

`handler_match` is not a type. Boundary markers such as `[; e]` are not public
type syntax either.

Public output shows ordinary value types and ordinary effect rows:

```text
α [console; e] -> [e] α
```

Hidden evidence answers a different question:

```text
When this computation enters a handler, which effects may that handler see?
```

That is not the same as "what value type does this expression have?" or "which
effect row escapes outward?" Therefore normal hovers and the Types pane do not
print `handler_match`.

If hidden evidence is solved from a concrete row, its residual result is still
reflected in the public type as an ordinary row.

```text
internal:
  handler_match([console, state], Surface, {console}, ρ)
  ρ = [state]

public:
  [state] α
```

What is hidden is the `handler_match` relation itself, not the ordinary row
that results from solving it.

## Same Public Type, Different Hidden Evidence

These two functions may have the same public type shape:

```yulang
my compose_plain f g x = f(g x)
my compose_surface f (g: _ -> [_] _) x = f(g x)
```

The public type can look like this for both:

```text
compose_plain   : (α [γ] -> [δ] β) -> (ε -> [γ] α) -> ε -> [δ] β
compose_surface : (α [γ] -> [δ] β) -> (ε -> [γ] α) -> ε -> [δ] β
```

The hidden evidence differs:

```text
compose_plain:
  effects from g are hidden from inner handlers

compose_surface:
  surface effects from g may be seen by inner handlers
```

The public type says where `g`'s effects flow. The hidden evidence says which
handlers along the way may catch those effects. Those are different questions,
so the public type alone does not always distinguish them.

## Runtime View

At runtime, Yulang does not rewrite every effect row when crossing a boundary.
It checks the boundary while searching for a handler.

Conceptually, when an effect is performed, the runtime searches outward:

```text
perform console
  -> if a boundary is crossed, decide whether this handler can see the effect
  -> only visible handlers are candidates
```

An effect from an unannotated argument is hidden from inner handlers. Once it
leaves the matching boundary, it becomes visible again as an ordinary effect.

This is why the public type system does not need to expose a row whose effect
indices have been shifted. Inference keeps a hidden constraint; runtime keeps
boundary evidence.

## Summary

Yulang's effect handler hygiene is split across these layers:

- Ordinary value types and effect rows are inferred in the normal subtyping
  graph.
- The question "which effects may this handler remove?" is represented by a
  hidden `handler_match` constraint beside that graph.
- Unknown rows are not opened just to satisfy a handler.
- `handler_match` is not printed in normal type output.
- Solved residual rows are printed as ordinary effect rows.
- Runtime handler search uses boundary evidence to choose which handler is
  allowed to catch an effect.

This keeps public types as ordinary row types while preserving effect hygiene
for higher-order functions.
