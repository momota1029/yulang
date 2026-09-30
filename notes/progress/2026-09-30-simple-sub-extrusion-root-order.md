# Simple-sub extrusion root-order probe

Date: 2026-09-30
Status: hand-derived finite characterization; general order theorem open
Scope: interaction of opposite-polarity extrusion calls on one shared variable
Source: `mlsub-compare` `Typer.scala::extrude`, audited commit `9bae772624c23b52a93c1b226157e16898b4d9db`

## Setup

Use an above-boundary variable `v` with `L(v)=[Int]`, `U(v)=[]`. Invoke
positive and negative extrusion separately, so each call has the reference
implementation's own empty `(Variable, polarity)` cache. Let their fresh
representatives be `a` and `b`.

### Positive, then negative

The positive call installs `a` in `U(v)` and copies `L(v)` to `L(a)`. The
negative call then installs `b` in `L(v)` and copies the now-current `U(v)` to
`U(b)`:

```text
L(v) = [b, Int]     U(v) = [a]
L(a) = [Int]        U(a) = []
L(b) = []           U(b) = [a]
```

### Negative, then positive

The negative call first installs `b` in `L(v)` and copies empty `U(v)` to
`U(b)`. The positive call then installs `a` in `U(v)` and copies the now-
current `L(v)` to `L(a)`:

```text
L(v) = [b, Int]     U(v) = [a]
L(a) = [b, Int]     U(a) = []
L(b) = []           U(b) = []
```

The raw bound graphs are not alpha-equivalent: one stores the cross-polarity
constraint `b ≤ a` in `U(b)`, the other stores it in `L(a)`. But under the
ordinary interval reading, both graphs induce the same conjunction of
inequalities:

```text
Int ≤ v, b ≤ v, v ≤ a, Int ≤ a, b ≤ a
```

Thus this example disproves raw graph alpha-equivalence as the right
root-order criterion, while supporting equality of satisfying-assignment
fibers for this variable-only case. It also shows why source-side writes cannot
be ignored: the second call observes the first call's link and transfers the
same cross-polarity inequality to its own representative's opposite bound.

## Exact limit

This is one two-call variable-only case, not a general commutation theorem. It
does not cover structural bounds whose recursive extrusion mutates other
vertices, repeated visits with mixed Function polarity, duplicate bound
occurrences/order, recursive closures, level anchors, mutation-triggered
constraint propagation, or root projection. The next proof should define
root-order equivalence as equality of the relevant scheme/assignment relation,
then prove each adjacent swap of independent root transitions preserves that
relation under explicit side conditions. If the side conditions fail for a
structural counterexample, the Oracle root order must remain part of the
semantics.

Independent compiler-referee review confirmed both transition traces and the
equality of their induced assignment fibers. It found no semantic issue; it
noted only that the inequality conjunction is equivalent even though the raw
edge sets differ, now stated explicitly above. Review scope: these two calls
and this conclusion only; no broader commutation claim was reviewed and no
tests were run.
