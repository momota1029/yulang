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

## Conditional adjacent-swap argument

The variable-only witness suggests a stronger statement for the extrusion
operation itself, under a deliberately closed-world condition. Fix one level
boundary `B` and one initial bound graph. Consider a finite sequence of
extrusion calls that each use a fresh private cache, and assume no constraints
or non-extrusion mutations arrive between calls. Each call receives a root
drawn from that graph. Source variables and their original structural bounds
are shared; each call's fresh representatives are disjoint and have level
`B`.

An earlier call can change a later call's source-bound snapshot only by
prepending its representatives to source lower/upper lists. Every such
representative is at level `B`, so the later `extrude` returns it immediately
without traversing it or creating new representatives. For each source `v`,
same-polarity representatives are inserted on the side the same-polarity
extrusion does **not** copy. Opposite-polarity representatives are inserted
on exactly the side the later opposite-polarity extrusion copies. Let `i+`
denote a call that extrudes `v` positively and `j-` one that extrudes it
negatively. Whichever call occurs second copies the earlier representative
into its own opposite bound. In either order this records the same subtype
relation:

```text
parent(v,-,j-) ≤ parent(v,+,i+)
```

The location differs (upper bound of the negative representative versus lower
bound of the positive representative), but both rows denote that same
inequality. This applies pointwise to every shared source identity and every
opposite-polarity pair. Same-polarity pairs produce no cross constraint in
either order. Since the inserted boundary representatives do not affect the
discovery of above-`B` nodes, the each-call traversal of original constructors
and bounds is unchanged; only these cross-polarity inequalities move between
equivalent bound rows. Thus adjacent call swaps preserve the conjunction of
all bound inequalities, and by adjacent transpositions so does any permutation
of the calls.

This is a conditional proof for assignment-fiber invariance of
independent Simple-sub extrusion calls. It predicts that raw graph
alpha-equivalence is too strong while the induced interval relation can be
order-independent. It depends on private per-call caches, globally fresh
representatives, one common boundary level, frozen original bounds, and no
intervening constraints. It does not cover two Yulang member preparations that
advance shared constraints, selected-edge evidence, polarity projection,
effects, level changes, or public scheme observations.

Independent compiler-referee review confirmed both transition traces and the
adjacent-swap argument within the stated assumptions: source-side links are the
only mutations to original variables; boundary-level parents stop recursive
discovery; and each opposite-polarity pair contributes the same inequality
regardless of call order. Raw edge sets differ, but the induced assignment
fibers agree. The reviewer found no semantic issue within scope. This does not
prove Yulang member-preparation/root-order or public scheme equivalence. No
tests were run.
