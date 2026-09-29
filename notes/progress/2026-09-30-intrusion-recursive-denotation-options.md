# SCC intrusion recursive denotation: decision boundary

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Reference: frozen Yulang2 Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Classification: architecture investigation; no semantic option selected

## Finding

The frozen Oracle exposes finite polarized type syntax and a directed
variable-bound worklist. Compaction records a recursive interval when a
`(variable, polarity)` visit is already active; ordinary instantiation
freshens the recursive identity and reinstalls lower and upper sides as
inequalities. It does not expose a recursive type constructor or an explicit
coinductive subtype-pair rule. Relevant source locations and prior probes are
listed in `intrusion-oracle-subtype-map.md` and
`intrusion-recursive-inequality-oracle-probe.md`.

This evidence rules out treating recursive interval records as recursive
equations by default. It does not select a mathematical solution carrier or
prove that no carrier can characterize the Oracle's accepted intervals.

## Candidate foundations

1. **Constraint graph with a denotational assignment carrier.** Keep recursive
   records as ordinary polarized inequalities between finite endpoints, and
   assign graph variables values in a separately defined subtype carrier.
   This preserves the Oracle's distinction between an inequality such as
   `q ≤ Arr(Int, q)` and an equation for `q`. The carrier still must explain
   intervals with matching recursive lower and upper Function bounds, empty
   fibers, `Bottom`/`Top`, unions/intersections, Function variance, and
   nominal constructors. Until those rules are fixed, soundness and
   principality cannot be proved.
2. **Guarded regular-tree carrier.** Interpret assignments as regular trees
   and use structural subtyping. This can represent solutions to some
   self-referential intervals, but it introduces a recursive comparison rule
   absent from the Oracle implementation map. It is viable only with a
   correspondence proof showing that it neither accepts nor rejects any
   supported Oracle observation; it must not silently convert an interval
   edge into an equality.
3. **Operational constraint semantics alone.** Define a relation directly
   from the Oracle worklist, saved views, instantiation, and continuations.
   This gives a concrete parity target for already selected views, but using
   Oracle acceptance itself as satisfaction would be circular and would not
   supply the independent soundness/principality theorem required by Gate C.

The architect's read-only analysis recommends first proving transport for an
already selected view: one injective fresh map for ordinary and recursive
identities, stable free anchors, and restoration of each recursive interval
as its two inequality sides. Projection congruence and ordered root-step
simulation can then be pursued independently of carrier choice. This is
useful progress, but it does not discharge Gate C.

## Decision boundary and status

The repository does not currently authorize a carrier or recursive subtype
rule. Selecting one changes the semantic basis of the replacement and needs a
reviewed successor contract before implementation. The options above are
research candidates, not an approval request embedded in the design. The
overall objective remains active; Gate C, the one-root simulation, full Oracle
equivalence, and implementation remain incomplete. No code, tests, Python, or
measurements were used for this investigation.
