# Cycle97: change-triggered diagnostic replay

Status: Draft implementation boundary, 2026-11-10.

## Objective and data

Build an executable replay of complete diagnostic trees over ordinary-state
updates. Rebuild only when the materialized original Goal changes. Keep one
snapshot per input state, including plateaus, while reusing the previous tree.
Return actual rebuild and diagnostic-node-visit counts. The declaration checker
is run by the public entry; no fuel, finite work domain, model, rank or successful
child is supplied to computation.

## Independent target

For every registry, fixed slots and Sources, fixed original Goal, initial atoms
and finite update list, successful replay returns exactly the same ordered list
of full trees as direct public frontier runs at each state. This includes every
unsupported, rejected and unfinished descendant, all branch order and duplicates.
This correctness has no consistency or monotonicity premise. Only trees are
cached: ordinary graphs and old demands must still be recomputed independently.

Under the cycle96 Chain premise (each actual atom list includes the previous
list and has a model), rebuilds are at most one plus the original variable
occurrence potential. Every rebuilt tree's full preorder list has length at
most the cycle95 computed domain length: each actual closure is a list block
inside the concatenation over all syntax variants. This is stronger than set
inclusion, which alone would not bound repeated occurrences. Total diagnostic
node visits are bounded by the product of these two source-derived bounds,
independently of the supplied update-list length.

## Boundaries and source basis

The finite input list is supplied; replay neither calls the ordinary solver nor
proves that an actual solver produces a Chain or finishes its updates. Every
update still incurs materialization, comparison and output-list cost. This is
not a runtime bound, graph-size bound, fair scheduler or saturation stop test.
A plateau can be followed by another change and is always processed.

The materializer is the existing explicit paired-int implementation fragment,
not general entailment or a language restriction on other types. Sources and
slots retain the unresolved source/invocation derivation boundary. Spec 6.3 is
the basis for constraint-driven narrowing; no unique-impl narrowing is used.
The audit branch X13-X16 observations are local examples and do not establish
this replay theorem. No new semantic policy is chosen. All five B4 bridges
remain incomplete.

## Exact graph refresh adapter

`runGraphs` follows cached replay with one fresh ordinary graph compilation per
state and independently indexed old-demand list. Its checked zipper rejects mismatched lengths instead
of truncating; the public replay establishes the exact length and never reaches
that mismatch. For every successful replay and arbitrary occurrence-indexed old
source demands, the resulting full outputs equal direct public materialized
runs at every original state. This is stronger than equality of tree projections
and prevents row or type constraints from being lost on diagnostic plateaus.
It still does not solve those graphs, claim model existence, derive a trace or
bound graph compilation work. `visits` is an explicit accounting metric for
rebuilt-tree preorder occurrences, not every operation or internal traversal.
