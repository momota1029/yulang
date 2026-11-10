# Cycle96: finite actual materialization changes

Status: Draft implementation boundary, 2026-11-10.

## Scope and independent measure

The cycle95 ordinary detector is unchanged. For every fixed original Goal,
count variable occurrences in both endpoints of every argument. This measure is
computed from source syntax, not supplied as fuel, a rank certificate, or a
successful trace. A materialization changes only named variables into int, so
its count cannot increase, and unchanged count means literally unchanged Form.

For arbitrary before/after atom lists with membership inclusion and a model of
the later list, cycle95 fusion implies the later materialized Goal is obtained
by materializing the earlier one. Thus a changed Goal strictly decreases the
computed count. For every finite list of actual atom states satisfying these
explicit adjacent consistency/inclusion premises, the number of adjacent Goal
changes plus the last Goal's remaining count is at most the initial count.
The number of changes is therefore bounded independently of trace length.

The computation takes no model, supplied proof, source valuation, fuel, or
callback. Its theorem concerns arbitrary state lists, not a claimed solver run.
The later-model premise is essential because conflicting paired evidence can
make the existing detector undo int materialization by changing evidence order.

## Why this is a partial result

Spec 6.3 requires actual constraint-driven narrowing and saturation before final
classification. This supplies a concrete progress component for the int-only
fixed-template materializer. It does not bound ordinary changes invisible to that
materializer, repeated visits at the same Goal, generated templates, graph nodes,
or total execution time. A plateau does not imply later stability. No bounded
retry driver is introduced. Paterson descendant closure is already independent
of this state-refinement measure; joining them into a scheduler remains open.

Sources remains Goal-indexed and its lifetime boundary is unchanged. No original
Derives correspondence, source allocation, K2 classification, dictionary order,
or B4 completion follows. Yulang2 x-oracle X13-X16 reports local shared/nested interval approximations,
not arbitrary interval states or a general saturation trace. Existing audit
evidence is comparison material only; no new Yulang2 execution is claimed.

## Actual public-run connection

Equal materialized Goals give identical complete diagnostic Tree projections of
actual public graph runs, even if old demands differ. The old demands affect
ordinary graphs, not that tree. Under Extension, any changed Tree projection
strictly decreases the same source potential. Equal potential therefore forces
equal trees at the two compared states, but is not a promise about later states.
The theorem includes unfinished children, outside/rejected diagnostics, ordering
and multiplicity because it compares the entire existing Tree value. It does
not claim equality of graphs, model families or source observations over time.
