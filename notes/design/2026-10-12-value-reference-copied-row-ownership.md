# Value-reference ownership on copied rows

Status: Authoritative
Scope: Value-reference incidence inheritance for Simple-sub extrusion and per-use freshening
Approved-by: user
Approved-at: 2026-10-12
Drafted-by: primary, integrating approved question-board answer revision 2
Reviewed-by: independent architecture audit, 2026-10-12 (no blocking contradiction)
Supersedes: none; supplements the open copied-row scope of the parent-copy SCC design
Source: `questions/2026-10-12-value-reference-copy-content-owner/approved-answer.md`, revision 2

## Decision

Simple-sub extrusion and per-use freshening both copy type descriptions and
their applicable bounds without copying Value-reference incidences from the
source row. Recording an extrusion parent or allocating a fresh-use row does
not add a Value-reference edge.

A copied row may receive incidences from a separately defined source-owner
construction. Such a construction preserves the existing resolved binder as
the edge target. The original Apply-result and definition-root incidence rules
remain unchanged; a copy operation does not retarget their edges to a copied
type row. No target-copy correspondence is introduced merely because a type
description was copied.

The rule for SCC qualification remains the approved Value-reference graph.
A computational shortcut such as edge short-circuiting may be considered only
with evidence that it preserves SCC membership in that graph and, consequently,
the selected parent-qualified intrusion condition. Adopting a concrete shortcut
also requires a justification of its computational cost. No shortcut
algorithm, complexity bound, or implementation is selected here.

## Scope and proof boundary

The two operations share this incidence-inheritance rule; their Simple-sub
type maps, polarity behavior, levels, and fresh-use scopes remain distinct.
Only a concrete contradiction or a correctness-threatening counterexample
reopens the affected part of this rule. Missing proof or implementation
convenience alone does not change it.

This decision does not identify which source constructors assign incidences
to copied rows, prove that a particular retained parent/copy pair lies in the
same SCC, or prove equality preservation, soundness, required principality,
complete Call/effect hygiene, source completeness, implementation correctness,
or F5 replacement. It authorizes no compiler implementation or cutover. Those
obligations remain governed by the parent-copy SCC design and the top-level
inference principles.
