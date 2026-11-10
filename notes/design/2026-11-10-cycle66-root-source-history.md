# Cycle66: one root source table across actual recursive captures

Status: Draft (implementation boundary, not a language-semantics decision)
Date: 2026-11-10

## Goal and independent relation

Close the source-ownership subgoal for arbitrary finite histories of actual
`CommonRoleWhereSourceModels.run` returns, not just one parent's children.
`History slots root goal` starts at the root and takes an edge only when the real
candidate runner returns a result and the next goal is in its actual child list.
Each edge may use a different declaration, old demand state and local binder map.
The relation does not assume ownership, a model, child success or termination.

The fixed finite table is `parentTable root`. For every reachable goal, every
ambient name in both endpoints belongs to that table. For every further actual
capture, the endpoint names in its captured bindings and all generated children
also belong to the root table. Local binder numbers are retained separately from
ambient identities: compound bindings can have several ambient source owners.

## Executable boundary and intended quantified claims

`prepareAt table slots old declaration goal bindingSource` adds computed canonical
root owners to the existing real result. It looks up the concatenation of captured
binding endpoint occurrences and child endpoint occurrences, retaining order and
duplicates. Erasing the payload recovers all three original outcomes whenever the
current goal is included in the supplied table. `History` discharges this premise
for the root table, without a caller-supplied owner or source equality.

For all finite root/goal histories and all further calls, prove:
1. Original candidate outcomes are preserved, with no added lookup failure.
2. Every actual payload occurrence has its executable canonical owner in the
   original root table, even after arbitrary changes to intermediate local binders.
3. Across two independently reached goals/results, computed owners are equal iff
   their original ambient names are equal. Identical observed types do not merge
   names, and identical local binder numbers do not imply source identity.
4. Allocating any such payload into any root graph preserves the complete snapshot
   at its computed owner (including unknowns, K2 and capture payloads).

## Scope and remaining bridges

This proves root-table closure for the existing linear structural interval capture
fragment. It does not enumerate a finite set of goals or bound history length.
No Paterson termination, state-dependent regeneration, fresh existential identities,
associated feedback, graph adequacy or final dictionary classification is claimed.
The existing explicit `bindingSource` still controls demand grouping; endpoint
ownership does not synthesize that semantic map. All five main B4 bridges remain.

Before implementation: reread spec 6.3 (sibling updates before finalization), and
`work/dots-audit:notes/audit/x-oracle.md` X13–X16 and C3-PARENT/C3-PARENT-NEG.
Those executable examples do not certify this general source-history theorem.
No new Yulang2 execution or language decision is needed for this structural bridge.

## Executable finite traversal

`follow` also executes any finite list of declaration/binder-map/child-position
instructions, threading the real returned demand history. Its success implies
`History` and therefore discharges root allocation's domain premise. This utility
follows only positive candidate paths; a non-positive result or missing position
ends that traversal, without assigning a language-visible final classification.
It does not choose instructions, decide fairness or run a saturation scheduler.
