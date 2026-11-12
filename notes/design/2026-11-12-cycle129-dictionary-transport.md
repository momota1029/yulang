# Cycle129: dictionary order and typed source-slot transport

Status: Draft implementation plan, 2026-11-12. Scope: I-18 item5 only.

General B4 V3 still has 12 unfilled fields out of 12. The work below reduces
inputs for evidenceNode and the fixed-context order bridge; it does not fill a
whole field or implement the unassigned general Step.

1. Prove checked registry reordering preserves computed nominal bindings and
frames, including absent-key and failed-argument cases. Compose with raw
reconstruction/preparation order invariance. Keep Context/root/payload fixed.
2. Characterize typed finite source coverage independently of executable lookup,
and derive exact endpoint/output localization, retaining duplicate occurrences.
Nominal Linked alone remains insufficient because reserved/global/row IDs need
not be base type slots.
3. Supply a syntactic transport certificate between two already constructed
nominal snapshots. An explicit embedding preserves separate type and row maps;
ordinary atoms, recorded head equations, intervals, and nominal descriptors are
exact renamed images. Global atoms, seed and allocation ownership are unchanged.
Prove full nominal Models equivalence for every global assignment. This is a
checkable adapter contract, not a constructor of the target snapshot, an allocator,
a solver, or a source semantic decision. Fresh slots must have no invented head,
nominal descriptor or interval constraint. The target snapshot and row map remain
explicit inputs until the source-state owner supplies the actual extension.

For every model M, the target conclusion is Models after M iff Models before M.
No certificate field may itself mention Models or assume this equivalence.
Descriptor argument bounds must transport both type and row parameters, including
non-singleton bounds. Observation/knownness preservation is a separate obligation;
model equivalence must not be misreported as candidate or driver equivalence.

Source authority is spec/06-roles.md §6.3: where conjunction and output equalities,
with all existing readiness/freshness guards retained. Relevant Yulang2 audit
ROLE-MORE-001/002 confirms candidate-order behavior only in recorded examples;
ROLE-MORE-003 differs on advertised where clauses and is not imported here.
