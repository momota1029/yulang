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

## Closed composition at the second checkpoint

The fixed-frame source compiler now transports successful variable localization,
head and RHS construction, checked plans, complete finite recipes and raw payload
preparation through the syntactic certificate. The returned local packages are
exactly renamed, while the entire source-indexed dictionary is unchanged. Old
failure is deliberately not preserved: newly available IDs can make it succeed.

The whole prepared item list is exactly the mapped old list, including duplicate
items and output requests. Recording that mapped list gives the same full nominal
Models at every assignment. One unchanged readback witness has actual declaration
Evidence in every target transaction model; both original and target full snapshot
Models are retained. No context-changing candidate-frame equality is asserted.

Two strict supplied extensions exercise 1-to-2 and 2-to-3 slots. The latter keeps
an actual nominal descriptor with both type and row parameters; type77 and row43
stay distinct and a concrete full nominal assignment satisfies both states.
A repeated nonempty dictionary batch and a separately evaluated arrow term check
multiplicity and the separate type/row maps. Independent arbitrary nominal source
Instance/Evidence also transports under registry order, with computed frames at
one fixed Context and the same existing binder-value witnesses.

## Final boundary checks and actual new-source use

The complete raw executor is exercised both on an old source ID retained through
the mixed extension and on newly represented reserved type ID88. In the latter
case the old preparation is none and the new one returns a real tree with two
explicit outputs, full nominal joint model and independent source Evidence. The
new source remains RootPending. This is useful dictionary materialization, not
successful candidate inspection or Survivor construction.

Freshness requires an additional CoordinatesBound premise: each new type or row
source must be either an old mixed source or no larger than the old allocation
seed. Under that premise, generated membership, source allocation and Fresh are
preserved with the original owner map. The mixed fixture satisfies the premise
using reserved88 and row44 below seed77. It does not authorize arbitrary IDs.

An identity-coordinate fixture changes only the normalized view. It has a real
full nominal model before and after, and satisfies Transport, while Known and
RootPending differ. Thus view/readiness equivalence cannot be derived from the
model-preservation certificate alone. The state owner must add an observational
contract or produce an actual source-state construction before that next bridge.

## Next dictionary-owned bridge: locality of supplied Frames (not proved here)

`Frame` contains `capture`, `allocation` and `identity`, so equality of captures
alone cannot justify equal canonical child occurrences. A useful next contract
should record agreement only at nodes of one reconstructed finite dictionary:
for every node occurrence/root and selected checked declaration, require the same
capture at its key, the same complete canonical emitted child occurrence list,
and recursively the same agreement at those children. No premise should mention
raw preparation success or source Evidence. A first implementation may compare
all three frame fields at each visited root; then narrow that sufficient contract
to the used declaration and clause positions without dropping output requests.

Proposed lemma chain (all new work, not counted among the125 theorems):
1. `reconstruct_frame_local`: for every checked registry, frames F/G, payload P,
   root R and source tree D, if reconstruct F P R = some D and recursive frame
   agreement holds on D, then reconstruct G P R = some D.
2. `prepare_frame_local`: for every fixed source snapshot and the same data,
   old raw preparation = some T plus frame agreement on T.dictionary implies
   new raw preparation = some T. Reuse computed endpoint localization unchanged;
   transport each head/RHS lookup through capture agreement at the selected key.
3. `prepare_transport_frame_local`: compose (2) with the present syntactic
   Transport, yielding the exact reindexed tree with an unchanged source
   dictionary under F/G rather than requiring global Frames equality.

These are dictionary-local congruence goals. Deriving the recursive frame
agreement from two actual candidate contexts, normalizing views, constructing a
target snapshot or proving driver-order invariance remain separate obligations
owned by their respective source/candidate work. The concrete view counterexample
rules out obtaining that agreement from model equivalence alone.
