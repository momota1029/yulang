# General dictionary recovery and registry comparison

Status: partial I-18 item 5, 2026-11-11. No language rule is selected here.
Astra owns items 1 and 2. This reduces representation prerequisites of
`evidenceNode`, `dictionaryRefl`, and `canonicalLocalOrder`; no general-source
`B4Bridges` field is closed. All 12 fields remain unfilled.

## Data and independent relations

The recovered `GeneralSourceDictionaries.Occurrence` retains a stable source ID
and the actual multiargument `GeneralSourceState.Demand roles`. Its ID is not a
list position. The finite dictionary retains selected declaration keys and every
child occurrence. Its least equivalence congruence allows sibling permutations
while preserving whole occurrences and keys; it is not a set of keys, and does
not identify every dictionary. Erasure loses source provenance, as the general
`erase_forgets_occurrence` regression demonstrates for every demand.

`Evidence localRule` is a reusable induction carrier, explicitly conditional on
a still-missing declaration-instance judgment. `Linked` is a concrete snapshot
property of all endpoint and output source IDs. Neither property proves role
satisfaction. The all-model instance-equation component quantifies each shared
assignment and retains every repeated output equality. Its terms are ordinary
`TyTerm Nat`; producing them from the actual declaration/capture remains open.
It does not interpret the catalogue of generic pattern constructors by fiat.

`GeneralRegistryReordering.Reorders` uses the actual new `Registry`: constructors
and role signatures are identical; visible declarations are permuted, then each
corresponding declaration retains id, role, head, associated equations and output
binders, while its complete where list is permuted. Clause IDs, output equations,
and multiplicities survive. `reorders_checked` transports every declaration
certificate, including the universal capture-stability premise. This is not yet
candidate or resolver order independence.

## Boundaries and next work

1. Instantiate actual declaration heads and outputs into ordinary source terms,
   respecting separate type and row IDs and nominal constructor interpretation.
2. Connect visible declarations and exact child-emission identities to the local
   evidence relation; prove all-model evidence from the selected candidate state.
3. Establish source-indexed readback/canonicalization into the key-only B4 payload.
   Erasure alone cannot reconstruct the source obligation identities.

No new semantic question is introduced by the order relation. The previous
boundary-input questions about source allocation remain in force; arbitrary IDs
in this carrier are not presented as an allocator or derived source identities.

## Yulang2 comparison

Read `notes/audit/y2-claims-role-boundaries-cycle-2.md`, ROLE-MORE-003/004.
It distinguishes old advertised where clauses from real body dependencies.
The current spec 6.3 requires every where child; old behavior is not imported.
Spec 6.2 retains call-site visible implementation identity; spec 6.3 makes
sibling where requirements a conjunction. No new Yulang2 runtime was run.

## Second and third subgoals

`GeneralRegistryChildOrder` proves the general reorder equivalence laws and the
permutation of actual `emitAll` results, with each clause-indexed allocation held
fixed. Complete Emission structures, not only implementation keys, are compared.

The next dictionary equation bridge takes a shared State and an actual Demand.
A located equation package stores local slots for both argument endpoints and
each output occurrence, plus local ordinary head/RHS terms. Its explicit source
identity equations tie those slots to the Demand. Ordinary substitution maps
local type variables with `state.source` and local row variables with
`state.rowSource`; a single common renaming would be wrong. If the four families
of generated inequality atoms occur in the actual state's ordinary list, the
bridge proves the corresponding global equations in every model of that state.
This still does not derive the equations from declaration patterns or prove
candidate selection. It is an independent concrete prerequisite of evidenceNode.

The shared-state bridge is now proved: `recorded_holds` and `recorded_entails`
derive all-model meaning from actual stored local inequalities, with separate
source/type and source/row identities. Source-preserving refinements preserve
these fixed global equations. A satisfiable fixture retains two output
occurrences (six atoms total) and distinct type/row source IDs 10 and 20.

The remaining order adapter is a real boundary, not notation:
`swapped_child_order_not_equal` proves that two distinct clause IDs give unequal
raw emitted lists after swapping, although `emitAll_permute_requirements` proves
permutation. Thus raw emitAll cannot itself supply the skeleton's literal
`canonicalLocalOrder`; source-obligation canonicalization must be implemented.
No new owner semantics is required to record this obstruction.

## Fourth subgoal: canonical source clause order

Canonicalize a declaration's where list by its retained clause IDs, which Checked
already requires to be unique. This is an internal ordering of the existing
source obligations, not a new allocator or language priority. Preserve the
original declaration and prove the canonical view has the same independent
checks. Reordered declarations should have exactly equal canonical views, hence
exactly equal complete emitted children under the same clause-indexed capture
and allocation. This addresses the raw-order obstruction locally; candidate
judgments, state updates and the B4 adapter still remain.

The fourth subgoal is now proved in `GeneralCanonicalChildOrder`:
`canonicalEmit_reorders` gives exact equality of the entire emitted list for any
two checked reordered declarations with the same capture/allocation. The proof
uses uniqueness of actual clause IDs, not equality of role keys.
`canonicalEmit_perm` preserves every original child and its complete output data.
The raw-order obstruction is addressed at emission only; no claim is made that
different final resolver states or survivor selections already correspond.
