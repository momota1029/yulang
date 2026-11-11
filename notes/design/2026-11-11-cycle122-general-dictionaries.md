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
