# Nested carrier fixture: exact operational gap

Inspected `GeneralDictionaryNestedCarrierExample`,
`GeneralDictionaryNestedRefinementExamples`, `GeneralNominalProvenanceSource`,
`GeneralNominalSourceFormation`, and `GeneralNominalCycleSteps`.

## Existing facts, not missing facts

The eight-slot provenance source already has checked metadata and
`GeneralNominalProvenanceSource.initial_source`. Its existing root has three
point arguments `(0,0)`, `(3,3)`, `(6,6)`. Its seed is 7 and all present source
identities are at most 7. This is a valid initial source, not an unformed snapshot.
The separate regression query is `nominal 0 [nominal 0 [variables [7]]]` at
`(0,3)`. It is not one of that root's actual located argument intervals.

The nine-slot target preserves every old descriptor and source identity and
adds source identity 8 with an unresolved head and no nominal descriptor. Its
`Refines` certificate and direct report transport are proved. They do not imply
an operational refresh.

## Why the exact fixture is not an enabled refresh

`GeneralNominalCycleSteps.Refresh.support` requires every target source to
already occur among the old sources. Source 8 occurs in the target, but the old
source has no reserved/ordinary/allocated identities beyond 0 through 7.
Consequently this exact source/target pair cannot supply `support`.

An enabled `.refresh` action additionally requires a source that was not Known
and becomes Known. In this target, the new source 8 remains unresolved with no
descriptor; old descriptors are merely copied. Thus this target does not exhibit
the required new-Known witness either. Merely adding an unused slot is not an
enabled action in the operational relation.

`model_preserved` proves models of a displayed family, rather than the required
`Refresh.exact` statement for every old journal model. The target's lack of new
constraints should make the latter derivable, but it would not repair the two
failed action requirements above.

## Nonpoint query is not already a positive candidate

`positive_nonpoint` asserts source Models and Finished inspection only. It does
not assert ProjectionModels, private-state Models, or a candidate Instance.
Its displayed model uses bottom at source 2 and top at source 5. The repeated
capture name 7 ties the two nominal observation origins together in
`ProjectionModels`; those distinct values are not a witness for that condition.
A candidate fixture should instead use equal leaf values, for example both int,
and prove the complete projection/private/schema branch.

Changing the actual initial root argument to `(0,3)` also needs
`InitialSource.intervals`: every source model must satisfy the root interval.
The unmodified source permits independent leaf values in the two nominal arms,
so that all-model condition must not be inferred from one positive assignment.
An explicit source constraint/equality between the arms is a sensible setup.

## Minimal next operational construction

1. Define a checked declaration/role whose actual normalized query is the
   two-level repeated-capture query, with a real root located at `(0,3)`.
2. Supply initial source constraints sufficient for its root interval, and
   reprove Metadata, Linked, intervals, below_seed and unallocated. Existing
   provenance metadata is reusable only when the registry remains compatible.
3. Prove Prepared and a positive BranchModels witness with equal actual leaves;
   compute emitted requests and children rather than assuming them.
4. Prove source/Value PacketGuard, selected applicability, generated focus,
   Installable and novelty for actual installation. This creates a legitimate
   reserved output source.
5. Build a nine-slot target exposing that reserved output, with an actually
   Known head justified by the installed journal, rather than an unrelated
   unconstrained source 8. Preserve all source/row identities and descriptors.
6. Prove Refresh.exact for all old journal models, Refresh.support from the
   reserved-source membership, old-unknown/new-known witnesses, and the actual
   Value step. Then invoke the existing nested report/current-instance theorem.

This is new operational fixture work, not a missing cast in the existing
8-to-9 regression. No source definitions or operational rules were changed.
