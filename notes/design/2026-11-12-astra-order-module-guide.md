# General registry order: module guide

Item 5a, based on integration `55fd40388`. The detailed result and complete
public theorem signatures are in
[Item 5a of the boundary note](2026-11-11-astra-general-boundary.md#item-5a--canonical-local-order-on-the-feedback-boundary).

| Module | Purpose and principal interface |
| --- | --- |
| [GeneralNominalRegistryOrder](../../lean/Yulang/GeneralNominalRegistryOrder.lean) | `keys_membership` and `fresh` preserve allocation reservations; `generated`, `branch_models`, `request_ready`, `prepared`, `failed`, and `head_ready` transport the actual candidate semantics. `children` gives literal equality of the complete canonical emitted list. |
| [GeneralNominalCandidateReordering](../../lean/Yulang/GeneralNominalCandidateReordering.lean) | `survivor`, `inspection_pending`, `cycle_inspection_pending`, and `feedback_candidateK2` are equivalences at one general state. `inspection_witness` transports the exact inspected positions before testing recurrence there. |
| [GeneralNominalLocalReordering](../../lean/Yulang/GeneralNominalLocalReordering.lean) | `boundary_local` proves exact independent Local equivalence at one state. `resolves` preserves the full diagnostic tree. `reachable_local_order` restricts this theorem to the V5 input domain. `whereAccessible_of_readback` retains the explicit Readback premise; `whereAccessible_iff` only transports an existing witness. |
| [GeneralDictionaryCanonicalLocalOrder](../../lean/Yulang/GeneralDictionaryCanonicalLocalOrder.lean) | `CanonicalLocalOrder` copies the exact open V5 field. `exact_factorization` proves it equivalent to `FinalStateAgreement`, which compares both executor-returned states under one registry. `of_returned_state_equality` is a sufficient conditional bridge. |
| [GeneralDictionaryFinalOrderObstruction](../../lean/Yulang/GeneralDictionaryFinalOrderObstruction.lean) | A shared source-formed initial state is reachable for checked reordered registries. An unconstrained executor returns a pending state for one enumeration and a K2 state for the other. `not_canonicalLocalOrder` refutes the field for this executor only; it does not refute order independence of a faithful saturating executor. |

The proof reuses `GeneralRegistryReordering`, `GeneralCanonicalChildOrder`,
`GeneralDictionaryEmissionPlans`, `GeneralDictionaryRecursiveOrder`, and
`GeneralDictionaryRecursiveSemanticOrder`. Canonical children already have
identical source IDs, requests, associated equations, and enumeration. No new
quotient of child lists or dictionary payloads is introduced;
`GeneralDictionaryPayloadOrder.Equivalent` remains the boundary's dictionary
relation.

The exact V5 bridge count stays **6/14**. Same-state permutation invariance is
proved; final-state agreement is still required. No executor, Step, Stable,
Committed, Evidence, or language rule is changed. Progress/descent remains
paused, including the outstanding associated-output-growth owner question.

The new dependency audit is [Audit/AstraOrder.lean](../../lean/Audit/AstraOrder.lean).
The frozen `lean/Audit.lean` and `lean/README.md` are unchanged.
