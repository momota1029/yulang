# Next item 5 bridges: allocated IDs and computed-frame order

This is a proposed decomposition, not a new theorem or implementation. References below describe the checked source definitions inspected after cycle128.

## 1. Concrete missing bridge: reserved type IDs to actual base slots

### Existing facts

- `GeneralNominalAllocation.source` uses the persistent seed and an origin tuple. `source_initial_fresh`, `source_identity`, and `source_preserved` establish relevant separation and stability facts.
- `GeneralNominalAllocation.propagate` calls `GeneralNominalState.extend` and adds ownership entries. `extend` changes only `reserved` and global `ordinary`; the base slot carrier does not grow.
- `GeneralNominalState.sources` combines base type IDs, base row IDs, reserved IDs, and IDs mentioned in global ordinary atoms. Its `Linked` therefore does not establish type-slot availability.
- `GeneralDictionaryHeadlessLocations.Available` requires actual `base.source` witnesses for every demand lower endpoint, upper endpoint, and output target. `locate_success_iff` is already the exact executable bridge once that property is proved.
- `GeneralDictionaryBinderLocations.sourceSlot_exact` characterizes each successful lookup. `locateTerm` additionally requires an actual type slot for a variable RHS. `GeneralDictionaryVariableHeads.DenotesAt` requires a captured singleton identity and an actual type slot.

Consequently, `Linked (privateState ...) child.demand → Available (privateState ...).base child.demand` is not justified in general. A reserved endpoint can satisfy the former while having no base type slot. Reusing `GeneralDictionaryHeadlessLocations.linked_available` would be a mistake: that theorem accepts `GeneralSourceState.Linked`, not the weaker nominal-state relation.

### Proposed first lemma, with minimal explicit premises

Introduce a typed finite coverage certificate, not a new allocator:

- Inputs: an existing nominal state `before`, a proposed base snapshot `after`, and a finite list `neededTypeIDs`.
- Premise: for each ID in that list, an actual slot of `after` maps to the same ID under `after.source`.
- Premise for the demand: every lower endpoint, upper endpoint, and requested output target is in `neededTypeIDs`.
- Conclusion: `GeneralDictionaryHeadlessLocations.Available after demand`, hence `∃ inputs, locate after demand = some inputs` by the existing theorem.

This small lemma needs neither a model nor candidate selection. It should be the first testable interface, followed by a regression where a reserved ID is unavailable before and available afterward. Preserve duplicate demand occurrences even when the coverage list contains an ID once.

### Operation still needed to discharge coverage

The actual missing operation is a conservative base-slot extension realizing an explicit finite set of authorized existing source identities. A certificate for that operation must retain:

1. An embedding of old slots preserving BOTH `source` and `rowSource`, and injectivity of the new type-source map.
2. Correct renaming of old local atoms, intervals, heads, normalized view, nominal descriptor parameter slots, and catalogue proofs.
3. Existing seed and origin ownership unchanged; reserved identities must not be recomputed from a new seed. Collisions cannot be resolved by identifying different IDs.
4. New slots initially carry no invented known head, nominal descriptor, or singleton/equality constraint.
5. Full nominal model equivalence for every global assignment, rather than only the Common-model refinement theorem.

`GeneralSourceState.Refines` supplies useful old-slot/source/row/ordinary/interval fields but is insufficient by itself for item 5 above: `refinement_models` is Common-specific and does not transport the full nominal descriptor/view obligations. A dedicated nominal extension certificate/model theorem is needed.

A choice of new row-source coordinates is not specified here. The representation pairs type and row coordinates at every slot. Require that mapping explicitly in the extension certificate, or coordinate its construction with the owning source-state work; never silently use the type ID as a row ID.

The finite needed set must include not just demand endpoints/targets but also captured type IDs used by supported head and explicit RHS variables. That addition permits use of `DenotesAt` and `locateTerm`; endpoint localization alone is not whole materialization completeness.

### Boundaries that remain even after this bridge

Adding slots does not equate different captured endpoint IDs. `GeneralDictionaryVariableHeads` and the input-variable arm of `GeneralDictionaryVariableTerms.bodyTerm` still require identity equality, not merely semantically equivalent values. Root output guards, readiness, coverage, unsupported compound/default RHSs, and generation of successor candidate contexts remain untouched. This extension must not be represented as the missing general Step.

## 2. Computed-frame equality under registry reordering

### Assessment

At a FIXED `GeneralNominalCandidates.Context`, fixed root, and checked registries sharing constructor/role catalogues, equality of `GeneralDictionaryNominalCandidateReadback.frames` under `GeneralRegistryReordering.Reorders` appears true. It is not blocked by order-sensitive allocation or global identity. This equality is a proposed theorem, not proved in cycle128.

The checkedness premise matters: the implementation uses `find?`, and duplicate keys with different heads could otherwise make the selected report depend on list order.

### Existing supporting facts and proof route

1. `GeneralRegistryReordering.reorders_visible` pairs visible declarations. `DeclarationReorders` preserves ID, role, head, associated equations and output binders; only requirement enumeration changes.
2. `GeneralDictionaryNominalCandidateReadback.declaration_found`, with `GeneralDictionaryEmissionPlans.declaration_key_unique`, pins successful lookup to the unique corresponding declaration. Absent key/role lookup is transported using both directions of the registry relation.
3. `GeneralNominalCandidates.arguments` depends on context/root, not registry. `GeneralNominalInspection.queries` uses only `declaration.normalHead` and the fixed context. Thus corresponding declarations have equal reports, including inspected order and captures. Where-clause order does not enter this computation.
4. Prove `bindings` equality, including the absent-lookup/absent-arguments fallback cases. Do NOT try to prove the selected full declarations equal: their requirement lists may be reordered.
5. `GeneralNominalAllocation.source` ignores its registry/root parameters beyond the already supplied origin; `source_registry_independent` states registry independence. Allocation and frame identity use stable invocation/key/clause/position origins. Equal bindings therefore give equal capture functions, and allocation/identity functions agree pointwise.
6. Apply frame/function extensionality. State the theorem using two declaration lists with common constructor/role catalogues, as in `GeneralDictionaryPayloadReconstructionOrder`, to avoid unnecessary dependent casts.

`keys` and `reserved` can change LIST order under reordering, but neither list is read to compute frame field values. Their order is not an obstruction to this specific theorem. Full propagated-state equality, ownership-list equality, or candidate invariance after different state evolutions does not follow.

### Immediate payoff

Combining computed-frame equality with existing `GeneralDictionaryPayloadReconstructionOrder.reconstruct_reorders` and `prepare_reorders` gives fixed-context optional-result invariance for the no-caller-Frames wrappers. It still says nothing about different final snapshots, recursive child contexts, driver order, or existence of a complete candidate forest.

## Verification status

Read-only design review of the named definitions/theorems; no implementation, theorem checking, new semantics, or shared-checkout edits were performed for this note.
