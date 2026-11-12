# Committed packets and final-model source evidence

Status: Draft proof design, 2026-11-12. Scope: I-23, existing Astra saturation definitions unchanged.

The carrier is GeneralNominalSaturationState.State over the existing full nominal assignment. Source Evidence remains the cycle130 model-indexed recursive source judgment at state.context. Each committed packet entails its branch equations in every journal model, not a replacement existential branch witness. A current-context packet with the checked declaration metadata and preparation therefore gives a source Instance in each such model; the existing source evidence node constructor combines children in that same model.

Stable closes Installable packets, not arbitrary selected candidates. To construct an Installable packet from a selected local judgment, registration supplies a site and merge closure comes from Stable. Two other requirements remain: consistency with the whole journal and agreement with previously recorded alias choices. ContextComplete suffices for the first via the existing complete_consistency theorem. The second will be exposed explicitly as selected key agreement with every recorded packet whose occurrence identity is aliased to the selected occurrence. Neither requirement is asserted to follow from Stable or reachability.

Planned statements quantify over every registry, saturation state, occurrence, selected key and emitted children, then every model of that same state. With Stable, ContextComplete and alias choice agreement, selection gives a current-context committed packet. Its children have actual Generated edges. Its source Instance and Evidence hold for every state model, conditional only on same-model child Evidence. A separate packet-level bridge needs commitment and checked source facts but no ContextComplete or alias assumption.

This does not claim the unconditional concrete V4 EvidenceNode field. Context feedback and selected/recorded alias coherence are outstanding source invariants. No Stable definition, Survivor predicate, transition or source semantics is strengthened or weakened here.

## Verified implementation scope

`GeneralDictionaryCommittedEvidence` proves the packet and stable-selected bridges. `GeneralDictionarySaturationBoundary.boundary` supplies all thirteen predicate definitions using precisely Astra's carrier, unchanged transition and stability predicates, and the cycle130 source evidence at the current context. Its `closure`, `stepModels`, and `dictionaryRefl` have the actual V4 field types unconditionally. `evidenceNode_of_journal_invariants` and `generatedChildren_of_journal_invariants` retain the explicit `SelectedJournalInvariants` hypothesis. They are not completed unconditional fields.

`GeneralDictionaryCommittedEvidenceExamples` repairs the cycle130 terminal associated-output counterexample by an actual enabled install Step. Successor Models are exactly original models satisfying the declared int output equation. Every successor model has source Evidence, a good model exists, and the former bad model is excluded. This regression interprets evidence at the packet's stored source inspection context. It does not identify that context with the successor private context, nor prove fresh candidate preparation after regeneration.

Source invariants still needed: (1) feedback of every packet and site condition to ordinary context models (`ContextComplete`), and (2) agreement of a newly selected key with recorded alias keys. The current transition proofs do not establish these for every stable arbitrary State. An invariant-bearing carrier could make them explicit in a later interface, but would still require initialization and preservation proofs; no such carrier change is made here.

## Formal feedback scope check

`GeneralDictionaryStableFeedbackGap.stable_does_not_imply_feedback` constructs an arbitrary saturation State with a consistent fully-known ordinary context and an inconsistent stored packet. No packet installation is jointly enabled, the sole site already represents itself, and every context source is already known. The state is therefore Stable but not ContextComplete. The state is not claimed reachable. There are no journal models, so this does not refute V4 EvidenceNode; it precisely rules out silently deriving context feedback from the present Stable predicate on the unrestricted carrier.
