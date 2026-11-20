# Cycle 288 test matrix

The hypotheses of the generic helpers remain explicit. The fixture theorems
instantiate them; no existential placeholder supplies a missing condition.

| Data tested | Required outcome | Lean witness |
|---|---|---|
| Original one-parent raw endpoint, opaque child | Whole-type leaf uniquely selected, request-free, packet from original source; no existing ledger discharge or old Refresh carrying slot 2 | `RowLeafWitness288.leaf`, `RowLeafMark288.auxiliary_only`, previous `RowSettlement287` |
| Same actual source/output, row-destructuring child | No correct current frame, no source-certified leaf, no alternative one-output slice; remains pending rather than rejected | `RowLeafWitness288.no_leaf/parent_iff`, `RowLeafSlice288.extension_iff`, previous `RowGeneratedChild287.pending_actual` |
| One augmented output fact over the old input prefix | Exact old source and output equations; both branches have those models but only the opaque branch has the independent proof | `RowLeafSlice288.prefix_exact/slice_exact/same_models/extension_iff` |
| Guarded static supplement (plan list only) | Same models, core and effects; old trusted cache available; real Step from new data yet no raw trace to the new ledger | `RowLedger288.layouts/models_eq/old_refresh`, `RowLedgerStep288.real_refresh_at_hypothetical_state/no_raw_path_to_supplement` |
| Unscoped foreign plan from the other registry | Same occurrence and same full Models despite syntactic settlement and trusted output; no frame or dictionary under checked intended registry; not source-reachable | `ForeignLeaf288.semantic_shortcut_counterexample/no_correct_frame/no_raw_path` |
| Private reserved aggregate address | Actually listed, yet no certified cache in this family can recognize its type head | `RowLedgerNames288.actual_listed/listed_not_recognizable` |
| Every legal guarded refresh, not a single picked layout | Must mark type identity 2 with the point F(type identity 1) up to embedding; no further step (other sites current and committed); exact one-step maximal endpoints | `RowLedgerFirst288.only_output_refresh`, `RowRefreshShape288.actually_nominal`, `RowRefreshHalt288.maximal_iff/scoped_accessible` |
| Old output projection vs executable auxiliary phase | All three guarded-family phases have the same two-fact output view and Models; phase edge iff corresponding raw step; foreign state has same ready phase but fails Family | `RowPhaseSimulation288.exact_observer/all_output_views_same`, `RowLedgerPhase288.phase_cannot_certify_membership`; exact pure phase transition table checked in standalone audit |
| Fresh certificate from all *source* models after marking | Top at output alone preserves source slice; exact current packet fails, so cannot demand new whole-snapshot Leaf or any raw Evidence at that assignment | `RowLeafLifetime288.no_fresh_leaf`, `RowRefreshEvidence288.no_source_dictionary_at_mark` |
| Same Top witness with local equations only | Leaf inputs/outputs and class effects still pass; actual root head is source-supported and nested reads are empty | `RowLeafLocality288.exact_obstruction`, `RowLeafSourceHeads288.actual_source_scoped_checks/nested_reads_empty` |
| V8 evidence after every guarded refresh | All full models have exactly payload `.node 0 [.node 1 []]`; canonically completing type slot 2 suffices starting from any valid source input and preserves every row | `RowRefreshEvidence288.exact_payload`, `RowRefreshProjection288.completion_exact/exact_support/completed_coordinates` |
| Actual emission and lifetime | No receipt before child exists; fresh full-snapshot source witness exists only on the opaque original endpoint and fails after marking | `RowLeafWindow288.actual_activation_window/post_mark_absent` |
| Scoped leaf receipt vs strong whole-context witness | Source-read/local receipt exists after each guarded refresh; ordinary evidence uses full Models only for the ambient conjunct; the unscoped and pre-emission states cannot pass | `RowLeafReceipt288.strong_and_weak_separate/no_foreign_receipt/no_pre_emission_receipt` |
| Actual V8 diagnosis after arbitrary guarded refresh | Exactly `.selected 0 [.selected 1 []]`, not merely propositional existence of a dictionary | `RowRefreshDiagnostics288.safe/selected_child/exact_tree` |
| Exact typed dependencies of two actual recorded observations | Opaque child head uses type 0 and row 0 on arbitrary assignments; output mark needs only types 1 and 2 and no private type or ambient row | `RowLeafHeadSupport288.typed_support_minimal`, `RowOutputHeadSupport288.actually_recorded/no_private_or_row_read` |
| Old matching guard on the opaque leaf and pending contrast | The receipt implies the retained root head is ready; the real row-pattern branch itself also passes the old DecisionGuard because deferred inspection contributes no nested reads. It remains pending with models and no dictionary | `RowLeafDecisionGuard288.actual_guard`, `RowDeferredDecisionGuard288.not_a_settlement_criterion` |

The experiment neither installs a new rule nor changes spec, parser/Rust,
legacy snapshots, existing module sources, or aggregate termination. The
guarded Phase family excludes the foreign ledger and is not a source validator.
The ledger supplement is not the output projection and cannot be reached by
the original raw source trace. See the design note for which tempting
generalizations these closed counterexamples refute.
