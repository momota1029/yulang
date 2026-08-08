//! CPK-0c proof-state inventory guard and projection-admission fixture matrix.
//!
//! Rust does not expose source-level reflection to unit tests. The inventory guard therefore
//! combines two deliberately simple checks: an exact lexical census of every reviewed proof-state
//! surface, and an allowlist of the writer/consumer boundaries approved by the CPK-0 addendum.
//! A direct access added anywhere in the reviewed sources changes the census and forces the author
//! to classify the site before updating this oracle.

// CPK-8A raw fixture-writer freeze. These are deliberately low-level test admissions, not
// production authority boundaries. The lexical gate below makes a newly introduced shortcut
// visible before CPK-8B can remove its legacy backing field.
//
// A correctness-contract: 5 CPK proof query fixtures with an explicit proof-store mirror.
// B historical Legacy characterization: 0 after CPK-8G-6e closes all 60 retirements.
// C semantic fixture: 9 local semantic/provenance fixtures that inspect record identity.
// D fixture-construction debt: 0; the CPK-6b/CPK-7 hygiene passes migrated every known
// oracle-active shortcut to a mirrored admission path.
//
// These counts classify lexical writer sites, not every caller of a shared fixture. CPK-8B splits
// the dual-purpose CDM fixture at an explicit proof-state boundary: CPK-0b/0c use the mirrored
// variant. The follow-up caller audit classified the historical RCPF/CDM/DPN flat/factored
// representation, failure, delta, and census characterizations as B; CPK-8G-6b-e retire all 60
// after their CPK-owned replacements land. No Legacy-only shared constructor remains. CPK-8E-5 retires
// six of those purposes (including the carrier-order helper/test pair); 44 remain compiled for 8G.
//
// Production read/write graph for CPK-8B, grouped by physical field ownership:
// - upper_replay_claims and its record/root/producer indexes: writers original/derived claim,
//   claim move, register_constraint_upper_replay_claims; after CPK-8G-6f they are write-only flat
//   mirrors while CPK owns projection/routing reads.
// - CPK-8G-7a closes the CPK parent read view. CPK-8G-7b1/b2 remove the replay and structural
//   exact-key mirrors independently; CPK-8G-7b3 removes the qualified-carrier projection; and
//   CPK-8G-7b4 removes the final claim-parent Vec mirror while preserving the CPK admission and
//   RCPF one-way feed. All five CPK-8G-7 sub-slices are complete.
// - live_coverage_by_root remains the claim-lifecycle migration mirror after CPK-8B transfers
//   transition/dedup ownership to ProofOccurrenceStore::live_states_by_coverage_root. CPK-8G-8a2
//   removes the separate five-field flat support/root bundle after CPK takes both its reads and
//   mutation decisions; clause and claim mirrors remain in their later physical-removal slices.
// - CPK-8G-8a2 leaves projection supports solely in ProofOccurrenceStore. CPK-8G-8b0 transfers
//   typed clause admission to CPK and CPK-8G-8b1 removes the seven-field flat clause/link/
//   attribution mirror. Dependent-record edges remain for the later 8G-8c removal slice.
// - ParentSetArena/ReplayOccurrenceStore/ReplayResultSummary/ReplayClauseProjection/
//   NonReplayClaimParentStore: writers replay admission and parent mutation; readers Factored
//   replay authority and exact test-only shadow capture. CPK-8B must replace writers before any
//   physical removal.

// CPK-8E-0 final migration-parity snapshot, frozen at 8d208792 before oracle retirement.
// This is a manifest of CPK-observable contracts, not a serialized snapshot of Legacy storage.
// The baseline commands are the `cpk_` and `rcpf_` lib-test filters plus the exact-carrier-order
// test. Together they pin the following surfaces for the later independently revertible slices:
// - CPK-2/3 occurrence order, exact replay finite map, first witness, trivial/evidence admission,
//   and the semantic execution snapshot;
// - CPK-4 projection decisions and publication classes for Standalone, DerivedUnary, and
//   ReplayConjunction formulas, including canonical supports and all five lineage sources;
// - CPK-5/7 prepared route parent root/claim/side/lineage order, event counts, target-late,
//   same-root, claim-move, and endpoint-decoupling behavior;
// - the deliberate-retirement baselines cdm_a_9_2_exact_carrier_arrival_order_preserves_bulk_snapshot,
//   rcpf_e2a_claimed_attribution_matrix_partitions_all_five_sources_at_the_writer,
//   rcpf_e2b_claimed_attribution_union_mismatch_quarantines_event_oracle,
//   rcpf_event_oracle_is_opt_in_and_shadow_writes_do_not_interfere,
//   rcpf_event_oracle_mismatch_is_quarantined_after_legacy_noop, and
//   rcpf_shadow_exact_relation_matches_legacy_across_extensions_and_carriers;
// - the replacement prerequisites rcpf_clause_projection_bootstraps_after_the_target_record_consumes_metadata,
//   rcpf_clause_projection_excludes_evidence_and_trivial_replays, and
//   rcpf_f_consumer_2_factored_dependency_chain_matches_legacy_oracle.
// Later CPK-8E slices may remove an oracle assertion only after its typed CPK contract above is
// direct, or after the deliberate-retirement reason is recorded without changing expectations.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cpk8RawFixtureWriterClass {
    CorrectnessContract,
    HistoricalLegacyCharacterization,
    SemanticFixture,
    FixtureConstructionDebt,
}

const CPK8_RAW_FIXTURE_WRITER_CLASSIFICATION: &[(Cpk8RawFixtureWriterClass, usize)] = &[
    // CPK-8G-6a moves the D3b canonical-fixture normalization read/write onto the CPK store.
    (Cpk8RawFixtureWriterClass::CorrectnessContract, 5),
    // CPK-8G-6d retires the final raw Legacy parent/occurrence characterization writer.
    (Cpk8RawFixtureWriterClass::HistoricalLegacyCharacterization, 0),
    // CPK-8G-2b moves twelve reviewed original-claim fixture calls behind the CPK-owned
    // allocation transaction. CPK-8G-2c moves the final two direct derived-claim fixture
    // calls behind the same CPK-owned transaction; they are no longer raw flat-store writers.
    (Cpk8RawFixtureWriterClass::SemanticFixture, 9),
    (Cpk8RawFixtureWriterClass::FixtureConstructionDebt, 0),
];

const CPK8_RAW_FIXTURE_WRITER_TOTAL: usize = 14;

const CPK8_CDM_MIRRORED_FIXTURE_CALLERS: &[&str] = &[
    "cpk_0b_captures_canonical_logical_proof_surfaces_end_to_end",
    "cpk_0c_fixture_matrix_captures_semantic_and_logical_baselines",
];

const CPK8_CDM_FIXTURE_CALLER_CLASSIFICATION: &[(Cpk8RawFixtureWriterClass, usize)] = &[
    (Cpk8RawFixtureWriterClass::CorrectnessContract, 2),
    // CPK-8G-6b-e retire every historical Legacy/RCPF comparison caller after its CPK-owned
    // replacement lands.
    (Cpk8RawFixtureWriterClass::HistoricalLegacyCharacterization, 0),
    (Cpk8RawFixtureWriterClass::SemanticFixture, 0),
    (Cpk8RawFixtureWriterClass::FixtureConstructionDebt, 0),
];

const CPK8_CDM_LEGACY_ONLY_FIXTURE_CALLERS: &[&str] = &[];

// CPK-8E deliberate retirements. The CDM snapshot helper existed only for its adjacent test;
// the three event-oracle entries characterized migration infrastructure with no product-facing
// contract. The other properties are frozen by the CPK same-root, attribution, finite-map,
// first-witness, and five-lineage contract tests before these names disappear. The MPC fail-open
// entry characterized only the removed Legacy projection reader; its adjacent CPK test freezes the
// product contract as an attempt-terminal MissingProofFact failure.
const CPK8E_RETIRED_LEGACY_TESTS_AND_HELPERS: &[&str] = &[
    "cdm_a_9_2_exact_carrier_arrival_order_preserves_bulk_snapshot",
    "cdm_carrier_order_snapshot",
    "rcpf_e2a_claimed_attribution_matrix_partitions_all_five_sources_at_the_writer",
    "rcpf_e2b_claimed_attribution_union_mismatch_quarantines_event_oracle",
    "rcpf_event_oracle_is_opt_in_and_shadow_writes_do_not_interfere",
    "rcpf_event_oracle_mismatch_is_quarantined_after_legacy_noop",
    "rcpf_shadow_exact_relation_matches_legacy_across_extensions_and_carriers",
    "mpc_a_9_5_legacy_unattributed_claim_link_fails_open",
];

// CPK-8G-4b deliberate retirements. These tests injected a dangling ReplayOccurrenceId into
// RCPF's separate by-result/occurrence arenas and asserted that the former RCPF publication reader
// quarantined the attempt. Publication authority now reads CPK's inline qualified-parent payload;
// machine-issued append-only IDs and atomic CPK admission make that RCPF-only dangling-ID shape
// unreachable. The CPK evaluator's debug invariant test replaces their storage-appropriate guard.
const CPK8G4B_RETIRED_RCPF_PUBLICATION_TESTS_AND_HELPERS: &[&str] = &[
    "factored_evaluator_failure_does_not_publish_projection_intent",
    "rcpf_d2c_2c_1_missing_occurrence_publication_fixture",
    "rcpf_d2c_2c_1_snapshot_evaluation_failure_does_not_publish",
    "rcpf_c3d_factored_read_error_quarantines_the_production_attempt",
];

// CPK-8G-6b category-B retirements. Each entry records the exact CPK-owned contract that makes
// the former migration comparison or Legacy/RCPF storage characterization redundant.
const CPK8G6B_RETIRED_PROOF_ORACLE_AND_REPLACEMENT_BACKED_TESTS: &[(&str, &str)] = &[
    (
        "cpk_5_generic_route_matches_legacy_and_counts",
        "CPK-7 direct PreparedReplayRoute generic-pair and five-lineage tests pin the CPK routing payload; Legacy event-count equality was migration-only",
    ),
    (
        "cpk_5_incremental_only_and_skip_routes_match_legacy",
        "CPK-7 direct covered-pair, incremental-only, and skip disposition tests pin every surviving route decision; Legacy accepted-count equality was migration-only",
    ),
    (
        "cpk_5_routing_is_invariant_across_same_root_parent_arrival_orders",
        "CPK-7 canonical-parent, first-witness, and same-root permutation tests directly pin order invariance without the routing oracle",
    ),
    (
        "cpk_7_shadow_oracle_rejects_claim_index_corruption",
        "cpk_7_cpk_authority_preflight_rejects_claim_index_corruption and CPK attempt-terminal tests directly pin dangling-claim rejection; only the migration oracle panic is retired",
    ),
    (
        "rcpf_clause_projection_bootstraps_after_the_target_record_consumes_metadata",
        "cpk_projection_target_late_metadata_bootstraps_formula directly pins target-late formula, publication, and projection behavior in the CPK-owned indexes",
    ),
    (
        "rcpf_clause_projection_excludes_evidence_and_trivial_replays",
        "cpk_evidence_and_trivial_replays_do_not_create_projection_formula directly pins the no-formula/no-support contract in CPK",
    ),
    (
        "rcpf_f_consumer_2_factored_dependency_chain_matches_legacy_oracle",
        "cpk_premise_dependency_chain_contains_exact_replay_endpoints directly pins canonical constraint and replay-endpoint dependency edges",
    ),
];

// CPK-8G-6c category-B retirements. These flat/CDM tests characterized the representation that
// remains dual-written through 8G-6 but is no longer a production reader. Each reason names the
// CPK-owned contract that survives physical removal; the three dedicated census helpers are
// tracked separately because their manifest entries stood in for adjacent tests.
const CPK8G6C_RETIRED_FLAT_CDM_TESTS: &[(&str, &str)] = &[
    (
        "cdm_a_9_1_current_eager_path_matches_bulk_oracle",
        "cpk_claim_payload_matches_flat_across_five_lineages_and_move and the CPK-only logical snapshot pin eager claim materialization without the flat bulk oracle",
    ),
    (
        "cdm_a_9_4_independent_then_claimed_keeps_both_occurrences",
        "cpk_gap_1_mixed_claim_fixture_matches_all_four_cpk_consumers_exactly and the CPK-only canonical transition fixtures pin independent-then-claimed support",
    ),
    (
        "cdm_a_9_5_second_exact_carrier_keeps_bookkeeping_without_rematerializing_root",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed pins exact-carrier dedup and one-time root materialization in CPK",
    ),
    (
        "cdm_a_9_6_materialized_state_census_is_linear_in_link_events",
        "cpk_7_slice_a_claim_index_writes_do_not_scan_the_global_claim_store and CPK's event-local claim indexes replace the flat materialization census",
    ),
    (
        "moved_root_collision_reconstructs_original_full_and_delta_lineage",
        "cpk_claim_payload_matches_flat_across_five_lineages_and_move and cpk_claim_move_updates_record_coverage_and_preserves_root_liveness pin moved-root lineage and coverage",
    ),
    (
        "cdm_b_all_claim_parent_writer_kinds_update_qualified_carrier_index",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed and cpk_gap_1_five_lineages_project_through_the_real_formula_graph pin every CPK parent kind",
    ),
    (
        "cdm_b_debug_cross_check_rejects_a_deliberately_corrupted_index",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed plus cpk_8g_4b_evaluator_traps_missing_machine_issued_references replace the flat-index debug cross-check",
    ),
    (
        "cdm_b_qualified_carrier_index_census_is_linear_in_distinct_carriers",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed and cpk_7_slice_a_prepared_parent_blocks_share_exact_entries pin event-local exact-parent indexing without a global scan",
    ),
    (
        "lower_and_upper_replay_planning_capture_legacy_parent_drafts",
        "cpk_7_slice_a_prepared_parent_blocks_share_exact_entries and the CPK lower-only/upper-only parent-block tests directly pin replay planning payloads",
    ),
    (
        "replay_claim_parent_dedup_keeps_each_exact_replay_carrier",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed pins exact replay carrier identity and dedup in the CPK-owned index",
    ),
    (
        "cdm_d_9_3_evidence_only_emits_replay_evidence_delta",
        "cpk_3_evidence_only_replay_records_both_bound_edges_in_active_shadow and cpk_evidence_and_trivial_replays_do_not_create_projection_formula pin the evidence-only CPK payload",
    ),
    (
        "cdm_d_9_3_one_sided_lower_emits_bound_delta",
        "cpk_2_non_replay_proof_events_match_frozen_contract and the direct CPK PreparedReplayRoute tests pin one-sided lower admission",
    ),
    (
        "cdm_d_9_3_promotion_emits_single_bound_derivation_delta",
        "cpk_2_non_replay_proof_events_match_frozen_contract pins the typed CPK bound-derivation occurrence emitted by promotion",
    ),
    (
        "cdm_d_9_3_replay_canonical_duplicate_emits_exact_carrier_delta",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed and direct CPK parent-block tests pin canonical duplicate exact-carrier admission",
    ),
    (
        "cdm_d_9_3_replay_new_emits_lower_delta_without_bulk_fallback",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed and direct CPK replay-route tests pin new replay admission without bulk fallback",
    ),
    (
        "cdm_d_9_3_replay_prefiltered_duplicate_emits_exact_carrier_delta",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed pins prefiltered duplicate exact-carrier admission in CPK",
    ),
    (
        "cdm_d_9_3_reduction_route_emits_row_carrier_delta",
        "cpk_claim_payload_matches_flat_across_five_lineages_and_move and cpk_gap_1_five_lineages_project_through_the_real_formula_graph pin reduction-route lineage",
    ),
    (
        "cdm_d_9_3_structural_admission_emits_structural_carrier_delta",
        "cpk_claim_payload_matches_flat_across_five_lineages_and_move and cpk_gap_1_five_lineages_project_through_the_real_formula_graph pin structural lineage",
    ),
    (
        "mpc_b_clause_and_dpn_a_edge_census_are_linear_in_link_events",
        "cpk_projection_target_and_dependency_admission_is_atomic_and_target_late pins event-local CPK clause and dependency indexing",
    ),
    (
        "factored_record_lower_projection_includes_direct_and_qualified_roots",
        "cpk_gap_1_mixed_claim_fixture_matches_all_four_cpk_consumers_exactly and the CPK formula graph tests pin direct and qualified root inclusion",
    ),
];

const CPK8G6C_RETIRED_FLAT_CDM_DEDICATED_HELPERS: &[&str] = &[
    "assert_replay_shadow_does_not_interfere",
    "cdm_linear_materialization_census",
    "cdm_linear_qualified_carrier_index_census",
    "dpn_linear_registration_census",
];

// CPK-8G-6d category-B retirements. These bounds-level tests used RCPF parent/occurrence stores
// as migration comparators or injected failures after the authoritative CPK transaction. Direct
// replay_factored.rs structure tests remain compiled for 8G-9/10.
const CPK8G6D_RETIRED_RCPF_PARENT_OCCURRENCE_TESTS: &[(&str, &str)] = &[
    (
        "rcpf_c1_query_facade_reuses_the_occurrence_store_indexes",
        "cpk_3_exact_replay_and_first_witness_match_factored_oracle and the CPK-only logical snapshot pin indexed replay occurrence lookup",
    ),
    (
        "rcpf_c1_no_claim_and_replay_only_records_allocate_no_non_replay_storage",
        "cpk_no_claim_path_allocates_no_claim_storage_or_index_work pins zero allocation for the CPK no-claim path",
    ),
    (
        "rcpf_c1_non_replay_store_matches_legacy_for_structural_reduction_and_mixed_records",
        "cpk_gap_1_five_lineages_project_through_the_real_formula_graph pins structural, reduction, and mixed qualified parents in CPK",
    ),
    (
        "rcpf_c1_non_replay_store_preserves_structural_and_reduction_exact_dedup",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed pins exact structural and reduction parent dedup",
    ),
    (
        "rcpf_c1_non_replay_store_failure_quarantines_after_legacy_admission",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed pins no-partial-commit failure handling before any downstream mirror write",
    ),
    (
        "rcpf_c2_factored_replay_inspections_scale_with_occurrences_not_roots",
        "cpk_7_slice_a_replay_indexes_update_atomically_with_writers and the event-local CPK exact-parent index replace the RCPF inspection census",
    ),
    (
        "rcpf_c2_factored_evaluator_uses_structural_and_reduction_flat_sources",
        "cpk_gap_1_five_lineages_project_through_the_real_formula_graph pins CPK evaluator decisions for structural and reduction sources",
    ),
    (
        "rcpf_c3b_replay_parent_admission_uses_one_hash_probe_per_parent",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed and cpk_7_slice_a_prepared_parent_blocks_share_exact_entries pin event-local exact-parent admission",
    ),
    (
        "rcpf_c3b_terminal_failure_stops_drain_before_the_next_queued_work",
        "cpk_terminal_failure_stops_drain_before_the_next_queued_work directly pins the surviving queue-stop contract on the CPK terminal channel",
    ),
    (
        "rcpf_d3a_0b_cross_kind_winner_matches_legacy_for_both_orders_and_kinds",
        "target_late_mixed_roots_do_not_expose_historical_order_to_later_replay and the CPK first-source index pin replay-first and non-replay-first winners",
    ),
    (
        "rcpf_d3a_0b_winner_failure_follows_legacy_parent_and_route_commit",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed plus whole-attempt discard pin authoritative CPK state and downstream failure isolation",
    ),
    (
        "rcpf_phase_b_failure_preserves_legacy_parent_admission_before_terminal_stop",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed and the typed hard-error discard tests replace legacy-before-RCPF failure ordering",
    ),
    (
        "rcpf_summary_first_witness_tracks_legacy_insertion_order",
        "cpk_3_replay_first_winner_matches_factored_for_every_parent_arrival_order pins CPK first-witness identity across arrival orders",
    ),
    (
        "factored_record_lower_projection_keeps_first_winner_for_new_occurrence_old_root",
        "target_late_mixed_roots_do_not_expose_historical_order_to_later_replay pins the CPK first-source winner and projection result for both arrival orders",
    ),
];

const CPK8G6D_RETIRED_RCPF_PARENT_OCCURRENCE_DEDICATED_HELPERS: &[&str] = &[
    "add_derived_replay_parent_claim",
    "add_original_replay_parent_claim",
    "apply_factored_canonical_duplicate_snapshot",
    "assert_non_replay_store_matches_legacy",
    "factored_replay_first_witness_oracle",
    "legacy_non_replay_claim_parents",
    "legacy_replay_first_witness_oracle",
    "rcpf_c2_replay_inspection_census",
    "rcpf_c3b_replay_parent_admission_census",
];

const CPK8G6D_RETIRED_RCPF_PARENT_OCCURRENCE_TYPE_ALIASES: &[&str] =
    &["ReplayFirstWitnessOracleValue"];

// CPK-8G-6e completes category-B retirement. These tests pinned Legacy/RCPF sequencing,
// quarantine, and projection-reader behavior after CPK had already become the sole production
// authority. Each surviving property is named below; old Legacy-before-RCPF commit order and
// mirror-corruption behavior are deliberately retired rather than recast as product contracts.
const CPK8G6E_RETIRED_RCPF_PUBLICATION_FAILURE_READER_TESTS: &[(&str, &str)] = &[
    (
        "rcpf_c3a_legacy_rollback_disables_factored_writers_and_oracles",
        "rcpf_c3a_normal_attempt_runs_once_without_authority_dispatch and the CPK-only reader chain pin the surviving single-authority behavior; suppressing obsolete RCPF mirrors under Legacy rollback was migration-only",
    ),
    (
        "rcpf_d2a_legacy_rollback_split_preserves_immediate_publication_sequence",
        "target_late_mixed_roots_do_not_expose_historical_order_to_later_replay plus the CPK publication evaluator tests pin epoch, affected-owner, and projection sequences without Legacy split/combined parity",
    ),
    (
        "rcpf_d2b_factored_clause_projection_failure_keeps_legacy_links_and_edges",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed and cpk_projection_target_and_dependency_admission_is_atomic_and_target_late pin authoritative links and edges before the downstream one-way feed",
    ),
    (
        "rcpf_d2c_1_phase_b_failure_blocks_materialization_and_event_oracle",
        "CPK qualified-parent and projection-index preflight tests pin no partial authoritative commit, while rcpf_c3a_failed_attempt_is_discarded_as_typed_hard_error pins downstream whole-attempt discard",
    ),
    (
        "rcpf_d2c_2a_clause_projection_failure_stops_before_materialization",
        "CPK qualified-parent atomicity and typed whole-attempt discard replace the obsolete Legacy-Phase-A-before-RCPF-failure ordering",
    ),
    (
        "rcpf_d2c_2c_2a_deferred_clause_intent_preserves_immediate_value",
        "cpk_projection_target_late_metadata_bootstraps_formula, dpn_b_9_5_late_constraint_route_retriggers_dependent_record, and the CPK-only target-late fixture pin immediate value, deferred publication, epoch, and affected-owner behavior",
    ),
    (
        "rcpf_d2c_2c_2b_later_phase_c_failure_discards_whole_event_publication",
        "rcpf_c3a_failed_attempt_is_discarded_as_typed_hard_error pins whole-attempt output discard, and CPK qualified-parent/projection transactions pin authoritative no-partial-commit state",
    ),
    (
        "rcpf_d4_non_replay_pre_consumer_failure_blocks_phase_c_and_publication",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed covers non-replay parents and CPK projection-index atomicity plus whole-attempt discard prevent observable Phase-C publication",
    ),
    (
        "rcpf_d4_replay_pre_consumer_failure_blocks_phase_c_and_publication",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed covers replay parents and CPK projection-index atomicity plus whole-attempt discard prevent observable Phase-C publication",
    ),
    (
        "rcpf_e2c_a1_read_failure_keeps_legacy_phase_a_before_terminal_stop",
        "CPK qualified-parent atomicity and typed whole-attempt discard replace the retired Legacy-Phase-A-before-RCPF-reader failure order",
    ),
    (
        "rcpf_f_consumer_2_factored_lookup_failure_commits_no_dependency_edges",
        "cpk_projection_target_and_dependency_admission_is_atomic_and_target_late pins preflight-before-edge-commit, while cpk_premise_dependency_chain_contains_exact_replay_endpoints pins the successful chain",
    ),
    (
        "rcpf_f_consumer_2_legacy_rollback_ignores_factored_occurrence_corruption",
        "cpk_8g_4b_evaluator_traps_missing_machine_issued_references and CPK append-only atomic admission replace the RCPF dangling-occurrence shape; Legacy ignoring a corrupt obsolete mirror is historical",
    ),
    (
        "target_late_legacy_rollback_reproduces_epoch_publication_and_consumer_sequences",
        "target_late_mixed_roots_do_not_expose_historical_order_to_later_replay pins the full CPK-only publication and downstream consumer sequence for both winner and root orders",
    ),
    (
        "rcpf_d4_4_quarantine_discards_attempt_without_legacy_retry",
        "cpk_8f3_rcpf_failure_does_not_start_a_second_proof_attempt and rcpf_c3a_failed_attempt_is_discarded_as_typed_hard_error pin single-attempt hard failure and output discard",
    ),
    (
        "factored_lower_full_oracle_matches_target_late_bootstrap",
        "cpk_projection_target_late_metadata_bootstraps_formula directly pins CPK target-late claimed roots, formula keys, publication class, and projection decision",
    ),
    (
        "factored_lower_delta_oracle_matches_populated_replay_delta",
        "canonical_projection_storage_is_invariant_across_all_four_event_permutations and the CPK-only target-late fixture pin the populated claimed-root delta and canonical key",
    ),
    (
        "factored_lower_oracle_mismatch_quarantines_after_legacy_commit",
        "cpk_8g_4b_evaluator_traps_missing_machine_issued_references and cpk_gap_1_every_proof_failure_is_attempt_terminal replace flat-mirror mismatch quarantine with CPK-native invariant and terminal-failure coverage",
    ),
    (
        "factored_record_lower_projection_preserves_independent_supports",
        "cpk_gap_1_mixed_claim_fixture_matches_all_four_cpk_consumers_exactly and canonical_projection_storage_is_invariant_across_all_four_event_permutations pin mixed claimed and independent support",
    ),
    (
        "factored_record_lower_projection_transitions_independent_then_claimed_canonically",
        "cpk_projection_target_late_metadata_bootstraps_formula and canonical_projection_storage_is_invariant_across_all_four_event_permutations pin independent-to-claimed canonical order and MetadataOnly publication",
    ),
];

const CPK8G6E_RETIRED_RCPF_PUBLICATION_FAILURE_READER_HELPERS: &[&str] = &[
    "admit_factored_replay",
    "d4_phase_c_state",
    "legacy_only_cdm_replay_claim_fixture",
    "legacy_only_cdm_replay_claim_fixture_with_authority",
    "legacy_rollback_proof_authority",
    "legacy_rollback_test_authority",
    "lower_quarantine_fixture_once",
    "new_with_authority",
    "replay_factored_storage_census",
    "run_target_late",
];

const CPK8G6E_RETIRED_RCPF_PUBLICATION_FAILURE_READER_TYPES: &[&str] = &[
    "CdmReplayClaimFixtureProofState",
    "D4PhaseCState",
    "ReplayFactoredStorageCensus",
    "TargetLateMaterializationRead",
];

const CPK8G6_RETIRED_CATEGORY_B_TOTAL: usize =
    CPK8G6B_RETIRED_PROOF_ORACLE_AND_REPLACEMENT_BACKED_TESTS.len()
        + CPK8G6C_RETIRED_FLAT_CDM_TESTS.len()
        + CPK8G6D_RETIRED_RCPF_PARENT_OCCURRENCE_TESTS.len()
        + CPK8G6E_RETIRED_RCPF_PUBLICATION_FAILURE_READER_TESTS.len();

// CPK-8G-6 closure ledger. The first five slices dispose the reviewed test dependents before the
// code-level irreversibility boundary; the next three remove the authority/reader surfaces; 6h
// permanently gates that combined result while leaving the physical RCPF stores for 8G-9/10.
const CPK8G6_COMPLETED_SUBSLICES: &[(&str, &str)] = &[
    (
        "8G-6a",
        "migrated 14 category-A contracts to CPK-only fixtures and corrected the 60-test category-B census",
    ),
    (
        "8G-6b",
        "retired seven proof-oracle and replacement-backed category-B tests",
    ),
    (
        "8G-6c",
        "retired twenty flat/CDM characterization tests",
    ),
    (
        "8G-6d",
        "retired fourteen RCPF parent/occurrence migration characterizations",
    ),
    (
        "8G-6e",
        "retired the final nineteen RCPF publication/failure/Legacy-reader characterizations",
    ),
    (
        "8G-6f",
        "removed Proof authority, migration observations, comparators, and Legacy proof readers",
    ),
    (
        "8G-6g1",
        "removed flat/RCPF Legacy-comparison reader adapters",
    ),
    (
        "8G-6g2",
        "removed Replay authority selection while preserving the unconditional RCPF feed",
    ),
    (
        "8G-6h",
        "closed zero-reference gates and froze the RCPF structure-test deferral",
    ),
];
const CPK8G6_COMPLETED_SUBSLICE_TOTAL: usize = 9;

// CPK-8G-6f crosses the code-level irreversibility boundary after all Category-B dependents retire.
// These names are mechanically forbidden in the production/test sources that formerly implemented
// Proof authority selection and its migration observations. Replay authority is tracked separately
// by the 8G-6g2 ledger below because its former gate also controlled RCPF mirror writes.
const CPK8G6F_REMOVED_PROOF_AUTHORITY_SURFACES: &[&str] = &[
    "ProofReadAuthority",
    "proof_read_authority",
    "cpk_proof_oracle_active",
    "ReplayRoutingShadowToken",
    "ShadowReplayRouteObservation",
    "ShadowReplayDirection",
    "ShadowReplayEventObservation",
    "ShadowProjectabilityObservation",
    "ShadowProjectionPublicationClass",
    "ShadowProjectionPublicationObservation",
    "projectability_observations",
    "projection_publication_observations",
    "replay_route_observations",
    "replay_event_observations",
    "compare_projection_record_shadow",
    "compare_projection_publication_shadow",
    "begin_replay_routing_shadow",
    "compare_replay_route_shadow",
    "finish_replay_routing_shadow",
    "legacy_prepared_replay_route",
    "record_legacy_replay_parent_snapshot",
    "legacy_scheme_projectable_lowers",
];

// CPK-8G-6g1 removes the flat-vs-RCPF Legacy comparison adapter after its final historical
// dependents retire. The surviving Factored evaluator test reads RCPF directly and retains its
// fresh/shared/canonical-order contract; it no longer selects or compares a Legacy source.
const CPK8G6G1_RETIRED_LEGACY_READER_TESTS: &[(&str, &str)] = &[(
    "rcpf_c2_factored_oracle_skips_a_quarantined_shadow",
    "Category B: the test selected the removed Legacy evaluator after corrupting/quarantining the RCPF shadow; CPK publication and typed attempt-terminal failure tests now own the product contract",
)];

const CPK8G6G1_REMOVED_LEGACY_READER_SURFACES: &[&str] = &[
    "ReplayEvaluatorSource",
    "try_legacy_lower_projection",
    "try_legacy_lower_projection_delta",
    "try_legacy_qualified_lower_projection",
    "try_legacy_record_lower_projection",
    "try_compare_factored_record_lower_projection",
    "try_factored_lower_projection_mutation_oracle",
    "observe_factored_lower_projection",
    "observe_factored_upper_materialization",
    "observe_factored_replay_event_boundary",
    "try_compare_factored_replay_event_boundary",
    "try_compare_factored_claimed_attribution_union",
    "try_compare_first_qualified_parent_sources",
    "enable_replay_factored_event_oracle",
    "enable_replay_factored_evaluator_oracle",
    "legacy_replay_parent_oracle",
    "factored_replay_parent_oracle",
    "legacy_replay_clause_link_oracle",
    "factored_replay_clause_link_oracle",
    "assert_factored_replay_clause_projection_matches_legacy",
    "try_evaluate_scheme_projection_mutation",
];

// CPK-8G-6g2 removes the final authority-selection surface. The RCPF stores remain live; their
// former authority gate is now only the sticky quarantine status, so normal writes are always fed.
const CPK8G6G2_REMOVED_REPLAY_AUTHORITY_SURFACES: &[&str] = &[
    "ReplayReadAuthority",
    "LegacyRollback",
    "replay_read_authority",
    "new_with_replay_read_authority",
    "new_with_imported_boundary_and_replay_read_authority",
    "try_collect_legacy_premise_dependency_chain",
    "try_collect_legacy_claim_parent_dependency_chain",
    "register_replay_claim_parents(",
    "apply_bound_replay_actions(",
    "apply_prefiltered_replay_provenance(",
];

// CPK-8E's projection-reader closure. These tests no longer derive expected values from
// legacy_scheme_projectable_lowers_for_test: they freeze project_lower decisions and then exercise
// the production CPK compact, alias, generalized-witness, and routing consumers directly.
const CPK8E_SCHEME_PROJECTION_READER_MIGRATIONS: &[&str] = &[
    "cpk_original_standalone_writer_publishes_mixed_projection_contract",
    "cpk_gap_1_mixed_claim_fixture_matches_all_four_cpk_consumers_exactly",
    "cpk_gap_1_replay_conjunction_matches_all_four_cpk_consumers",
    "cpk_gap_1_unclaimed_standalone_derived_and_incomplete_match_cpk_consumers",
    "cpk_gap_1_five_lineages_project_through_the_real_formula_graph",
    "cpk_gap_1_included_empty_keeps_generalized_witness_parentless",
    "cpk_gap_1_same_root_representative_replacement_matches_all_consumers",
    "cpk_gap_1_same_root_permutations_preserve_canonical_payload_shape",
];

// Historical CPK-8E closure sets. CPK-8G-6 retired every category-B member and removed both
// authority/Legacy-reader surfaces; these empty sets remain as mechanical proof that none of those
// reviewed dependents silently returned.
const CPK8E_ROUTING_COUNT_PARITY_HOLDOUTS: &[&str] = &[];

const CPK8E_PERMANENT_FAULT_INJECTION_DEPENDENTS: &[&str] = &[];

const CPK8E_REPLACEMENT_BACKED_LEGACY_FIXTURES: &[&str] = &[];

const CPK8E_PHYSICAL_REMOVAL_DEFERRED_FIXTURES: &[&str] = &[];

const CPK8E_MIGRATION_ORACLE_DEPENDENT_TOTAL: usize = 0;

// CPK-8G physical-removal manifest after the 8G-6 closure. The 60 category-B dependents are retired
// and the 14 category-A contracts are independently pinned above. What remains here is only the
// direct RCPF structure/integration coverage deferred to 8G-9/10 and the shell/telemetry coverage
// deferred beyond it. A test is listed exactly once and carries every physical target it protects;
// this prevents a multi-target test from hiding one dependency behind a duplicate name.
//
// The target names follow the deletion phase in the approved CPK-8G plan: authority/oracle
// retirement (8G-6), flat parent/projection layers (8G-7/8), RCPF leaf-to-root removal (8G-9/10),
// flat claim removal (8G-11), and final shell/telemetry cleanup (8G-12).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Cpk8gPhysicalTarget {
    ParentSetArena,
    ReplayOccurrenceStore,
    ReplayResultSummary,
    ReplayFactoredShellAndTelemetry,
}

struct Cpk8gPhysicalTestGroup {
    targets: &'static [Cpk8gPhysicalTarget],
    tests: &'static [&'static str],
}

const CPK8G_ADDITIONAL_EXPLICIT_LEGACY_AUTHORITY_TESTS: &[&str] = &[];

// CPK-8G-6a closes the reader census beyond the original 54 explicit-authority/oracle
// dependents. These six tests reach the flat projection reader through the RCPF event oracle or
// its direct comparison adapters without selecting Legacy authority themselves. They are still
// category B: CPK-owned target-late, canonical projection, first-source, and publication tests
// now pin the product contracts that survive their 8G-6 retirement.
const CPK8G6_IMPLICIT_LEGACY_READER_DEPENDENTS: &[&str] = &[];

// Category A contracts that survive 8G-6. Ten D3b tests retain canonical storage, target-late,
// generalized-witness, diagnostic-role, portable-prefix, and query-budget assertions on CPK-only
// fixtures. Two CPK mirrored-fixture contracts and two direct authority-identity tests likewise
// keep their substantive CPK behavior while shedding only constructor/identity plumbing.
const CPK8G6_CPK_ONLY_CORRECTNESS_CONTRACTS: &[&str] = &[
    "target_late_mixed_roots_do_not_expose_historical_order_to_later_replay",
    "canonical_projection_storage_is_invariant_across_all_four_event_permutations",
    "same_root_replacement_preserves_raw_and_canonical_positions",
    "canonical_qualified_and_generalized_parent_sequences_are_invariant_across_all_permutations",
    "canonical_insertion_census_pins_lengths_and_entry_moves",
    "canonical_generalized_witness_prefix_and_completeness_survive_sampled_large_orders",
    "canonical_portable_export_and_explanation_sequences_are_invariant_across_all_permutations",
    "canonical_diagnostic_roles_remain_ordered_when_distinct_causes_share_a_location",
    "canonical_export_budget_truncation_is_invariant_and_a_full_snapshot_prefix",
    "canonical_portable_query_budget_causes_are_invariant_full_result_prefixes",
    "cpk_0b_captures_canonical_logical_proof_surfaces_end_to_end",
    "cpk_0c_fixture_matrix_captures_semantic_and_logical_baselines",
    "cpk_7_cpk_authority_preflight_rejects_claim_index_corruption",
    "rcpf_c3a_loaded_files_driver_finishes_without_terminal_failure",
];

const CPK8G6_HISTORICAL_LEGACY_CHARACTERIZATION_TOTAL: usize = 0;
const CPK8G6_CPK_ONLY_CORRECTNESS_CONTRACT_TOTAL: usize = 14;
const CPK8G9_10_DEFERRED_RCPF_STRUCTURE_TEST_TOTAL: usize = 11;

const CPK8G_PHYSICAL_REMOVAL_TEST_GROUPS: &[Cpk8gPhysicalTestGroup] = &[
    Cpk8gPhysicalTestGroup {
        targets: &[Cpk8gPhysicalTarget::ParentSetArena],
        tests: &[
            "virtual_empty_arena_has_zero_allocation_and_stays_virtual_on_empty_extend",
            "extends_an_empty_arena_in_canonical_order",
            "repeated_extension_of_the_same_roots_preserves_existing_winners",
            "entry_permutations_intern_and_iterate_as_the_same_logical_map",
            "representative_claim_is_first_wins_before_delta_canonicalization",
            "invalid_ids_and_claims_return_errors",
            "reservation_failure_returns_error_without_committing_storage",
        ],
    },
    Cpk8gPhysicalTestGroup {
        targets: &[Cpk8gPhysicalTarget::ReplayResultSummary],
        tests: &[
            "result_summary_indexes_single_and_multiple_roots_without_empty_storage",
            "result_root_reservation_failure_rejects_both_summary_indices",
            "qualified_parent_source_store_is_first_wins_fallible_and_validated",
        ],
    },
    Cpk8gPhysicalTestGroup {
        targets: &[
            Cpk8gPhysicalTarget::ReplayOccurrenceStore,
            Cpk8gPhysicalTarget::ReplayResultSummary,
        ],
        tests: &[
            "rcpf_c2_factored_evaluator_matches_fresh_shared_and_insertion_order_queries",
        ],
    },
    Cpk8gPhysicalTestGroup {
        targets: &[Cpk8gPhysicalTarget::ReplayFactoredShellAndTelemetry],
        tests: &[
            "rcpf_c3a_normal_attempt_runs_once_without_authority_dispatch",
            "rcpf_c3a_failed_attempt_is_discarded_as_typed_hard_error",
            "rcpf_c3a_failure_is_a_typed_hard_error_without_retry",
            "rcpf_c3a_loaded_files_driver_finishes_without_terminal_failure",
        ],
    },
];

const CPK8G7_COMPLETED_SUBSLICES: &[&str] =
    &["8G-7a", "8G-7b1", "8G-7b2", "8G-7b3", "8G-7b4"];
const CPK8G8A_COMPLETED_SUBSLICES: &[&str] = &["8G-8a0", "8G-8a1", "8G-8a2"];
const CPK8G8B_COMPLETED_SUBSLICES: &[&str] = &["8G-8b0", "8G-8b1"];

// Rollback readiness across the CPK-8G deployed-state boundary:
// - f561c8d9 remains the historical fully-Legacy-capable baseline from before physical-removal
//   work. c1c3352e (CPK-8G-5, "freeze final CPK dual-write proof baseline") is the operative last
//   fully dual-write-capable green point and the rollback target once CPK-8G-6 crosses the
//   code-level irreversibility boundary. Preserve that hash with the last-known-good binary and
//   its Cargo.lock/rustc metadata.
// - Reproduce the operative point in an isolated worktree. Build the binary with
//   `RUSTC_WRAPPER= cargo build -p yulang`, check with `RUSTC_WRAPPER= cargo check -p infer`, then
//   run `cpk_`/`rcpf_`/`dpn_`/`mpc_`, the scoped `constraints::` suite with its reviewed skip list,
//   `generalize::`/`compact::`/`explain::`/`portable_explain::`, and the logical-proof snapshot
//   characterization, always with `--test-threads=4` for tests.
// - CPK-8G-7b1 is the first commit that stops a production flat writer. From that commit onward,
//   rollback means deploying the archived c1c3352e binary, not reverting source and restarting a
//   newly built process. Discard every in-flight ConstraintMachine and cross a cold process
//   boundary; no state built after the writer removal can be transferred into the archived binary.
//   Start it with a version-scoped or empty cache root, never a cache concurrently writable by the
//   CPK-8G-7 binary and the archived binary.
// - ConstraintMachine, TypeBounds, and all RCPF stores are process-local inference state. Neither
//   the poly cache nor the compiled-source-unit envelopes serialize them: persisted artifacts hold
//   post-inference poly/compiled syntax, namespace, lowering, typed, and runtime surfaces.
// - The cache already gates compiled artifacts with CACHE_SCHEMA_VERSION and
//   COMPILED_UNIT_CACHE_FORMAT. CPK-8G changes no serialized surface, so it needs no cache-format
//   bump. Those keys do not include the compiler commit, however: rollout and rollback must use a
//   version-scoped cache root (or an empty cache), never a concurrently writable mixed-version
//   cache. Both directions require a cold process boundary. No in-process ConstraintMachine state
//   is transferable between the CPK-only and last-known-good binaries.

const REVIEWED_SOURCES: &[(&str, &str)] = &[
    (
        "constraints/directed_weight.rs",
        include_str!("directed_weight.rs"),
    ),
    ("constraints/mod.rs", include_str!("mod.rs")),
    (
        "constraints/machine/bounds.rs",
        include_str!("machine/bounds.rs"),
    ),
    (
        "constraints/machine/entry.rs",
        include_str!("machine/entry.rs"),
    ),
    (
        "constraints/machine/mod.rs",
        include_str!("machine/mod.rs"),
    ),
    (
        "constraints/machine/propagate.rs",
        include_str!("machine/propagate.rs"),
    ),
    ("constraints/mutation.rs", include_str!("mutation.rs")),
    (
        "constraints/ocast_eligibility.rs",
        include_str!("ocast_eligibility.rs"),
    ),
    (
        "constraints/portable_explain.rs",
        include_str!("portable_explain.rs"),
    ),
    ("constraints/proof/mod.rs", include_str!("proof/mod.rs")),
    (
        "constraints/replay_factored.rs",
        include_str!("replay_factored.rs"),
    ),
    ("constraints/replay_soak.rs", include_str!("replay_soak.rs")),
    ("constraints/row_effect.rs", include_str!("row_effect.rs")),
    ("constraints/timing.rs", include_str!("timing.rs")),
    ("constraints/trace.rs", include_str!("trace.rs")),
    ("constraints/explain.rs", include_str!("explain.rs")),
];

// Counts are regenerated only after every changed reference has been reviewed against addendum §2.
// CPK-8E-5 removes only the reviewed references owned by the six retired Legacy tests and their
// dedicated carrier-order helper; the lower counts below do not remove a production authority.
const PROOF_STATE_REFERENCE_CENSUS: &[(&str, usize)] = &[
    // CPK-8B adds two test-only reads that deliberately corrupt the Legacy mirror and prove
    // reduction-route exact dedup remains owned by the CPK index.
    // CPK-8G-3 adds the reviewed flat-mirror transaction and its atomicity assertion; CPK owns
    // exact admission while these references only feed or verify the migration mirror. CPK-8G-5
    // adds one test-only mirror reset (through the non-replay field name) proving the logical
    // snapshot is independent of every former flat/RCPF read. CPK-8G-6c removes the reviewed
    // flat/CDM parent-relation characterizations and their dedicated bulk-oracle helpers after
    // their CPK replacements land.
    // CPK-8G-6d removes the RCPF parent/occurrence comparison fixtures' flat-ledger reads.
    // The dedicated first-witness/non-replay comparator helpers disappear with their callers.
    // CPK-8G-6e removes the final publication/failure ordering and Legacy-reader assertions.
    // CPK-8G-6g1 removes the flat side of the event/projection comparison adapter.
    // CPK-8G-6g2 removes the final authority-selected Legacy premise-chain reader and the unused
    // flat-parent argument from the now-unconditional Factored phase-B plan. CPK-8G-7a moves the
    // remaining production and test readers to the result-local CPK view; the surviving references
    // are the flat mirror definition, capacity preflight, and commit path (plus the separately
    // counted non-replay RCPF store whose name contains this token).
    // CPK-8G-7b4 removes the final flat parent Vec and its complete capacity/commit writer. The
    // surviving references are the separately counted RCPF NonReplayClaimParentStore field only.
    ("claim_parents_by_constraint", 6),
    // The final dead shadow-interference comparator disappears with the 8G-6c ledger helpers.
    // CPK-8G-7b1 removes this first flat parent-relation mirror and its writer completely.
    ("replay_claim_parent_keys", 0),
    // CPK-8G-7b3 removes the carrier projection from the shared parent mirror writer.
    ("qualified_carrier_index", 0),
    // CPK-8G-7b2 removes the independent structural exact-key mirror and its writer completely.
    ("structural_claim_parent_keys", 0),
    // CPK-8G-2b/2c add reviewed transaction-preflight and atomicity-test references; the flat
    // projection collection remains a mirror during these ownership-transfer slices. CPK-8G-6a
    // removes five D3b A-fixture reads now served by the CPK claim/support indexes. CPK-8G-6c
    // removes the historical flat materialization/projection reads and their oracle snapshots.
    // CPK-8G-6d removes two parent-failure ordering fixture reads.
    // CPK-8G-8a0 moves every reader to CPK, 8G-8a1 makes the flat bundle a one-way mirror, and
    // CPK-8G-8a2 removes the mirror field and writer completely.
    ("scheme_projection_claims_by_lower_record", 0),
    // CPK-4 adds reviewed test-only reads for the writer-boundary snapshot and
    // mutation-oracle readiness, plus one fixture-only empty-ledger seed. CPK-5
    // adds one routing-shadow capture-readiness read. Slice B adds one reviewed test-only
    // empty-ledger seed. CPK-8B removes the sole production-store projection writer re-read by
    // carrying its support snapshot in the admission event. CPK-8G-4b retires two RCPF-only
    // dangling-occurrence fixtures and their raw flat projection-ledger seeds.
    // CPK-8G-5 adds one test-only mirror reset for the CPK-only snapshot freeze. CPK-8G-6a
    // removes six D3b A-fixture reads/writes now served by the canonical CPK support view.
    // CPK-8G-6c removes historical flat bulk/delta oracle reads and snapshots.
    // CPK-8G-6f removes four Legacy projectability/publication shadow reads.
    // CPK-8G-6g1 removes the remaining lower-projection comparison reads; CPK-8G-8a0 moves the
    // evaluator, semantic consumers, fixtures, and assertions to CPK; CPK-8G-8a2 removes the
    // final mirror storage and its writer.
    ("projection_proofs_by_lower_record", 0),
    // CPK-8G-8a0 adds the CPK root-to-lower reverse membership and removes the last flat readers;
    // CPK-8G-8a2 removes all three reverse-membership/owner mirror fields.
    ("scheme_projection_lower_records_by_root", 0),
    ("scheme_projection_lower_record_memberships", 0),
    ("scheme_projection_claimed_lower_owners", 0),
    // CPK-8G-8b0 transfers exact typed clause admission to CPK and removes RCPF's numeric flat-ID
    // lookups. CPK-8G-8b1 removes the complete seven-field flat clause/link/attribution mirror.
    ("record_proof_clauses", 0),
    ("record_proof_clause_by_key", 0),
    ("record_proof_clause_ids_by_lower_record", 0),
    ("record_proof_clause_links_by_lower_record", 0),
    ("record_proof_clause_link_keys", 0),
    // The remaining six lexical matches are ReplayClauseProjection's deliberately retained
    // replay_attributed_claim_supports field and its direct RCPF structure tests, not the removed
    // TypeBounds attribution mirror.
    ("attributed_claim_supports", 6),
    ("flat_retained_attributed_claim_supports", 0),
    // CPK-8E's CPK-only dependency-chain contract reads the index directly to verify its
    // replay-endpoint closure; this is a reviewed test assertion, not a production authority.
    // CPK-8G-4a adds the reviewed CPK-owned reverse index, its atomicity/target-late contract
    // test, and the flat one-way mirror preflight/commit. Evaluator reads remain flat until 4b.
    // CPK-8G-5 adds the CPK-owned snapshot iterator and resets the flat dependency mirror once in
    // the snapshot-independence test; neither reference restores flat read authority.
    // CPK-8G-6b removes the replacement-backed Legacy dependency-chain mirror read.
    // CPK-8G-6d removes one downstream RCPF first-source failure assertion.
    // CPK-8G-6g1 removes the Legacy dependency-edge comparison read.
    ("dependent_records_by_premise", 23),
    // Fixture hygiene uses the reviewed root-admission API instead of four raw field writes;
    // CPK-8E removes the final migration-only Legacy normalizer read.
    ("origins", 128),
    ("source_boundaries", 7),
    // Fixture hygiene removes two raw synthetic ConstraintRecord field initializers and two
    // direct row-attachment writes in favor of the reviewed mirrored admission API. The CPK-7
    // endpoint correction adds one test-only semantic row-provenance merge assertion.
    // CPK-owned reduction-route dedup resolves its exact semantic carrier once; CPK-8E removes
    // the two remaining migration-only Legacy normalizer reads.
    // CPK-8G-6c removes two historical reduction/structural carrier assertions.
    // CPK-8G-6d removes structural/reduction RCPF comparison fixtures.
    ("row_derivations", 42),
    ("generalized_schemes", 9),
    // Slice B's test-only four-consumer oracle and Included(empty) regression invoke the
    // reviewed generalized-witness reader. Neither adds a production proof-state consumer.
    ("generalized_witnesses", 13),
    // CPK-6a adds one reviewed production-store scheme-instantiation writer read. CPK-8E removes
    // both the thread-local writer hook and the final Legacy normalizer read.
    ("scheme_instantiations", 16),
    // CPK-3 adds reviewed test-only claim hooks and lineage parity reads; CPK-4 adds
    // shadow-evaluator and capture-readiness reads; CPK-5 adds routing readiness.
    // CPK-6a adds five reviewed production-store upper-claim writer reads and
    // three fixture-only mirrors for low-level TypeBounds claim construction. Fixture hygiene
    // adds four reviewed test-only reads while switching those fixtures to mirrored admission.
    // CPK-7 Slice A adds two reviewed test-only reads for index write/move atomicity fixtures;
    // Slice B adds one reviewed routing fault-fixture read. Slice C adds one test-only Legacy
    // normalization read for exact prepared-parent parity. The endpoint-decoupling correction
    // adds two test-only claim-move assertions. Slice C item 2 adds one test-only read proving
    // two uncovered roots share one physical upper record. Item 16 adds one test-only outer-
    // census assertion before corrupting the CPK claim index; none is a production authority.
    // CPK-8B freezes original/derived claim admission in UpperReplayClaimRegistration. Original
    // admission removes two production CPK-writer re-reads and adds one reviewed transaction-local
    // snapshot read plus one test-only mutation proving that the event cannot observe later flat
    // state. Derived admission then removes the two remaining production CPK-writer re-reads.
    // Claim move freezes claim/current-record at flat-mutation completion, replacing its only
    // production CPK-writer re-read with one transaction-local snapshot read; the strengthened
    // atomicity fixture mutates the flat claim afterward to prove the event is closed. The total
    // lexical count therefore stays unchanged. CPK-8E adds one reviewed CPK-only routing-contract
    // read to reconstruct a moved claim's exact current-record key. None is a new production read
    // authority. CPK-8E removes three migration-only thread-local writer-hook reads and the
    // final three Legacy normalizer reads. CPK-8G-2a adds two reviewed test-only reads that
    // compare the complete CPK claim payload with the flat allocation and post-move snapshots;
    // allocation and production read authority remain unchanged in this slice.
    // CPK-8G-2b adds the flat mirror preflight/commit and atomicity assertions while removing
    // the old flat-issued-ID constructor path.
    // CPK-8G-2d adds reviewed flat-mirror validation and atomicity snapshots around the CPK-owned
    // current-record move transaction; these reads do not restore flat allocation authority.
    // CPK-8G-3 removes two authority reads formerly used by replay/structural exact-key writers;
    // the CPK prepared payload now supplies those roots to the flat mirror.
    // CPK-8G-5 resets the flat claim mirror once in the snapshot-independence test. CPK-8G-6a
    // removes four D3b A-fixture claim reads now served by ProofOccurrenceStore. CPK-8G-6b
    // removes two migration-only outer-census reads with the routing-oracle fault fixture.
    // CPK-8G-6c removes five historical flat claim/lineage assertions.
    // CPK-8G-6d removes the final test-only Legacy first-witness lineage lookup helper.
    // CPK-8G-6f removes six flat-claim reads from the Proof Legacy reader/planner/shadow path.
    // CPK-8G-6g1 removes flat event-oracle claim/root reconstruction reads. CPK-8G-8a0 removes
    // three support/root readers that formerly resolved producer/root through the flat claim Vec.
    // 8G-8a1 removes the flat support decision path's five claim/root lookups; 8G-8a2 removes the
    // final lookup from the deleted support/root mirror commit.
    ("upper_replay_claims", 68),
    // CPK-7 Slice A adds nine reviewed references for the approved production CPK index and its
    // atomicity/no-global-scan tests. Slice B adds the reviewed query read and fault injection.
    // CPK-8G-1 adds one reviewed CPK-only allocation-census read proving the no-claim writer
    // leaves the record index's length and capacity untouched.
    // CPK-8G-2b adds both CPK-owned and flat-mirror transaction preflight/atomicity references.
    // CPK-8G-2d adds the CPK-owned move preflight/commit, flat-mirror commit, and direct
    // multi-move/atomicity assertions. The flat index is now observed only as a transition mirror.
    // CPK-8G-6c removes one historical flat materialization-census read.
    ("claims_by_upper_record", 62),
    // CPK-8E removes the final migration-only live-coverage normalizer read. CPK-8G-2d adds the
    // fallible flat-mirror preflight/commit and direct root-liveness assertions after repeated move.
    // CPK-8G-6f removes the Legacy projectability reader's flat coverage lookup.
    ("live_coverage_by_root", 13),
    // CPK-8E removes the final migration-only parent-set normalizer read.
    // CPK-8G-5 resets each former RCPF snapshot source once in its CPK-only freeze test.
    // CPK-8G-6d removes parent-admission failure and probe characterizations.
    // CPK-8G-6g1 removes only comparison-oracle reads; the direct arena API remains.
    // CPK-8G-6g2 adds one test-only physical-census read for writer-continuity verification.
    // CPK-8G-8b0 removes the last authority preflight that consulted RCPF parent sets.
    ("replay_parent_sets", 10),
    // CPK-8E removes the final three migration-only finite-map normalizer reads. CPK-8G-4b
    // retires the three RCPF-only dangling-occurrence publication fault injections. CPK-8G-6b
    // removes the replacement-backed evidence/trivial occurrence-arena assertion.
    // CPK-8G-6d removes RCPF occurrence facade/census comparisons.
    // CPK-8G-6g1 removes Legacy-parity reconstruction and event-boundary reads.
    // CPK-8G-6g2 adds one test-only physical-census read for writer-continuity verification.
    // CPK-8G-8b0 removes the RCPF occurrence-based exact-link authority preflight.
    ("replay_occurrences", 16),
    // CPK-8E removes the final migration-only first-witness normalizer read.
    // CPK-8G-5 adds one parity read for the new CPK first-source index plus the snapshot test's
    // RCPF reset; both are test-only checks at the final dual-write freeze.
    // CPK-8G-6c removes one historical factored projection assertion.
    // CPK-8G-6d removes RCPF first-source/first-witness comparison reads.
    // CPK-8G-6g1 removes event/evaluator oracle activation and comparison reads.
    // CPK-8G-6g2 adds one test-only physical-census read for writer-continuity verification.
    ("replay_result_summary", 13),
    // CPK-8G-6b removes four reads from the two replacement-backed clause-projection fixtures.
    // CPK-8G-6g1 removes flat-vs-RCPF attribution and exact-link reconstruction reads.
    // CPK-8G-6g2 adds one test-only physical-census read for writer-continuity verification.
    // CPK-8G-8b0 removes RCPF from admission dedup and the test evaluator's attribution union.
    ("replay_clause_projection", 6),
    // CPK-8G-6g2 likewise pins non-replay parent population after removing the authority gate.
    ("non_replay_claim_parents_by_constraint", 6),
];

const REVIEWED_BOUNDARIES: &[(&str, &str)] = &[
    // Source boundary and constraint derivation.
    ("constraints/machine/entry.rs", "alloc_source_boundary"),
    (
        "constraints/machine/entry.rs",
        "record_source_boundary_location",
    ),
    ("constraints/machine/entry.rs", "record_root_origin"),
    (
        "constraints/machine/entry.rs",
        "attach_root_origin_to_existing_subtype",
    ),
    (
        "constraints/machine/entry.rs",
        "enqueue_canonical_subtype_with_origin",
    ),
    ("constraints/machine/entry.rs", "enqueue_replay_subtype"),
    ("constraints/machine/entry.rs", "merge_replay_derivation"),
    (
        "constraints/machine/entry.rs",
        "merge_structural_derivation",
    ),
    (
        "constraints/machine/entry.rs",
        "merge_constraint_canonicalization_disposition",
    ),
    (
        "constraints/machine/entry.rs",
        "merge_scheme_instantiation_routes",
    ),
    (
        "constraints/machine/entry.rs",
        "enqueue_row_derived_subtype",
    ),
    // Bounds, row/subtract, and generalized provenance.
    ("constraints/machine/bounds.rs", "record_bound_provenance"),
    ("constraints/machine/bounds.rs", "record_bound_disposition"),
    (
        "constraints/machine/bounds.rs",
        "record_pruned_bound_dispositions",
    ),
    (
        "constraints/machine/bounds.rs",
        "merge_scheme_instantiations_into_lower_bound",
    ),
    ("constraints/mod.rs", "add_lower"),
    ("constraints/mod.rs", "add_upper"),
    ("constraints/machine/entry.rs", "intern_row_derivation"),
    ("constraints/machine/entry.rs", "record_subtract_fact"),
    ("constraints/row_effect.rs", "row_derivation_parents"),
    (
        "constraints/machine/bounds.rs",
        "record_lower_filter_provenance",
    ),
    (
        "constraints/row_effect.rs",
        "register_unweighted_row_reduction",
    ),
    (
        "constraints/row_effect.rs",
        "merge_unweighted_row_reduction_derivation",
    ),
    (
        "constraints/machine/entry.rs",
        "alloc_generalized_scheme_record",
    ),
    (
        "constraints/machine/entry.rs",
        "intern_scheme_instantiation",
    ),
    (
        "constraints/machine/entry.rs",
        "record_scheme_instantiation_use",
    ),
    // Upper claims and claim-parent relations.
    ("constraints/mod.rs", "original_upper_replay_claim"),
    ("constraints/mod.rs", "derived_upper_replay_claim"),
    ("constraints/mod.rs", "insert_upper_record_claim_canonical"),
    ("constraints/mod.rs", "move_upper_replay_claim"),
    (
        "constraints/mod.rs",
        "insert_scheme_projection_live_coverage_state",
    ),
    (
        "constraints/mod.rs",
        "remove_scheme_projection_live_coverage_state",
    ),
    (
        "constraints/machine/bounds.rs",
        "commit_claim_qualified_parent_mutation",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_replay_claim_parents_with_factored_drafts",
    ),
    (
        "constraints/machine/entry.rs",
        "merge_structural_claim_parents",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_reduction_route_claim_parent",
    ),
    ("constraints/replay_factored.rs", "preflight_extend"),
    ("constraints/replay_factored.rs", "commit_extend"),
    ("constraints/replay_factored.rs", "try_insert"),
    ("constraints/replay_factored.rs", "update_parent_versions"),
    ("constraints/replay_factored.rs", "try_record_admission"),
    ("constraints/replay_factored.rs", "try_admit"),
    // Projection, clauses, attribution, and dependencies.
    (
        "constraints/machine/bounds.rs",
        "register_constraint_upper_replay_claims",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_lower_projection_derivation",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_existing_constraint_lower_projection_delta",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_lower_projection_delta",
    ),
    (
        "constraints/machine/bounds.rs",
        "projection_carrier_is_independent",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_premise_dependency_chain",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_new_constraint_premise_route_edges",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_record_proof_clause_link",
    ),
    (
        "constraints/machine/bounds.rs",
        "commit_record_proof_clause_link_batch_mutation",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_replay_evidence_clause_link",
    ),
    (
        "constraints/machine/bounds.rs",
        "try_admit_projection_index",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_claim_parent_dependency_chain",
    ),
    ("constraints/mod.rs", "support_has_clause_link"),
    (
        "constraints/replay_factored.rs",
        "try_project_replay_parents",
    ),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClaimedRootPlan {
    None,
    Delta(usize),
    FullBootstrap(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IndependentSupportPlan {
    None,
    EventCarrier,
    ProducerFullScan,
    RecordFullBootstrap,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ProjectionAdmissionPlan {
    claimed_roots: ClaimedRootPlan,
    independent_supports: IndependentSupportPlan,
}

#[derive(Debug, Clone, Copy)]
struct ProjectionAdmissionInput {
    lower_exists: bool,
    qualified_parent_batch_inserted: bool,
    had_qualified_parent_before: bool,
    projection_ledger_existed_before: bool,
    all_claimed_roots_after_event: usize,
    new_claimed_roots: usize,
    event_carrier_present: bool,
}

fn projection_admission_plan(input: ProjectionAdmissionInput) -> ProjectionAdmissionPlan {
    if !input.lower_exists {
        return ProjectionAdmissionPlan {
            claimed_roots: ClaimedRootPlan::None,
            independent_supports: IndependentSupportPlan::None,
        };
    }
    if !input.projection_ledger_existed_before {
        return if input.all_claimed_roots_after_event == 0 {
            ProjectionAdmissionPlan {
                claimed_roots: ClaimedRootPlan::None,
                independent_supports: IndependentSupportPlan::None,
            }
        } else {
            ProjectionAdmissionPlan {
                claimed_roots: ClaimedRootPlan::FullBootstrap(input.all_claimed_roots_after_event),
                independent_supports: IndependentSupportPlan::RecordFullBootstrap,
            }
        };
    }
    let exact_noop = !input.qualified_parent_batch_inserted
        && input.new_claimed_roots == 0
        && !input.event_carrier_present;
    if exact_noop {
        return ProjectionAdmissionPlan {
            claimed_roots: ClaimedRootPlan::None,
            independent_supports: IndependentSupportPlan::None,
        };
    }
    let claimed_roots = if input.new_claimed_roots == 0 {
        ClaimedRootPlan::None
    } else {
        ClaimedRootPlan::Delta(input.new_claimed_roots)
    };
    let independent_supports =
        if input.qualified_parent_batch_inserted && !input.had_qualified_parent_before {
            IndependentSupportPlan::ProducerFullScan
        } else if input.event_carrier_present {
            IndependentSupportPlan::EventCarrier
        } else {
            IndependentSupportPlan::None
        };
    ProjectionAdmissionPlan {
        claimed_roots,
        independent_supports,
    }
}

#[test]
fn cpk_0c_proof_state_reference_census_matches_reviewed_inventory() {
    let joined = REVIEWED_SOURCES
        .iter()
        .map(|(_, source)| *source)
        .collect::<Vec<_>>()
        .join("\n");
    for &(name, expected) in PROOF_STATE_REFERENCE_CENSUS {
        assert_eq!(
            joined.matches(name).count(),
            expected,
            "proof-state reference census changed for {name}; classify every changed site against CPK-0 addendum section 2 before updating this count"
        );
    }
    for &(file, boundary) in REVIEWED_BOUNDARIES {
        let source = REVIEWED_SOURCES
            .iter()
            .find_map(|(candidate, source)| (*candidate == file).then_some(*source))
            .unwrap_or_else(|| panic!("reviewed source missing: {file}"));
        assert!(
            source.contains(&format!("fn {boundary}")),
            "reviewed proof boundary moved or disappeared: {file}::{boundary}; reclassify the inventory instead of silently dropping it"
        );
    }
}

#[test]
fn cpk_8g_7_flat_parent_relations_are_fully_removed() {
    let source = |file| {
        REVIEWED_SOURCES
            .iter()
            .find_map(|(candidate, source)| (*candidate == file).then_some(*source))
            .unwrap_or_else(|| panic!("reviewed source missing: {file}"))
    };
    for file in [
        "constraints/machine/bounds.rs",
        "constraints/machine/entry.rs",
        "constraints/proof/mod.rs",
    ] {
        let source = source(file);
        for field in [
            ".claim_parents_by_constraint",
            ".qualified_carrier_index",
            ".replay_claim_parent_keys",
            ".structural_claim_parent_keys",
        ] {
            assert!(
                !source.contains(field),
                "CPK-8G-7a forbids flat parent-relation reads outside the TypeBounds mirror writer: {file} contains {field}"
            );
        }
    }
    for field in [
        ".claim_parents_by_constraint",
        ".qualified_carrier_index",
        ".replay_claim_parent_keys",
        ".structural_claim_parent_keys",
    ] {
        assert!(
            !include_str!("tests/case_02.rs").contains(field),
            "CPK-8G-7a forbids flat parent-relation reads in constraints/tests/case_02.rs: {field}"
        );
    }

    let bounds = source("constraints/mod.rs");
    assert!(
        !bounds.contains("ReplayClaimParentKey"),
        "CPK-8G-7b1 removed replay exact-key mirror type reappeared"
    );
    assert!(
        !bounds.contains("StructuralClaimParentKey"),
        "CPK-8G-7b2 removed structural exact-key mirror type reappeared"
    );
    assert!(
        !bounds.contains("QualifiedCarrier"),
        "CPK-8G-7b3 removed qualified-carrier mirror type reappeared"
    );
    assert!(
        !bounds.contains("\n    claim_parents_by_constraint:"),
        "CPK-8G-7b4 removed flat parent Vec field reappeared"
    );
    for removed_writer in [
        "PreparedQualifiedParentMirrorCapacity",
        "fn push_claim_qualified_parent",
        "fn try_reserve_qualified_parent_mirror",
        "fn begin_qualified_parent_mirror_commit",
        "fn commit_qualified_parent_mirror_entry",
    ] {
        assert!(
            !bounds.contains(removed_writer),
            "CPK-8G-7b4 removed flat parent mirror writer reappeared: {removed_writer}"
        );
    }
    for (field, expected) in [
        // The one surviving substring is the distinct RCPF `non_replay_*` machine field.
        ("claim_parents_by_constraint", 1),
        ("qualified_carrier_index", 0),
        ("replay_claim_parent_keys", 0),
        ("structural_claim_parent_keys", 0),
    ] {
        assert_eq!(
            bounds.matches(field).count(),
            expected,
            "flat parent relation {field} gained a reader or lost a reviewed mirror-writer site"
        );
    }
    assert_eq!(
        CPK8G7_COMPLETED_SUBSLICES,
        &["8G-7a", "8G-7b1", "8G-7b2", "8G-7b3", "8G-7b4"],
        "CPK-8G-7 closure must retain all five reviewed sub-slice dispositions"
    );
}

#[test]
fn cpk_8g_8a2_flat_support_root_relations_are_fully_removed() {
    let reviewed_sources = [
        include_str!("mod.rs"),
        include_str!("machine/bounds.rs"),
        include_str!("proof/mod.rs"),
        include_str!("semantic_execution_snapshot.rs"),
        include_str!("tests/case_02.rs"),
    ]
    .join("\n");
    for field in [
        "scheme_projection_claims_by_lower_record",
        "projection_proofs_by_lower_record",
        "scheme_projection_lower_records_by_root",
        "scheme_projection_lower_record_memberships",
        "scheme_projection_claimed_lower_owners",
    ] {
        assert_eq!(
            reviewed_sources.matches(field).count(),
            0,
            "removed flat support/root relation reappeared: {field}",
        );
    }
    assert_eq!(
        CPK8G8A_COMPLETED_SUBSLICES,
        &["8G-8a0", "8G-8a1", "8G-8a2"],
        "CPK-8G-8a closure must retain all three reviewed sub-slice dispositions",
    );
}

#[test]
fn cpk_8g_8b1_flat_clause_link_attribution_relations_are_fully_removed() {
    let reviewed_sources = REVIEWED_SOURCES
        .iter()
        .map(|(_, source)| *source)
        .collect::<Vec<_>>()
        .join("\n");
    for surface in [
        "record_proof_clauses",
        "record_proof_clause_by_key",
        "record_proof_clause_ids_by_lower_record",
        "record_proof_clause_links_by_lower_record",
        "record_proof_clause_link_keys",
        "flat_retained_attributed_claim_supports",
        "RecordProofClauseId",
        "RecordProofClauseRecord",
        "RecordProofClauseKey",
        "RecordProofClauseLinkKey",
    ] {
        assert_eq!(
            reviewed_sources.matches(surface).count(),
            0,
            "removed flat clause/link/attribution surface reappeared: {surface}",
        );
    }
    assert_eq!(
        reviewed_sources.matches("attributed_claim_supports").count(),
        reviewed_sources
            .matches("replay_attributed_claim_supports")
            .count(),
        "the generic flat attribution mirror must not reappear; only RCPF's scoped replay attribution store remains",
    );
    assert_eq!(
        CPK8G8B_COMPLETED_SUBSLICES,
        &["8G-8b0", "8G-8b1"],
        "CPK-8G-8b closure must retain both reviewed sub-slice dispositions",
    );
}

#[test]
fn cpk_8a_raw_fixture_writer_census_is_fully_classified() {
    let bounds_mutation_tests = include_str!("machine/bounds.rs")
        .split("mod mutation_tests {")
        .nth(1)
        .expect("bounds mutation test module");
    let raw_fixture_sources = [
        bounds_mutation_tests,
        include_str!("proof/mod.rs")
            .split("mod tests {")
            .nth(1)
            .expect("proof test module"),
        include_str!("tests/case_02.rs"),
        include_str!("tests/case_03.rs"),
        include_str!("tests/explain.rs"),
    ]
    .join("\n");
    let raw_writer_count = [
        ".bounds.add_lower(",
        ".bounds.add_upper(",
        ".bounds.original_upper_replay_claim(",
        ".bounds.derived_upper_replay_claim(",
        "row_derivations.push",
        "upper_replay_claims.push",
        "scheme_projection_claims_by_lower_record.insert",
        "scheme_projection_claims_by_lower_record.entry",
    ]
    .iter()
    .map(|pattern| raw_fixture_sources.matches(pattern).count())
    .sum::<usize>();
    let classified = CPK8_RAW_FIXTURE_WRITER_CLASSIFICATION
        .iter()
        .map(|(_, count)| *count)
        .sum::<usize>();
    assert_eq!(
        raw_writer_count, CPK8_RAW_FIXTURE_WRITER_TOTAL,
        "a raw fixture writer changed; classify it into CPK-8A bucket A/B/C/D before CPK-8B",
    );
    assert_eq!(
        classified, raw_writer_count,
        "every raw fixture writer must be classified before legacy removal advances",
    );
    assert!(
        CPK8_RAW_FIXTURE_WRITER_CLASSIFICATION
            .iter()
            .all(|(class, count)| {
                !matches!(class, Cpk8RawFixtureWriterClass::FixtureConstructionDebt) || *count == 0
            }),
        "CPK-8A cannot begin the soak with unremediated fixture-construction debt",
    );
    assert!(
        bounds_mutation_tests.contains("fn cpk_mirrored_cdm_replay_claim_fixture()"),
        "the CPK correctness fixture must keep its explicit mirrored admission boundary",
    );
    assert!(
        !bounds_mutation_tests.contains("fn legacy_only_cdm_replay_claim_fixture"),
        "CPK-8G-6e must leave no historical Legacy-only fixture boundary",
    );
    for caller in CPK8_CDM_MIRRORED_FIXTURE_CALLERS {
        let body = bounds_mutation_tests
            .split(&format!("fn {caller}"))
            .nth(1)
            .unwrap_or_else(|| panic!("CPK mirrored fixture caller moved or disappeared: {caller}"))
            .split("\n    #[test]")
            .next()
            .expect("test body")
            .split("\n    fn legacy_only_cdm_replay_claim_fixture()")
            .next()
            .expect("final mirrored test body");
        assert!(
            body.contains("cpk_mirrored_cdm_replay_claim_fixture()"),
            "{caller} must construct the raw claim through the explicit CPK mirror variant",
        );
        assert!(
            !body.contains("legacy_only_cdm_replay_claim_fixture"),
            "{caller} must not fall back to the historical flat-only fixture",
        );
    }
    assert_eq!(
        bounds_mutation_tests
            .matches("cpk_mirrored_cdm_replay_claim_fixture()")
            .count()
            - 1, // Function declaration.
        CPK8_CDM_MIRRORED_FIXTURE_CALLERS.len(),
        "only the audited A callers may construct the mirrored CDM fixture",
    );
    assert_eq!(
        CPK8_CDM_LEGACY_ONLY_FIXTURE_CALLERS.len(),
        0,
        "CPK-8G-6e closes every reviewed CDM Legacy-only purpose",
    );
    assert_eq!(
        CPK8_CDM_FIXTURE_CALLER_CLASSIFICATION
            .iter()
            .map(|(_, count)| *count)
            .sum::<usize>(),
        CPK8_CDM_MIRRORED_FIXTURE_CALLERS.len()
            + CPK8_CDM_LEGACY_ONLY_FIXTURE_CALLERS.len(),
        "every purpose-split CDM fixture caller must remain classified",
    );
    assert!(
        bounds_mutation_tests
            .split("fn cpk_mirrored_cdm_replay_claim_fixture")
            .nth(1)
            .expect("CPK-only mirrored fixture wrapper")
            .split("fn build_cdm_replay_claim_fixture")
            .next()
            .expect("CPK-only mirrored fixture wrapper body")
            .contains("ConstraintMachine::new()"),
        "the two CPK fixture callers must use oracle-disabled construction",
    );
    let legacy_call_sites = bounds_mutation_tests
        .matches("legacy_only_cdm_replay_claim_fixture()")
        .count()
        + bounds_mutation_tests
            .matches("legacy_only_cdm_replay_claim_fixture_with_authority(")
            .count();
    assert_eq!(
        legacy_call_sites, 0,
        "CPK-8G-6e forbids a remaining Legacy-only CDM fixture call site",
    );
    for caller in CPK8_CDM_LEGACY_ONLY_FIXTURE_CALLERS {
        let tail = bounds_mutation_tests
            .split(&format!("fn {caller}"))
            .nth(1)
            .unwrap_or_else(|| panic!("audited Legacy-only fixture caller moved: {caller}"));
        let top_level_end = tail.find("\n    #[test]").unwrap_or(tail.len());
        let nested_end = tail.find("\n        #[test]").unwrap_or(tail.len());
        let body = &tail[..top_level_end.min(nested_end)];
        assert!(
            body.contains("legacy_only_cdm_replay_claim_fixture"),
            "{caller} must remain on the explicit Legacy-only fixture until its B test retires",
        );
    }
    let retired_test_sources = [
        bounds_mutation_tests,
        include_str!("proof/mod.rs"),
        include_str!("tests/case_02.rs"),
    ]
    .join("\n");
    for retired in CPK8E_RETIRED_LEGACY_TESTS_AND_HELPERS {
        assert!(
            !retired_test_sources.contains(&format!("fn {retired}")),
            "CPK-8E retired Legacy purpose reappeared: {retired}",
        );
    }
    let cpk8g4b_retired_sources = [bounds_mutation_tests, include_str!("mod.rs")].join("\n");
    for retired in CPK8G4B_RETIRED_RCPF_PUBLICATION_TESTS_AND_HELPERS {
        assert!(
            !cpk8g4b_retired_sources.contains(&format!("fn {retired}")),
            "CPK-8G-4b retired RCPF publication-reader purpose reappeared: {retired}",
        );
    }
    assert!(
        CPK8_CDM_FIXTURE_CALLER_CLASSIFICATION
            .iter()
            .all(|(class, count)| {
                !matches!(class, Cpk8RawFixtureWriterClass::FixtureConstructionDebt) || *count == 0
            }),
        "the audited CDM fixture callers must leave no category-D construction debt",
    );
}

#[test]
fn cpk_8e_migration_oracle_dependent_manifest_is_closed() {
    let proof_tests = include_str!("proof/mod.rs")
        .split("mod tests {")
        .nth(1)
        .expect("proof test module");
    let bounds_tests = include_str!("machine/bounds.rs")
        .split("mod mutation_tests {")
        .nth(1)
        .expect("bounds mutation test module");
    let case_02_tests = include_str!("tests/case_02.rs");

    assert_eq!(CPK8E_SCHEME_PROJECTION_READER_MIGRATIONS.len(), 8);
    for migrated in CPK8E_SCHEME_PROJECTION_READER_MIGRATIONS {
        assert!(
            proof_tests.contains(&format!("fn {migrated}")),
            "CPK-only scheme-projection reader replacement disappeared: {migrated}",
        );
    }
    assert_eq!(
        proof_tests
            .matches("legacy_scheme_projectable_lowers_for_test")
            .count()
            + case_02_tests
                .matches("legacy_scheme_projectable_lowers_for_test")
                .count(),
        0,
        "CPK-8E closure forbids test dependencies on the Legacy scheme-projection reader",
    );

    assert_eq!(CPK8E_ROUTING_COUNT_PARITY_HOLDOUTS.len(), 0);
    assert_eq!(CPK8E_PERMANENT_FAULT_INJECTION_DEPENDENTS.len(), 0);
    assert_eq!(CPK8E_REPLACEMENT_BACKED_LEGACY_FIXTURES.len(), 0);
    assert_eq!(CPK8E_PHYSICAL_REMOVAL_DEFERRED_FIXTURES.len(), 0);
    assert_eq!(
        CPK8E_ROUTING_COUNT_PARITY_HOLDOUTS.len()
            + CPK8E_PERMANENT_FAULT_INJECTION_DEPENDENTS.len()
            + CPK8E_REPLACEMENT_BACKED_LEGACY_FIXTURES.len()
            + CPK8E_PHYSICAL_REMOVAL_DEFERRED_FIXTURES.len(),
        CPK8E_MIGRATION_ORACLE_DEPENDENT_TOTAL,
    );

    let mut classified_legacy = CPK8E_REPLACEMENT_BACKED_LEGACY_FIXTURES
        .iter()
        .chain(CPK8E_PHYSICAL_REMOVAL_DEFERRED_FIXTURES)
        .copied()
        .collect::<Vec<_>>();
    classified_legacy.sort_unstable();
    let mut audited_legacy = CPK8_CDM_LEGACY_ONLY_FIXTURE_CALLERS.to_vec();
    audited_legacy.sort_unstable();
    assert_eq!(
        classified_legacy, audited_legacy,
        "all explicit Legacy fixtures must have exactly one CPK-8E disposition",
    );

    for dependent in CPK8E_ROUTING_COUNT_PARITY_HOLDOUTS
        .iter()
        .chain(CPK8E_PERMANENT_FAULT_INJECTION_DEPENDENTS)
    {
        let body = proof_tests
            .split(&format!("fn {dependent}"))
            .nth(1)
            .unwrap_or_else(|| panic!("migration-oracle dependent disappeared: {dependent}"))
            .split("\n    #[test]")
            .next()
            .expect("test body");
        assert!(
            body.contains("cpk_3_replay_admission_fixture"),
            "{dependent} must keep its explicit migration-oracle fixture",
        );
    }
    assert_eq!(proof_tests.matches("cpk_3_replay_admission_fixture(").count(), 0);
    assert_eq!(
        proof_tests
            .matches("cpk_3_replay_admission_fixture_with_authority(")
            .count(),
        0,
    );
    assert_eq!(
        proof_tests.matches("cpk_proof_oracle_active = true").count(),
        0,
        "CPK-8G-6f removes the final Proof migration-oracle activation",
    );
    assert!(!proof_tests.contains("cpk_oracle_machine()"));

    for fixture in CPK8E_REPLACEMENT_BACKED_LEGACY_FIXTURES
        .iter()
        .chain(CPK8E_PHYSICAL_REMOVAL_DEFERRED_FIXTURES)
    {
        assert!(
            bounds_tests.contains(&format!("fn {fixture}")),
            "classified Legacy fixture disappeared without a retirement update: {fixture}",
        );
    }
    assert!(
        !bounds_tests.contains("fn legacy_only_cdm_replay_claim_fixture"),
        "CPK-8G-6e must leave no Legacy-only fixture constructor",
    );
    for removed in [
        "legacy_cpk2_shadow_expected",
        "assert_non_replay_shadow_parity",
        "assert_replay_shadow_parity",
        "occurrence_without_event",
    ] {
        assert!(
            !proof_tests.contains(removed),
            "dead CPK-2 normalizer boundary reappeared: {removed}",
        );
    }
}

fn source_test_names(source: &str) -> Vec<&str> {
    let mut names = Vec::new();
    let mut pending_test = false;
    for line in source.lines() {
        let line = line.trim();
        if line == "#[test]" {
            pending_test = true;
            continue;
        }
        if !pending_test {
            continue;
        }
        if line.starts_with("#[") {
            continue;
        }
        if let Some(rest) = line.strip_prefix("fn ") {
            names.push(rest.split('(').next().expect("test function name"));
        }
        if !line.is_empty() && !line.starts_with("//") {
            pending_test = false;
        }
    }
    names
}

#[test]
fn cpk_8g_physical_removal_manifest_is_complete_and_uniquely_classified() {
    use std::collections::BTreeSet;

    let proof_source = include_str!("proof/mod.rs");
    let bounds_source = include_str!("machine/bounds.rs");
    let constraints_source = include_str!("mod.rs");
    let machine_entry_source = include_str!("machine/entry.rs");
    let replay_factored_source = include_str!("replay_factored.rs");
    let arena_source = include_str!("../arena.rs");
    let lifecycle_source = include_str!("../analysis/session/lifecycle.rs");
    let lowering_body_source = include_str!("../lowering/body/mod.rs");
    let case_02_source = include_str!("tests/case_02.rs");
    let reviewed_physical_sources = [
        proof_source,
        bounds_source,
        replay_factored_source,
        lowering_body_source,
    ];
    let reviewed_authority_reader_sources = REVIEWED_SOURCES
        .iter()
        .map(|&(_, source)| source)
        .chain([arena_source, lifecycle_source, lowering_body_source])
        .collect::<Vec<_>>();

    let explicit_legacy = CPK8_CDM_LEGACY_ONLY_FIXTURE_CALLERS
        .iter()
        .chain(CPK8E_PERMANENT_FAULT_INJECTION_DEPENDENTS)
        .chain(CPK8G_ADDITIONAL_EXPLICIT_LEGACY_AUTHORITY_TESTS)
        .copied()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        explicit_legacy.len(),
        0,
        "CPK-8G-6e must leave zero explicit Legacy-authority tests",
    );

    let authority_oracle_dependents = explicit_legacy
        .iter()
        .copied()
        .chain(CPK8E_ROUTING_COUNT_PARITY_HOLDOUTS.iter().copied())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        authority_oracle_dependents.len(),
        0,
        "the reviewed post-8G-6e authority/oracle dependent census must be closed",
    );
    let historical_legacy_characterizations = authority_oracle_dependents
        .iter()
        .copied()
        .chain(CPK8G6_IMPLICIT_LEGACY_READER_DEPENDENTS.iter().copied())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        historical_legacy_characterizations.len(),
        CPK8G6_HISTORICAL_LEGACY_CHARACTERIZATION_TOTAL,
        "the complete 8G-6 category-B Legacy reader census changed",
    );
    assert_eq!(
        CPK8G6_CPK_ONLY_CORRECTNESS_CONTRACTS.len(),
        CPK8G6_CPK_ONLY_CORRECTNESS_CONTRACT_TOTAL,
        "the 8G-6 category-A CPK-only survivor census changed",
    );
    for &contract in CPK8G6_CPK_ONLY_CORRECTNESS_CONTRACTS {
        let source_occurrences = reviewed_physical_sources
            .iter()
            .map(|source| source.matches(&format!("fn {contract}")).count())
            .sum::<usize>();
        assert_eq!(
            source_occurrences, 1,
            "8G-6 category-A contract moved, disappeared, or became ambiguous: {contract}",
        );
    }
    for &(retired, reason) in CPK8G6B_RETIRED_PROOF_ORACLE_AND_REPLACEMENT_BACKED_TESTS {
        assert!(!reason.is_empty(), "retired test must retain its category-B reason");
        let source_occurrences = reviewed_physical_sources
            .iter()
            .map(|source| source.matches(&format!("fn {retired}(")).count())
            .sum::<usize>();
        assert_eq!(
            source_occurrences, 0,
            "8G-6b retired test reappeared without a new disposition: {retired}",
        );
    }
    assert_eq!(CPK8G6C_RETIRED_FLAT_CDM_TESTS.len(), 20);
    for &(retired, reason) in CPK8G6C_RETIRED_FLAT_CDM_TESTS {
        assert!(!reason.is_empty(), "retired test must retain its category-B reason");
        let source_occurrences = reviewed_physical_sources
            .iter()
            .map(|source| source.matches(&format!("fn {retired}")).count())
            .sum::<usize>();
        assert_eq!(
            source_occurrences, 0,
            "8G-6c retired test reappeared without a new disposition: {retired}",
        );
    }
    assert_eq!(CPK8G6C_RETIRED_FLAT_CDM_DEDICATED_HELPERS.len(), 4);
    for &retired in CPK8G6C_RETIRED_FLAT_CDM_DEDICATED_HELPERS {
        assert_eq!(
            bounds_source.matches(&format!("fn {retired}")).count(),
            0,
            "8G-6c retired dedicated census helper reappeared: {retired}",
        );
    }
    assert_eq!(CPK8G6D_RETIRED_RCPF_PARENT_OCCURRENCE_TESTS.len(), 14);
    for &(retired, reason) in CPK8G6D_RETIRED_RCPF_PARENT_OCCURRENCE_TESTS {
        assert!(!reason.is_empty(), "retired test must retain its category-B reason");
        let source_occurrences = reviewed_physical_sources
            .iter()
            .map(|source| source.matches(&format!("fn {retired}")).count())
            .sum::<usize>();
        assert_eq!(
            source_occurrences, 0,
            "8G-6d retired test reappeared without a new disposition: {retired}",
        );
    }
    assert_eq!(
        CPK8G6D_RETIRED_RCPF_PARENT_OCCURRENCE_DEDICATED_HELPERS.len(),
        9,
    );
    for &retired in CPK8G6D_RETIRED_RCPF_PARENT_OCCURRENCE_DEDICATED_HELPERS {
        assert_eq!(
            bounds_source.matches(&format!("fn {retired}")).count(),
            0,
            "8G-6d retired dedicated census helper reappeared: {retired}",
        );
    }
    for &retired in CPK8G6D_RETIRED_RCPF_PARENT_OCCURRENCE_TYPE_ALIASES {
        assert!(
            !bounds_source.contains(&format!("type {retired}")),
            "8G-6d retired test-only type alias reappeared: {retired}",
        );
    }
    assert_eq!(
        CPK8G6E_RETIRED_RCPF_PUBLICATION_FAILURE_READER_TESTS.len(),
        19,
    );
    for &(retired, reason) in CPK8G6E_RETIRED_RCPF_PUBLICATION_FAILURE_READER_TESTS {
        assert!(!reason.is_empty(), "retired test must retain its category-B reason");
        let source_occurrences = reviewed_physical_sources
            .iter()
            .map(|source| source.matches(&format!("fn {retired}")).count())
            .sum::<usize>();
        assert_eq!(
            source_occurrences, 0,
            "8G-6e retired test reappeared without a new disposition: {retired}",
        );
    }
    for &retired in CPK8G6E_RETIRED_RCPF_PUBLICATION_FAILURE_READER_HELPERS {
        let source_occurrences = reviewed_physical_sources
            .iter()
            .map(|source| source.matches(&format!("fn {retired}(")).count())
            .sum::<usize>();
        assert_eq!(
            source_occurrences, 0,
            "8G-6e retired dedicated helper reappeared: {retired}",
        );
    }
    for &retired in CPK8G6E_RETIRED_RCPF_PUBLICATION_FAILURE_READER_TYPES {
        assert!(
            reviewed_physical_sources
                .iter()
                .all(|source| !source.contains(&format!("{retired}"))),
            "8G-6e retired test-only type reappeared: {retired}",
        );
    }
    assert_eq!(
        CPK8G6_RETIRED_CATEGORY_B_TOTAL, 60,
        "CPK-8G-6 category-B retirement ledger must account for all 60 reviewed tests",
    );
    assert_eq!(
        historical_legacy_characterizations.len(), 0,
        "CPK-8G-6e must leave zero category-B Legacy-reader dependents",
    );
    assert_eq!(
        CPK8G6_COMPLETED_SUBSLICES.len(),
        CPK8G6_COMPLETED_SUBSLICE_TOTAL,
        "the CPK-8G-6 closure ledger must contain all nine sub-slices",
    );
    let completed_subslices = CPK8G6_COMPLETED_SUBSLICES
        .iter()
        .map(|&(slice, summary)| {
            assert!(!summary.is_empty(), "completed sub-slice must retain its disposition");
            slice
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(
        completed_subslices,
        [
            "8G-6a", "8G-6b", "8G-6c", "8G-6d", "8G-6e", "8G-6f", "8G-6g1",
            "8G-6g2", "8G-6h",
        ]
        .into_iter()
        .collect(),
        "the CPK-8G-6 closure ledger must account for every approved sub-slice exactly once",
    );
    for &(retired, reason) in CPK8G6G1_RETIRED_LEGACY_READER_TESTS {
        assert!(!reason.is_empty(), "retired test must retain its category-B reason");
        assert_eq!(
            reviewed_physical_sources
                .iter()
                .map(|source| source.matches(&format!("fn {retired}(")).count())
                .sum::<usize>(),
            0,
            "CPK-8G-6g1 retired Legacy-reader test reappeared: {retired}",
        );
    }
    let removed_authority_reader_surfaces = CPK8G6F_REMOVED_PROOF_AUTHORITY_SURFACES
        .iter()
        .chain(CPK8G6G1_REMOVED_LEGACY_READER_SURFACES)
        .chain(CPK8G6G2_REMOVED_REPLAY_AUTHORITY_SURFACES)
        .copied()
        .collect::<BTreeSet<_>>();
    assert_eq!(
        removed_authority_reader_surfaces.len(),
        CPK8G6F_REMOVED_PROOF_AUTHORITY_SURFACES.len()
            + CPK8G6G1_REMOVED_LEGACY_READER_SURFACES.len()
            + CPK8G6G2_REMOVED_REPLAY_AUTHORITY_SURFACES.len(),
        "each removed authority/reader surface must have one unambiguous 8G-6 disposition",
    );
    for removed in removed_authority_reader_surfaces {
        assert!(
            reviewed_authority_reader_sources
                .iter()
                .all(|source| !source.contains(removed)),
            "CPK-8G-6h removed authority/Legacy-reader surface reappeared: {removed}",
        );
    }
    assert!(
        machine_entry_source.contains("ReplayFactoredShadowStatus::Active"),
        "CPK-8G-6g2 must retain the sticky RCPF quarantine gate while removing authority selection",
    );
    for surviving_writer in [
        "commit_claim_qualified_parent_mutation",
        "record_cpk_replay_parent_snapshot",
        "record_projection_clause",
        "record_projection_supports",
    ] {
        assert!(
            [proof_source, bounds_source, constraints_source]
                .iter()
                .any(|source| source.contains(surviving_writer)),
            "CPK-8G-6f must leave the dual-write path intact: {surviving_writer}",
        );
    }
    for replacement in [
        "canonical_projection_storage_is_invariant_across_all_four_event_permutations",
        "cpk_8f3_rcpf_failure_does_not_start_a_second_proof_attempt",
        "cpk_8g_4b_evaluator_traps_missing_machine_issued_references",
        "cpk_gap_1_every_proof_failure_is_attempt_terminal",
        "cpk_gap_1_mixed_claim_fixture_matches_all_four_cpk_consumers_exactly",
        "cpk_premise_dependency_chain_contains_exact_replay_endpoints",
        "cpk_projection_target_and_dependency_admission_is_atomic_and_target_late",
        "cpk_projection_target_late_metadata_bootstraps_formula",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed",
        "dpn_b_9_5_late_constraint_route_retriggers_dependent_record",
        "rcpf_c3a_failed_attempt_is_discarded_as_typed_hard_error",
        "rcpf_c3a_normal_attempt_runs_once_without_authority_dispatch",
        "target_late_mixed_roots_do_not_expose_historical_order_to_later_replay",
    ] {
        let source_occurrences = reviewed_physical_sources
            .iter()
            .copied()
            .chain(std::iter::once(case_02_source))
            .map(|source| source.matches(&format!("fn {replacement}")).count())
            .sum::<usize>();
        assert_eq!(
            source_occurrences, 1,
            "8G-6e CPK/system replacement moved or disappeared: {replacement}",
        );
    }
    for replacement in [
        "cpk_7_slice_b_keeps_uncovered_decoupled_route_beside_generic_pair",
        "cpk_7_slice_b_routes_covered_pairs_and_deduplicates_incremental_input",
        "cpk_gap_1_same_root_permutations_preserve_canonical_payload_shape",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed",
        "cpk_7_cpk_authority_preflight_rejects_claim_index_corruption",
        "cpk_terminal_failure_stops_drain_before_the_next_queued_work",
        "cpk_projection_target_late_metadata_bootstraps_formula",
        "cpk_evidence_and_trivial_replays_do_not_create_projection_formula",
        "cpk_premise_dependency_chain_contains_exact_replay_endpoints",
    ] {
        assert_eq!(
            proof_source.matches(&format!("fn {replacement}")).count(),
            1,
            "8G-6b CPK-owned replacement moved or disappeared: {replacement}",
        );
    }
    for replacement in [
        "cpk_3_exact_replay_and_first_witness_match_factored_oracle",
        "cpk_3_replay_first_winner_matches_factored_for_every_parent_arrival_order",
        "cpk_7_slice_a_prepared_parent_blocks_share_exact_entries",
        "cpk_7_slice_a_replay_indexes_update_atomically_with_writers",
        "cpk_gap_1_five_lineages_project_through_the_real_formula_graph",
        "cpk_no_claim_path_allocates_no_claim_storage_or_index_work",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed",
        "cpk_terminal_failure_stops_drain_before_the_next_queued_work",
        "target_late_mixed_roots_do_not_expose_historical_order_to_later_replay",
        "rcpf_c3a_failed_attempt_is_discarded_as_typed_hard_error",
    ] {
        let source_occurrences = reviewed_physical_sources
            .iter()
            .map(|source| source.matches(&format!("fn {replacement}")).count())
            .sum::<usize>();
        assert_eq!(
            source_occurrences, 1,
            "8G-6d surviving CPK/system replacement moved or disappeared: {replacement}",
        );
    }
    for replacement in [
        "cpk_7_slice_a_claim_index_writes_do_not_scan_the_global_claim_store",
        "cpk_7_slice_a_prepared_parent_blocks_share_exact_entries",
        "cpk_8g_4b_evaluator_traps_missing_machine_issued_references",
        "cpk_gap_1_mixed_claim_fixture_matches_all_four_cpk_consumers_exactly",
        "cpk_gap_1_five_lineages_project_through_the_real_formula_graph",
        "cpk_claim_payload_matches_flat_across_five_lineages_and_move",
        "cpk_claim_move_updates_record_coverage_and_preserves_root_liveness",
        "cpk_qualified_parent_admission_is_atomic_and_canonically_indexed",
        "cpk_projection_target_and_dependency_admission_is_atomic_and_target_late",
        "cpk_2_non_replay_proof_events_match_frozen_contract",
        "cpk_3_evidence_only_replay_records_both_bound_edges_in_active_shadow",
        "cpk_evidence_and_trivial_replays_do_not_create_projection_formula",
    ] {
        assert_eq!(
            proof_source.matches(&format!("fn {replacement}")).count(),
            1,
            "8G-6c CPK-owned replacement moved or disappeared: {replacement}",
        );
    }

    let replay_factored_tests = source_test_names(replay_factored_source);
    let bounds_rcpf_tests = source_test_names(bounds_source)
        .into_iter()
        .filter(|name| name.starts_with("rcpf_"))
        .collect::<Vec<_>>();
    let lowering_body_rcpf_tests = source_test_names(lowering_body_source)
        .into_iter()
        .filter(|name| name.starts_with("rcpf_"))
        .collect::<Vec<_>>();
    assert_eq!(
        replay_factored_tests.len(),
        10,
        "the direct replay_factored.rs unit-test census changed",
    );
    assert_eq!(
        bounds_rcpf_tests.len(),
        1,
        "the direct machine/bounds.rs rcpf_* test census changed",
    );
    assert_eq!(
        lowering_body_rcpf_tests.len(),
        4,
        "the direct lowering/body/mod.rs rcpf_* test census changed",
    );

    let deferred_rcpf_structure_tests = CPK8G_PHYSICAL_REMOVAL_TEST_GROUPS
        .iter()
        .filter(|group| {
            !group
                .targets
                .contains(&Cpk8gPhysicalTarget::ReplayFactoredShellAndTelemetry)
        })
        .flat_map(|group| group.tests.iter().copied())
        .collect::<BTreeSet<_>>();
    let enumerated_rcpf_structure_tests = replay_factored_tests
        .iter()
        .copied()
        .chain(bounds_rcpf_tests.iter().copied())
        .collect::<BTreeSet<_>>();
    for group in CPK8G_PHYSICAL_REMOVAL_TEST_GROUPS {
        if group
            .targets
            .contains(&Cpk8gPhysicalTarget::ReplayFactoredShellAndTelemetry)
        {
            assert_eq!(
                group.targets,
                &[Cpk8gPhysicalTarget::ReplayFactoredShellAndTelemetry],
                "shell/telemetry coverage must not hide an 8G-9/10 structure dependency",
            );
        }
    }
    assert_eq!(
        deferred_rcpf_structure_tests.len(),
        CPK8G9_10_DEFERRED_RCPF_STRUCTURE_TEST_TOTAL,
        "the direct RCPF structure-test deferral must remain intact for 8G-9/10",
    );
    assert_eq!(
        deferred_rcpf_structure_tests, enumerated_rcpf_structure_tests,
        "8G-6 closure must not absorb or misclassify direct RCPF structure tests deferred to 8G-9/10",
    );

    let expected_manifest = historical_legacy_characterizations
        .iter()
        .copied()
        .chain(replay_factored_tests.iter().copied())
        .chain(bounds_rcpf_tests.iter().copied())
        .chain(lowering_body_rcpf_tests.iter().copied())
        .collect::<BTreeSet<_>>();

    let all_targets = [
        Cpk8gPhysicalTarget::ParentSetArena,
        Cpk8gPhysicalTarget::ReplayOccurrenceStore,
        Cpk8gPhysicalTarget::ReplayResultSummary,
        Cpk8gPhysicalTarget::ReplayFactoredShellAndTelemetry,
    ];
    let mut manifested_names = BTreeSet::new();
    let mut manifested_targets = BTreeSet::new();
    for group in CPK8G_PHYSICAL_REMOVAL_TEST_GROUPS {
        assert!(
            !group.targets.is_empty(),
            "a physical-removal test group must protect at least one concrete target",
        );
        let target_set = group.targets.iter().copied().collect::<BTreeSet<_>>();
        assert_eq!(
            target_set.len(),
            group.targets.len(),
            "a physical target was duplicated inside one classification group",
        );
        manifested_targets.extend(target_set);
        for &name in group.tests {
            assert!(
                manifested_names.insert(name),
                "{name} appears in more than one physical-removal classification; represent multi-target coverage in one target set",
            );
            let source_occurrences = reviewed_physical_sources
                .iter()
                .map(|source| source.matches(&format!("fn {name}")).count())
                .sum::<usize>();
            assert_eq!(
                source_occurrences, 1,
                "physical-removal manifest entry moved, disappeared, or became ambiguous: {name}",
            );
        }
    }

    assert_eq!(
        manifested_targets,
        all_targets.into_iter().collect(),
        "every physical-removal layer must retain an explicitly classified protecting test",
    );
    assert_eq!(
        manifested_names, expected_manifest,
        "the physical-removal manifest must equal the source-enumerated union; classify additions and remove retired entries together",
    );
}

#[test]
fn cpk_0c_projection_admission_fixture_matrix_explains_known_boundaries() {
    let cases = [
        (
            "independent then claimed full bootstrap",
            ProjectionAdmissionInput {
                lower_exists: true,
                qualified_parent_batch_inserted: true,
                had_qualified_parent_before: false,
                projection_ledger_existed_before: false,
                all_claimed_roots_after_event: 1,
                new_claimed_roots: 1,
                event_carrier_present: true,
            },
            ProjectionAdmissionPlan {
                claimed_roots: ClaimedRootPlan::FullBootstrap(1),
                independent_supports: IndependentSupportPlan::RecordFullBootstrap,
            },
        ),
        (
            "pre-existing direct claim plus first replay",
            ProjectionAdmissionInput {
                lower_exists: true,
                qualified_parent_batch_inserted: true,
                had_qualified_parent_before: false,
                projection_ledger_existed_before: true,
                all_claimed_roots_after_event: 1,
                new_claimed_roots: 0,
                event_carrier_present: true,
            },
            ProjectionAdmissionPlan {
                claimed_roots: ClaimedRootPlan::None,
                independent_supports: IndependentSupportPlan::ProducerFullScan,
            },
        ),
        (
            "duplicate replay exact no-op",
            ProjectionAdmissionInput {
                lower_exists: true,
                qualified_parent_batch_inserted: false,
                had_qualified_parent_before: true,
                projection_ledger_existed_before: true,
                all_claimed_roots_after_event: 1,
                new_claimed_roots: 0,
                event_carrier_present: false,
            },
            ProjectionAdmissionPlan {
                claimed_roots: ClaimedRootPlan::None,
                independent_supports: IndependentSupportPlan::None,
            },
        ),
        (
            "target-late lower creation",
            ProjectionAdmissionInput {
                lower_exists: true,
                qualified_parent_batch_inserted: false,
                had_qualified_parent_before: true,
                projection_ledger_existed_before: false,
                all_claimed_roots_after_event: 2,
                new_claimed_roots: 0,
                event_carrier_present: false,
            },
            ProjectionAdmissionPlan {
                claimed_roots: ClaimedRootPlan::FullBootstrap(2),
                independent_supports: IndependentSupportPlan::RecordFullBootstrap,
            },
        ),
        (
            "existing ledger event delta",
            ProjectionAdmissionInput {
                lower_exists: true,
                qualified_parent_batch_inserted: true,
                had_qualified_parent_before: true,
                projection_ledger_existed_before: true,
                all_claimed_roots_after_event: 2,
                new_claimed_roots: 1,
                event_carrier_present: true,
            },
            ProjectionAdmissionPlan {
                claimed_roots: ClaimedRootPlan::Delta(1),
                independent_supports: IndependentSupportPlan::EventCarrier,
            },
        ),
    ];
    for (name, input, expected) in cases {
        assert_eq!(projection_admission_plan(input), expected, "{name}");
    }
}
