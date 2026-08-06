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
// A correctness-contract: 6 CPK proof query fixtures with an explicit proof-store mirror.
// B historical Legacy characterization: 4 explicit LegacyRollback/RCPF parent-draft fixtures.
// C semantic fixture: 24 local semantic/provenance fixtures that inspect record identity.
// D fixture-construction debt: 0; the CPK-6b/CPK-7 hygiene passes migrated every known
// oracle-active shortcut to a mirrored admission path.
//
// These counts classify lexical writer sites, not every caller of a shared fixture. CPK-8B splits
// the dual-purpose CDM fixture at an explicit proof-state boundary: CPK-0b/0c use the mirrored
// variant, while the remaining RCPF/CDM callers retain flat-only behavior through a clearly named
// Legacy-only variant. Those remaining callers still require an individual §6 purpose audit; the
// rename in this slice is deliberately not recorded as their completed retirement classification.
//
// Production read/write graph for CPK-8B, grouped by physical field ownership:
// - upper_replay_claims and its record/root/producer indexes: writers original/derived claim,
//   claim move, register_constraint_upper_replay_claims; readers legacy projection/routing and
//   CPK record_upper_claim/prepare_replay_route mirrors.
// - claim_parents_by_constraint, qualified_carrier_index, replay/structural parent keys:
//   writers commit_claim_qualified_parent_mutation and row/reduction admission; readers legacy
//   parent drafts/RCPF plus CPK projection-support and routing-parent mirrors.
// - live_coverage_by_root and scheme_projection_claims_by_lower_record: projection-link admission
//   still writes both representations. CPK-8B transfers live-coverage transition/dedup ownership
//   to ProofOccurrenceStore::live_states_by_coverage_root; live_coverage_by_root remains the
//   migration mirror read by legacy projectability/routing.
// - projection proofs/clauses/attributed supports/dependent-record edges: writers projection
//   delta, clause-link and dependency-chain admission; readers legacy formula evaluation and CPK
//   proof formulas/supports. These remain a writer-dependency closure, not proof-only deletion.
// - ParentSetArena/ReplayOccurrenceStore/ReplayResultSummary/ReplayClauseProjection/
//   NonReplayClaimParentStore: writers replay admission and parent mutation; readers Factored
//   replay authority and exact test-only shadow capture. CPK-8B must replace writers before any
//   physical removal.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cpk8RawFixtureWriterClass {
    CorrectnessContract,
    HistoricalLegacyCharacterization,
    SemanticFixture,
    FixtureConstructionDebt,
}

const CPK8_RAW_FIXTURE_WRITER_CLASSIFICATION: &[(Cpk8RawFixtureWriterClass, usize)] = &[
    (Cpk8RawFixtureWriterClass::CorrectnessContract, 6),
    (Cpk8RawFixtureWriterClass::HistoricalLegacyCharacterization, 4),
    (Cpk8RawFixtureWriterClass::SemanticFixture, 24),
    (Cpk8RawFixtureWriterClass::FixtureConstructionDebt, 0),
];

const CPK8_RAW_FIXTURE_WRITER_TOTAL: usize = 34;

const CPK8_CDM_MIRRORED_FIXTURE_CALLERS: &[&str] = &[
    "cpk_0b_captures_canonical_logical_proof_surfaces_end_to_end",
    "cpk_0c_fixture_matrix_captures_semantic_and_logical_baselines",
];

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
const PROOF_STATE_REFERENCE_CENSUS: &[(&str, usize)] = &[
    ("claim_parents_by_constraint", 66),
    ("replay_claim_parent_keys", 11),
    ("qualified_carrier_index", 26),
    ("structural_claim_parent_keys", 2),
    ("scheme_projection_claims_by_lower_record", 24),
    // CPK-4 adds reviewed test-only reads for the writer-boundary snapshot and
    // mutation-oracle readiness, plus one fixture-only empty-ledger seed. CPK-5
    // adds one routing-shadow capture-readiness read. Slice B adds one reviewed test-only
    // empty-ledger seed. CPK-8B removes the sole production-store projection writer re-read by
    // carrying its support snapshot in the admission event.
    ("projection_proofs_by_lower_record", 47),
    ("scheme_projection_lower_records_by_root", 5),
    ("scheme_projection_lower_record_memberships", 4),
    ("record_proof_clauses", 6),
    ("record_proof_clause_by_key", 10),
    ("record_proof_clause_ids_by_lower_record", 4),
    // CPK-4's test-only publication oracle checks that capture began before every link writer.
    ("record_proof_clause_links_by_lower_record", 7),
    ("record_proof_clause_link_keys", 12),
    ("attributed_claim_supports", 33),
    ("flat_retained_attributed_claim_supports", 12),
    ("dependent_records_by_premise", 23),
    // CPK-2's test-only legacy parity reconstruction adds one reviewed root-origin read.
    // Fixture hygiene now uses the reviewed root-admission API instead of four raw field writes.
    ("origins", 131),
    ("source_boundaries", 7),
    // CPK-2's test-only legacy parity reconstruction adds two reviewed row-derivation reads.
    // Fixture hygiene removes two raw synthetic ConstraintRecord field initializers and two
    // direct row-attachment writes in favor of the reviewed mirrored admission API. The CPK-7
    // endpoint correction adds one test-only semantic row-provenance merge assertion.
    ("row_derivations", 53),
    ("generalized_schemes", 9),
    // Slice B's test-only four-consumer oracle and Included(empty) regression invoke the
    // reviewed generalized-witness reader. Neither adds a production proof-state consumer.
    ("generalized_witnesses", 13),
    // CPK-2's test-only legacy parity reconstruction adds two reviewed instantiation reads.
    // CPK-6a adds one reviewed production-store scheme-instantiation writer read.
    ("scheme_instantiations", 18),
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
    // None is a new production read authority.
    ("upper_replay_claims", 105),
    // CPK-7 Slice A adds nine reviewed references for the approved production CPK index and its
    // atomicity/no-global-scan tests. Slice B adds the reviewed query read and fault injection.
    // Routing authority remains Legacy in both slices.
    ("claims_by_upper_record", 25),
    // CPK-3's test-only parity oracle adds one reviewed live-coverage read.
    ("live_coverage_by_root", 10),
    // CPK-3's test-only parity oracle adds one reviewed parent-set read.
    ("replay_parent_sets", 21),
    // CPK-3's test-only finite-map/first-witness oracle adds four reviewed occurrence reads.
    ("replay_occurrences", 54),
    // CPK-3's test-only first-witness parity oracle adds one reviewed summary read.
    ("replay_result_summary", 44),
    ("replay_clause_projection", 34),
    ("non_replay_claim_parents_by_constraint", 9),
];

const REVIEWED_BOUNDARIES: &[(&str, &str)] = &[
    // Test-only CPK shadow parity consumer; never a production authority.
    (
        "constraints/proof/mod.rs",
        "legacy_cpk2_shadow_expected",
    ),
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
    ("constraints/mod.rs", "push_claim_qualified_parent"),
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
        "constraints/mod.rs",
        "link_scheme_projection_claim_to_constraint_lower",
    ),
    ("constraints/mod.rs", "link_scheme_projection_claim"),
    ("constraints/mod.rs", "update_scheme_projection_proofs"),
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
    ("constraints/mod.rs", "register_record_proof_clause_link"),
    (
        "constraints/machine/bounds.rs",
        "commit_record_proof_clause_link_batch_mutation",
    ),
    (
        "constraints/machine/bounds.rs",
        "register_replay_evidence_clause_link",
    ),
    (
        "constraints/mod.rs",
        "register_original_claim_standalone_link",
    ),
    ("constraints/mod.rs", "insert_dependent_record_edge"),
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
        bounds_mutation_tests.contains("fn legacy_only_cdm_replay_claim_fixture()"),
        "historical callers must not silently regain an implicit dual-purpose fixture",
    );
    for caller in CPK8_CDM_MIRRORED_FIXTURE_CALLERS {
        let body = bounds_mutation_tests
            .split(&format!("fn {caller}"))
            .nth(1)
            .unwrap_or_else(|| panic!("CPK mirrored fixture caller moved or disappeared: {caller}"))
            .split("\n    #[test]")
            .next()
            .expect("test body");
        assert!(
            body.contains("cpk_mirrored_cdm_replay_claim_fixture()"),
            "{caller} must construct the raw claim through the explicit CPK mirror variant",
        );
        assert!(
            !body.contains("legacy_only_cdm_replay_claim_fixture"),
            "{caller} must not fall back to the historical flat-only fixture",
        );
    }
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
