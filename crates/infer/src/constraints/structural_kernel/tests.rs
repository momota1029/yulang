use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::Command;
use std::{cell::Cell, rc::Rc};

use poly::expr::DefId;
use poly::types::{Neg, Pos, Subtractability, TypeVar};

use super::commands::StructuralMutationIntent as I;
use super::{ProofAccessError, ProofAttemptKernel};
use crate::constraints::proof::{ProofFailure, ProofOperation};
use crate::constraints::{
    BoundDerivation, BoundRecordId, ConstraintMachine, ConstraintRecordId, ConstraintWeights,
    GeneralizedSchemeRecordId, LowerFilterRecordId, OriginId, ProvenanceCompleteness,
    UnweightedRowReductionRecordId, UpperReplayClaimId,
};

fn foreign_publication_round_failure() -> ProofFailure {
    let first = ConstraintMachine::new();
    let mut round = first.new_publication_evaluation_round();
    let mut second = ConstraintMachine::new();
    second
        .with_legacy_publication_query(&mut round, |query| Ok(query.complete(())))
        .expect_err("a round minted by another machine must fail authentication")
}

fn add_row4_test_lower(machine: &mut ConstraintMachine, seed: u32) -> BoundRecordId {
    let owner = TypeVar(seed);
    let endpoint = machine.alloc_pos(Pos::Var(TypeVar(seed + 1)));
    machine
        .bounds
        .add_lower(
            owner,
            endpoint,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(OriginId::unknown_internal()),
        )
        .id
}

fn assert_row4_row7_canary_panic(panic: Box<dyn std::any::Any + Send>) {
    let message = panic
        .downcast_ref::<&str>()
        .copied()
        .or_else(|| panic.downcast_ref::<String>().map(String::as_str));
    assert_eq!(
        message,
        Some(
            "row 4/7 post-commit non-terminal denial invalidates the reviewed same-machine round-locality invariant"
        )
    );
}

const ALL_INTENTS: [I; 29] = [
    I::AppendProofOccurrence,
    I::AdmitProjectionSupport,
    I::AdmitProjectionFormulaClause,
    I::AdmitProjectionIndex,
    I::AdmitOriginalClaim,
    I::DecideDerivedClaim,
    I::MoveUpperClaim,
    I::BindReductionClaim,
    I::TransitionLiveCoverage,
    I::AdmitReplayRelation,
    I::AdmitReplayQualifiedParents,
    I::AdmitQualifiedParents,
    I::AdmitBound,
    I::PromoteBound,
    I::TombstoneBound,
    I::ExtendBoundDerivation,
    I::AdmitConstraint,
    I::ExtendConstraintProof,
    I::UpdateReplayCompleteness,
    I::AdmitReplayDrop,
    I::AdmitRowResidual,
    I::AdmitRowDerivation,
    I::AdmitRowReduction,
    I::AdvanceRowReductionMatched,
    I::AdvanceRowReductionUnmatched,
    I::UpdateRowReductionOwner,
    I::AdmitLowerFilter,
    I::AdmitStructuralIdentity,
    I::AdmitSchemeInstantiation,
];

#[test]
fn cpk_sv_d_ss2_p0_liveness_query_denial_precedes_authoritative_commit() {
    let mut machine = ConstraintMachine::new();
    let root = UpperReplayClaimId(98_101);
    let state = UnweightedRowReductionRecordId(98_102);

    machine
        .proof_attempt
        .inject_query_scope_failure(ProofFailure::TerminalLatchBusy);
    assert!(
        !machine.insert_scheme_projection_live_coverage_state(root, state),
        "retryable query denial must not report a committed liveness transition"
    );
    assert!(
        machine.insert_scheme_projection_live_coverage_state(root, state),
        "the same transition must remain commit-ready after retryable query denial"
    );
    assert!(
        !machine.insert_scheme_projection_live_coverage_state(root, state),
        "the successful retry must commit exactly once"
    );
}

#[test]
#[should_panic(
    expected = "row 4/7 post-commit non-terminal denial invalidates the reviewed same-machine round-locality invariant"
)]
fn cpk_sv_d_ss2_p0_record_inclusion_publication_rejects_nonterminal_post_commit_denial() {
    let mut machine = ConstraintMachine::new();
    machine
        .proof_attempt
        .inject_query_scope_failure(ProofFailure::TerminalLatchBusy);

    let _ = machine.evaluate_record_inclusion_publication(BoundRecordId(98_103), false, false);
}

#[test]
fn cpk_sv_d_ss2_p0_row4_precommit_denial_blocks_commit_and_publication() {
    let mut machine = ConstraintMachine::new();
    let lower_record = add_row4_test_lower(&mut machine, 98_104);
    let commits = Rc::new(Cell::new(0));
    let mutation =
        ConstraintMachine::test_scheme_projection_mutation(lower_record, Rc::clone(&commits));
    let publication_before = machine.provenance_epoch;
    machine
        .proof_attempt
        .inject_query_scope_failure(ProofFailure::TerminalLatchBusy);

    assert_eq!(
        machine.apply_scheme_projection_mutation(mutation),
        Err(ProofFailure::TerminalLatchBusy)
    );
    assert_eq!(commits.get(), 0);
    assert_eq!(machine.provenance_epoch, publication_before);
}

#[test]
fn cpk_sv_d_ss2_p0_row4_success_commits_and_publishes_exactly_once() {
    let mut machine = ConstraintMachine::new();
    let lower_record = add_row4_test_lower(&mut machine, 98_105);
    let commits = Rc::new(Cell::new(0));
    let mutation =
        ConstraintMachine::test_scheme_projection_mutation(lower_record, Rc::clone(&commits));
    let publication_before = machine.provenance_epoch.as_u64();

    machine.apply_scheme_projection_mutation(mutation).unwrap();

    assert_eq!(commits.get(), 1);
    assert_eq!(machine.provenance_epoch.as_u64(), publication_before + 1);
}

#[test]
fn cpk_sv_d_ss2_p0_row4_semantic_postcommit_failure_is_terminal_without_publication() {
    let mut machine = ConstraintMachine::new();
    let lower_record = add_row4_test_lower(&mut machine, 98_106);
    let commits = Rc::new(Cell::new(0));
    let mutation =
        ConstraintMachine::test_scheme_projection_mutation(lower_record, Rc::clone(&commits));
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    let publication_before = machine.provenance_epoch;
    machine
        .proof_attempt
        .inject_query_scope_failure_after_successful_scopes(1, failure.clone());

    machine.apply_scheme_projection_mutation(mutation).unwrap();

    assert_eq!(commits.get(), 1);
    assert_eq!(machine.proof_terminal_failure(), Some(failure));
    assert_eq!(machine.provenance_epoch, publication_before);
}

#[test]
fn cpk_sv_d_ss2_p0_row4_nonterminal_postcommit_denials_trip_release_canary() {
    for failure in [
        ProofFailure::TerminalLatchBusy,
        foreign_publication_round_failure(),
    ] {
        let mut machine = ConstraintMachine::new();
        let lower_record = add_row4_test_lower(&mut machine, 98_107);
        let commits = Rc::new(Cell::new(0));
        let mutation =
            ConstraintMachine::test_scheme_projection_mutation(lower_record, Rc::clone(&commits));
        let publication_before = machine.provenance_epoch;
        machine
            .proof_attempt
            .inject_query_scope_failure_after_successful_scopes(1, failure);

        let panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = machine.apply_scheme_projection_mutation(mutation);
        }));
        assert_row4_row7_canary_panic(
            panic.expect_err("a post-commit non-terminal denial must trip the release canary"),
        );
        assert_eq!(commits.get(), 1);
        assert_eq!(machine.provenance_epoch, publication_before);
    }
}

#[test]
fn cpk_sv_d_ss2_p0_defer_precommit_denial_and_success_preserve_fence_boundary() {
    let mut denied = ConstraintMachine::new();
    let denied_record = add_row4_test_lower(&mut denied, 98_110);
    let denied_commits = Rc::new(Cell::new(0));
    let denied_pushes = Rc::new(Cell::new(0));
    denied
        .proof_attempt
        .inject_query_scope_failure(ProofFailure::TerminalLatchBusy);
    let result = denied.defer_scheme_projection_mutation_for_test(
        ConstraintMachine::test_scheme_projection_mutation(
            denied_record,
            Rc::clone(&denied_commits),
        ),
        Rc::clone(&denied_pushes),
    );
    assert_eq!(result, Err(ProofFailure::TerminalLatchBusy));
    assert_eq!((denied_commits.get(), denied_pushes.get()), (0, 0));

    let mut success = ConstraintMachine::new();
    let success_record = add_row4_test_lower(&mut success, 98_112);
    let success_commits = Rc::new(Cell::new(0));
    let success_pushes = Rc::new(Cell::new(0));
    success
        .defer_scheme_projection_mutation_for_test(
            ConstraintMachine::test_scheme_projection_mutation(
                success_record,
                Rc::clone(&success_commits),
            ),
            Rc::clone(&success_pushes),
        )
        .unwrap();
    assert_eq!((success_commits.get(), success_pushes.get()), (1, 1));
}

#[test]
fn cpk_sv_d_ss2_p0_defer_postcommit_denials_use_canary_or_terminal_branch() {
    for failure in [
        ProofFailure::TerminalLatchBusy,
        foreign_publication_round_failure(),
    ] {
        let mut machine = ConstraintMachine::new();
        let record = add_row4_test_lower(&mut machine, 98_114);
        let commits = Rc::new(Cell::new(0));
        let pushes = Rc::new(Cell::new(0));
        machine
            .proof_attempt
            .inject_query_scope_failure_after_successful_scopes(1, failure);
        let panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = machine.defer_scheme_projection_mutation_for_test(
                ConstraintMachine::test_scheme_projection_mutation(record, Rc::clone(&commits)),
                Rc::clone(&pushes),
            );
        }));
        assert_row4_row7_canary_panic(panic.expect_err("defer canary must panic"));
        assert_eq!((commits.get(), pushes.get()), (1, 0));
    }

    let mut machine = ConstraintMachine::new();
    let record = add_row4_test_lower(&mut machine, 98_116);
    let commits = Rc::new(Cell::new(0));
    let pushes = Rc::new(Cell::new(0));
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    machine
        .proof_attempt
        .inject_query_scope_failure_after_successful_scopes(1, failure.clone());
    machine
        .defer_scheme_projection_mutation_for_test(
            ConstraintMachine::test_scheme_projection_mutation(record, Rc::clone(&commits)),
            Rc::clone(&pushes),
        )
        .unwrap();
    assert_eq!((commits.get(), pushes.get()), (1, 0));
    assert_eq!(machine.proof_terminal_failure(), Some(failure));
}

#[test]
fn cpk_sv_d_ss2_p0_row7_precommit_denial_blocks_clause_commit() {
    let mut machine = ConstraintMachine::new();
    let record = add_row4_test_lower(&mut machine, 98_118);
    machine
        .proof_attempt
        .inject_query_scope_failure(ProofFailure::TerminalLatchBusy);
    assert_eq!(
        machine.exercise_row7_clause_link_for_test(record),
        Err(ProofFailure::TerminalLatchBusy)
    );
    assert!(!machine.row7_clause_link_exists_for_test(record));
}

#[test]
fn cpk_sv_d_ss2_p0_row7_postcommit_denials_and_success_preserve_publication_boundary() {
    for failure in [
        ProofFailure::TerminalLatchBusy,
        foreign_publication_round_failure(),
    ] {
        let mut machine = ConstraintMachine::new();
        let record = add_row4_test_lower(&mut machine, 98_120);
        let publication_before = machine.provenance_epoch;
        machine
            .proof_attempt
            .inject_query_scope_failure_after_successful_scopes(1, failure);
        let panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = machine.exercise_row7_clause_link_for_test(record);
        }));
        assert_row4_row7_canary_panic(panic.expect_err("row 7 canary must panic"));
        assert!(machine.row7_clause_link_exists_for_test(record));
        assert_eq!(machine.provenance_epoch, publication_before);
    }

    let mut semantic = ConstraintMachine::new();
    let record = add_row4_test_lower(&mut semantic, 98_122);
    let publication_before = semantic.provenance_epoch;
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    semantic
        .proof_attempt
        .inject_query_scope_failure_after_successful_scopes(1, failure.clone());
    semantic.exercise_row7_clause_link_for_test(record).unwrap();
    assert!(semantic.row7_clause_link_exists_for_test(record));
    assert_eq!(semantic.proof_terminal_failure(), Some(failure));
    assert_eq!(semantic.provenance_epoch, publication_before);

    let mut success = ConstraintMachine::new();
    let record = add_row4_test_lower(&mut success, 98_124);
    success
        .exercise_row7_self_cycle_clause_link_for_test(record)
        .unwrap();
    let publication_before = success.provenance_epoch.as_u64();
    assert!(
        !success
            .scheme_projection_record_is_included_in_fresh_scope(record)
            .unwrap(),
        "the row-7 positive fixture must begin excluded"
    );
    success.exercise_row7_clause_link_for_test(record).unwrap();
    assert!(success.row7_clause_link_exists_for_test(record));
    assert!(
        success
            .scheme_projection_record_is_included_in_fresh_scope(record)
            .unwrap(),
        "the committed standalone clause must make the row-7 fixture projectable"
    );
    assert_eq!(
        success.provenance_epoch.as_u64(),
        publication_before + 1,
        "the false-to-true row-7 transition must publish exactly once"
    );
}

#[derive(Clone, Copy)]
enum AllParentClauseLinkCaller {
    FactoredProjection,
    ReplayBootstrap,
}

fn exercise_all_parent_clause_link_wrapper(
    machine: &mut ConstraintMachine,
    caller: AllParentClauseLinkCaller,
    failure: ProofFailure,
) -> bool {
    match caller {
        AllParentClauseLinkCaller::FactoredProjection => machine
            .exercise_factored_all_parent_wrapper_for_test(|machine| {
                machine.proof_attempt.inject_query_scope_failure(failure);
            }),
        AllParentClauseLinkCaller::ReplayBootstrap => machine
            .exercise_replay_bootstrap_wrapper_for_test(|machine| {
                machine.proof_attempt.inject_query_scope_failure(failure);
            }),
    }
}

fn assert_all_parent_precommit_failure_classification(caller: AllParentClauseLinkCaller) {
    for failure in [
        ProofFailure::TerminalLatchBusy,
        foreign_publication_round_failure(),
    ] {
        let mut machine = ConstraintMachine::new();

        assert!(!exercise_all_parent_clause_link_wrapper(
            &mut machine,
            caller,
            failure,
        ));
        assert_eq!(machine.proof_terminal_failure(), None);
    }

    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    let mut machine = ConstraintMachine::new();

    assert!(!exercise_all_parent_clause_link_wrapper(
        &mut machine,
        caller,
        failure.clone(),
    ));
    assert_eq!(machine.proof_terminal_failure(), Some(failure));
}

#[test]
fn cpk_sv_d_ss2_p0_factored_all_parent_wrapper_preserves_precommit_classification() {
    assert_all_parent_precommit_failure_classification(
        AllParentClauseLinkCaller::FactoredProjection,
    );
}

#[test]
fn cpk_sv_d_ss2_p0_replay_bootstrap_wrapper_preserves_precommit_classification() {
    assert_all_parent_precommit_failure_classification(AllParentClauseLinkCaller::ReplayBootstrap);
}

#[test]
fn cpk_sv_d_ss1_privacy_ui_probes_are_ci_enforced() {
    let probes = [
        (
            "cpk_sv_d_ss1_ui_prepared_command",
            "cannot construct `PreparedStructuralCommand`",
        ),
        (
            "cpk_sv_d_ss1_ui_prepared_payload",
            "enum `PreparedPayload` is private",
        ),
        (
            "cpk_sv_d_ss1_ui_active_capability",
            "of struct `ActiveProofAttempt` are private",
        ),
        (
            "cpk_sv_d_ss1_ui_capability_ticket",
            "module `reservation` is private",
        ),
        (
            "cpk_sv_d_ss1_ui_raw_structural_data",
            "field `proof` of struct `StructuralData` is private",
        ),
        (
            "cpk_sv_d_ss1_ui_noop_proof",
            "module `unchanged` is private",
        ),
        (
            "cpk_sv_d_ss1_ui_write_port",
            "no function or associated item named `new`",
        ),
        (
            "cpk_sv_d_ss1_ui_domain_port_mismatch",
            "expected `ProofOccurrencesDomain`, found `ProjectionFormulaByRecordDomain`",
        ),
        (
            "cpk_sv_d_ss1_rf_ui_raw_escape",
            "lifetime may not live long enough",
        ),
        (
            "cpk_sv_d_ss1_rf_ui_cursor_escape",
            "lifetime may not live long enough",
        ),
        (
            "cpk_sv_d_ss1_rf_ui_round_view_storage",
            "lifetime may not live long enough",
        ),
        (
            "cpk_sv_d_ss1_rf_ui_same_kernel_mutation",
            "cannot borrow `*machine` as mutable because it is also borrowed as immutable",
        ),
        (
            "cpk_sv_d_ss1_rf_ui_nonce_forge",
            "cannot initialize a tuple struct which contains private fields",
        ),
        (
            "cpk_sv_d_ss2_p0_ui_legacy_sources_private",
            "cannot find type `LegacyOnlyReadSources` in module `super::super`",
        ),
        (
            "cpk_sv_d_ss2_p0_ui_legacy_view_storage",
            "lifetime may not live long enough",
        ),
    ];
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    for (cfg, expected) in probes {
        let output = Command::new(&cargo)
            .current_dir(env!("CARGO_MANIFEST_DIR"))
            .env("RUSTC_WRAPPER", "")
            .env("RUSTFLAGS", format!("--cfg {cfg} --check-cfg=cfg({cfg})"))
            .args(["check", "-p", "infer", "--lib"])
            .output()
            .expect("run SS1 privacy UI probe");
        assert!(
            !output.status.success(),
            "UI probe unexpectedly compiled: {cfg}"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(expected),
            "UI probe {cfg} missed expected diagnostic {expected:?}:\n{stderr}",
        );
    }
}

#[test]
fn cpk_sv_d_ss2_p0_legacy_scopes_read_real_machine_fields_without_machine_reborrow() {
    let mut machine = ConstraintMachine::new();

    // Proof family: seed one occurrence independent of the other family fixtures.
    machine
        .proof_store
        .record_constraint_root(ConstraintRecordId(99), OriginId::unknown_internal());

    // Bounds family: populate both the canonical index and record arena.
    let bound_endpoint = machine.alloc_pos(Pos::Con(vec!["ss2_p0_bound".into()], Vec::new()));
    machine.bounds.add_lower(
        TypeVar(70),
        bound_endpoint,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(OriginId::unknown_internal()),
    );

    // Constraint/replay family: populate its canonical index and record arena through production.
    let constraint_lower = machine.alloc_pos(Pos::Con(vec!["ss2_p0_lower".into()], Vec::new()));
    let constraint_upper = machine.alloc_neg(Neg::Con(vec!["ss2_p0_upper".into()], Vec::new()));
    machine.subtype(
        constraint_lower,
        constraint_upper,
        OriginId::unknown_internal(),
    );

    // Row family: seed both its map and exact-key record-index faces.
    let row_owner = TypeVar(71);
    let row_filter = Subtractability::Set(vec!["ss2_p0_row".into()], Vec::new());
    machine
        .lower_filters
        .entry(row_owner)
        .or_default()
        .insert(row_filter.clone());
    machine
        .lower_filter_record_ids
        .insert((row_owner, row_filter), LowerFilterRecordId(0));

    // Identity family: the real interner populates the record and canonical index together.
    machine.intern_scheme_instantiation(
        GeneralizedSchemeRecordId(0),
        DefId(1),
        DefId(2),
        TypeVar(72),
        ProvenanceCompleteness::Complete,
    );

    let mut projection_round = machine.new_projection_evaluation_round();
    let projection_counts = machine
        .with_legacy_projection_query(&mut projection_round, |mut query| {
            assert!(!query.shadow_check_target(7));
            assert!(query.shadow_check_target(7));
            let counts = query.legacy_storage_census();
            Ok(query.complete(counts))
        })
        .expect("legacy projection scope reads production owners");
    assert!(projection_counts.proof_occurrences >= 3);
    assert_eq!(projection_counts.bound_canonical, 1);
    assert_eq!(projection_counts.bound_records, 1);
    assert_eq!(projection_counts.constraint_canonical, 1);
    assert_eq!(projection_counts.constraint_records, 1);
    assert_eq!(projection_counts.replay_drop_index, 0);
    assert_eq!(projection_counts.row_records, 0);
    assert_eq!(projection_counts.row_lower_filter_map, 1);
    assert_eq!(projection_counts.row_lower_filter_index, 1);
    assert_eq!(projection_counts.identity_records, 3);
    assert_eq!(projection_counts.scheme_instantiations, 1);
    assert_eq!(projection_counts.scheme_instantiation_index, 1);

    let mut publication_round = machine.new_publication_evaluation_round();
    let publication_counts = machine
        .with_legacy_publication_query(&mut publication_round, |mut query| {
            assert!(!query.shadow_check_target(11));
            assert!(query.shadow_check_target(11));
            let counts = query.legacy_storage_census();
            Ok(query.complete(counts))
        })
        .expect("legacy publication scope reads production owners");
    assert_eq!(publication_counts, projection_counts);
}

#[test]
fn cpk_sv_d_ss2_p0_scope_local_projectable_lowers_match_legacy_helper() {
    let mut machine = ConstraintMachine::new();
    let owner = TypeVar(73);
    let endpoint = machine.alloc_pos(Pos::Con(vec!["ss2_p0_projectable".into()], Vec::new()));
    machine.bounds.add_lower(
        owner,
        endpoint,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(OriginId::unknown_internal()),
    );

    let expected = machine
        .scheme_projectable_lowers(owner)
        .map(|entry| {
            (
                entry.record,
                entry.bound.clone(),
                entry.reason,
                entry.projection_evidence,
            )
        })
        .collect::<Vec<_>>();

    let mut round = machine.new_projection_evaluation_round();
    let actual = machine
        .with_legacy_projection_query(&mut round, |query| {
            let mut evaluation = crate::constraints::proof::ProjectionEvaluationRound::new();
            let lowers = query.scheme_projectable_lowers_in_scope(owner, &mut evaluation)?;
            let owned = lowers
                .into_iter()
                .map(|entry| {
                    (
                        entry.record,
                        entry.bound.clone(),
                        entry.reason,
                        entry.projection_evidence,
                    )
                })
                .collect::<Vec<_>>();
            drop(evaluation);
            Ok(query.complete(owned))
        })
        .expect("scope-local projectable lowers remain available");

    assert_eq!(actual, expected);
}

#[test]
fn cpk_sv_d_ss2_p0_legacy_delegates_reject_foreign_rounds_before_scope_entry() {
    let first = ConstraintMachine::new();
    let mut foreign_projection = first.new_projection_evaluation_round();
    let foreign_failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerPreflight,
    };
    foreign_projection.inject_terminal_failure_for_test(foreign_failure);
    let projection_actual = foreign_projection.attempt_nonce_for_test();
    let mut second = ConstraintMachine::new();
    let projection_expected = second
        .new_projection_evaluation_round()
        .attempt_nonce_for_test();
    let projection_invoked = std::cell::Cell::new(false);
    let projection_result = second.with_legacy_projection_query(&mut foreign_projection, |query| {
        projection_invoked.set(true);
        Ok(query.complete(()))
    });
    assert_eq!(
        projection_result,
        Err(ProofFailure::ForeignAttemptRoundState {
            expected: projection_expected,
            actual: projection_actual,
        })
    );
    assert!(!projection_invoked.get());
    assert_eq!(second.proof_terminal_failure(), None);
    assert_eq!(second.proof_attempt.query_trace(), (1, 1, 0, 0, 0));

    let mut foreign_publication = first.new_publication_evaluation_round();
    let publication_actual = foreign_publication.attempt_nonce_for_test();
    let publication_expected = second
        .new_publication_evaluation_round()
        .attempt_nonce_for_test();
    let publication_invoked = std::cell::Cell::new(false);
    let publication_result =
        second.with_legacy_publication_query(&mut foreign_publication, |query| {
            publication_invoked.set(true);
            Ok(query.complete(()))
        });
    assert_eq!(
        publication_result,
        Err(ProofFailure::ForeignAttemptRoundState {
            expected: publication_expected,
            actual: publication_actual,
        })
    );
    assert!(!publication_invoked.get());
    assert_eq!(second.proof_terminal_failure(), None);
}

#[test]
fn cpk_sv_d_ss2_p0_legacy_delegate_access_denials_remain_retryable() {
    let mut machine = ConstraintMachine::new();
    let busy = ProofFailure::TerminalLatchBusy;

    let mut projection = machine.new_projection_evaluation_round();
    let projection_result: Result<(), ProofFailure> =
        machine.with_legacy_projection_query(&mut projection, |_| Err(busy.clone()));
    assert_eq!(projection_result, Err(busy.clone()));
    assert_eq!(machine.proof_terminal_failure(), None);
    machine
        .with_legacy_projection_query(&mut projection, |query| Ok(query.complete(())))
        .expect("projection access denial stays retryable");

    let mut publication = machine.new_publication_evaluation_round();
    let publication_result: Result<(), ProofFailure> =
        machine.with_legacy_publication_query(&mut publication, |_| Err(busy.clone()));
    assert_eq!(publication_result, Err(busy));
    assert_eq!(machine.proof_terminal_failure(), None);
    machine
        .with_legacy_publication_query(&mut publication, |query| Ok(query.complete(())))
        .expect("publication access denial stays retryable");
}

#[test]
fn cpk_sv_d_ss1_rf_one_scope_shares_but_separate_scopes_always_miss() {
    let mut machine = ConstraintMachine::new();
    let mut round = machine.new_projection_evaluation_round();
    let before_snapshot = machine.proof_attempt.shadow_snapshot_value();

    let within_scope = machine
        .with_projection_query(&mut round, |mut query| {
            assert!(!query.shadow_check_target(41));
            // A second top-level target reaches the same shadow record inside one scope.
            assert!(query.shadow_check_target(41));
            let stats = query.shadow_stats();
            Ok(query.complete(stats))
        })
        .unwrap();
    assert_eq!(within_scope, (1, 1));

    let separate_scope = machine
        .with_projection_query(&mut round, |mut query| {
            assert!(!query.shadow_check_target(41));
            let stats = query.shadow_stats();
            Ok(query.complete(stats))
        })
        .unwrap();
    assert_eq!(separate_scope, (1, 0));
    assert_eq!(
        machine.proof_attempt.shadow_snapshot_value(),
        before_snapshot
    );
}

#[test]
fn cpk_sv_d_ss1_rf_publication_scope_state_is_invocation_local() {
    let mut machine = ConstraintMachine::new();
    let mut round = machine.new_publication_evaluation_round();
    let first = machine
        .with_publication_projection_query(&mut round, |mut query| {
            assert!(!query.shadow_check_target(7));
            assert!(query.shadow_check_target(7));
            let stats = query.shadow_stats();
            Ok(query.complete(stats))
        })
        .unwrap();
    let second = machine
        .with_publication_projection_query(&mut round, |mut query| {
            assert!(!query.shadow_check_target(7));
            let stats = query.shadow_stats();
            Ok(query.complete(stats))
        })
        .unwrap();
    assert_eq!(first, (1, 1));
    assert_eq!(second, (1, 0));
}

#[test]
fn cpk_sv_d_ss1_rf_foreign_projection_round_is_access_denial() {
    let first = ConstraintMachine::new();
    let mut foreign_round = first.new_projection_evaluation_round();
    let foreign_failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerPreflight,
    };
    foreign_round.inject_terminal_failure_for_test(foreign_failure);
    let actual = foreign_round.attempt_nonce_for_test();
    let mut second = ConstraintMachine::new();
    let expected = second
        .new_projection_evaluation_round()
        .attempt_nonce_for_test();
    let invoked = std::cell::Cell::new(false);

    let result = second.with_projection_query(&mut foreign_round, |query| {
        invoked.set(true);
        Ok(query.complete(()))
    });
    assert_eq!(
        result,
        Err(ProofFailure::ForeignAttemptRoundState { expected, actual })
    );
    assert!(!invoked.get());
    assert_eq!(second.proof_attempt.query_trace(), (1, 1, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_rf_foreign_publication_round_is_access_denial() {
    let mut first = ConstraintMachine::new();
    let mut foreign_round = first.new_publication_evaluation_round();
    let warmed = first
        .with_publication_projection_query(&mut foreign_round, |mut query| {
            assert!(!query.shadow_check_target(71));
            let stats = query.shadow_stats();
            Ok(query.complete(stats))
        })
        .unwrap();
    assert_eq!(warmed, (1, 0));
    // SealingIncomplete deliberately retains no memo/override payload. The ordering proof is
    // therefore the K2 trace below: authentication must fail before the wrapper enters any
    // authenticated round-state path, irrespective of this prior successful K1 invocation.
    let actual = foreign_round.attempt_nonce_for_test();
    let mut second = ConstraintMachine::new();
    let expected = second
        .new_publication_evaluation_round()
        .attempt_nonce_for_test();
    let invoked = std::cell::Cell::new(false);

    let result = second.with_publication_projection_query(&mut foreign_round, |query| {
        invoked.set(true);
        Ok(query.complete(()))
    });
    assert_eq!(
        result,
        Err(ProofFailure::ForeignAttemptRoundState { expected, actual })
    );
    assert!(!invoked.get());
    let trace = second.proof_attempt.query_trace();
    assert_eq!(
        trace.2, 0,
        "foreign publication round entered its authenticated state path"
    );
    assert_eq!(trace.3, 0, "foreign publication query scope was entered");
    assert_eq!(trace, (1, 1, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_rf_nonce_exhaustion_uses_fresh_ephemeral_state() {
    let mut machine = ConstraintMachine::new();
    machine.proof_attempt = ProofAttemptKernel::new_reuse_disabled_for_test();
    let mut round = machine.new_projection_evaluation_round();
    assert_eq!(round.attempt_nonce_for_test(), None);

    for _ in 0..2 {
        let stats = machine
            .with_projection_query(&mut round, |mut query| {
                assert!(!query.shadow_check_target(9));
                let stats = query.shadow_stats();
                Ok(query.complete(stats))
            })
            .unwrap();
        assert_eq!(stats, (1, 0));
    }
}

#[test]
fn cpk_sv_d_ss1_rf_publication_nonce_exhaustion_uses_fresh_ephemeral_state() {
    let mut machine = ConstraintMachine::new();
    machine.proof_attempt = ProofAttemptKernel::new_reuse_disabled_for_test();
    let mut round = machine.new_publication_evaluation_round();
    assert_eq!(round.attempt_nonce_for_test(), None);

    for _ in 0..2 {
        let stats = machine
            .with_publication_projection_query(&mut round, |mut query| {
                assert!(!query.shadow_check_target(19));
                let stats = query.shadow_stats();
                Ok(query.complete(stats))
            })
            .unwrap();
        assert_eq!(stats, (1, 0));
    }
}

#[test]
fn cpk_sv_d_ss1_rf_query_failure_uses_exact_proof_failure_surface() {
    let mut machine = ConstraintMachine::new();
    let mut round = machine.new_projection_evaluation_round();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    let result: Result<(), ProofFailure> =
        machine.with_projection_query(&mut round, |_| Err(failure.clone()));
    assert_eq!(result, Err(failure.clone()));

    let result = machine.with_projection_query(&mut round, |query| Ok(query.complete(())));
    assert_eq!(result, Err(failure));
}

#[test]
fn cpk_sv_d_ss1_rf_access_denials_are_returned_without_poisoning_the_attempt() {
    let mut machine = ConstraintMachine::new();
    let mut projection = machine.new_projection_evaluation_round();
    let busy = ProofFailure::TerminalLatchBusy;
    assert!(!busy.requires_attempt_terminal());
    let result: Result<(), ProofFailure> =
        machine.with_projection_query(&mut projection, |_| Err(busy.clone()));
    assert_eq!(result, Err(busy));
    assert_eq!(machine.proof_terminal_failure(), None);
    machine
        .with_projection_query(&mut projection, |query| Ok(query.complete(())))
        .unwrap();

    let mut publication = machine.new_publication_evaluation_round();
    let foreign = ProofFailure::ForeignAttemptRoundState {
        expected: publication.attempt_nonce_for_test(),
        actual: None,
    };
    assert!(!foreign.requires_attempt_terminal());
    let result: Result<(), ProofFailure> =
        machine.with_publication_projection_query(&mut publication, |_| Err(foreign.clone()));
    assert_eq!(result, Err(foreign));
    assert_eq!(machine.proof_terminal_failure(), None);
    machine
        .with_publication_projection_query(&mut publication, |query| Ok(query.complete(())))
        .unwrap();

    assert!(
        ProofFailure::ResourceExhausted {
            operation: ProofOperation::ProjectLowerEvaluation,
        }
        .requires_attempt_terminal()
    );
}

#[test]
#[should_panic(expected = "already mutably borrowed")]
fn cpk_sv_d_ss1_rf_genuine_terminal_latch_conflict_panics() {
    let machine = ConstraintMachine::new();
    machine
        .proof_attempt
        .trigger_query_latch_conflict_for_test();
}

#[test]
fn cpk_sv_d_ss1_rf_publication_closure_failure_uses_common_terminal_branch() {
    let mut machine = ConstraintMachine::new();
    let mut round = machine.new_publication_evaluation_round();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    let result: Result<(), ProofFailure> =
        machine.with_publication_projection_query(&mut round, |_| Err(failure.clone()));
    assert_eq!(result, Err(failure.clone()));
    assert_eq!(machine.proof_terminal_failure(), Some(failure.clone()));

    let invoked = std::cell::Cell::new(false);
    let result = machine.with_publication_projection_query(&mut round, |query| {
        invoked.set(true);
        Ok(query.complete(()))
    });
    assert_eq!(result, Err(failure));
    assert!(!invoked.get());
}

#[test]
fn cpk_sv_d_ss1_rf_authenticated_scope_construction_failure_uses_common_branch() {
    let mut machine = ConstraintMachine::new();
    let mut round = machine.new_projection_evaluation_round();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerPreflight,
    };
    machine
        .proof_attempt
        .inject_query_scope_failure(failure.clone());
    let invoked = std::cell::Cell::new(false);
    let result: Result<(), ProofFailure> = machine.with_projection_query(&mut round, |query| {
        invoked.set(true);
        Ok(query.complete(()))
    });
    assert_eq!(result, Err(failure.clone()));
    assert!(!invoked.get());
    assert_eq!(machine.proof_terminal_failure(), Some(failure));
}

#[test]
fn cpk_sv_d_ss1_rf_publication_scope_construction_failure_uses_common_branch() {
    let mut machine = ConstraintMachine::new();
    let mut round = machine.new_publication_evaluation_round();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerPreflight,
    };
    machine
        .proof_attempt
        .inject_query_scope_failure(failure.clone());
    let invoked = std::cell::Cell::new(false);
    let result: Result<(), ProofFailure> =
        machine.with_publication_projection_query(&mut round, |query| {
            invoked.set(true);
            Ok(query.complete(()))
        });
    assert_eq!(result, Err(failure.clone()));
    assert!(!invoked.get());
    assert_eq!(machine.proof_terminal_failure(), Some(failure));
}

#[test]
fn cpk_sv_d_ss1_rf_scope_checks_are_once_per_scope_not_per_getter() {
    let mut machine = ConstraintMachine::new();
    let mut projection = machine.new_projection_evaluation_round();
    machine.proof_attempt.reset_query_trace();
    machine
        .with_projection_query(&mut projection, |query| Ok(query.complete(())))
        .unwrap();
    let projection_without_getters = machine.proof_attempt.query_trace();

    machine.proof_attempt.reset_query_trace();
    machine
        .with_projection_query(&mut projection, |query| {
            assert!(query.view().is_empty_shadow());
            assert!(query.view().is_empty_shadow());
            Ok(query.complete(()))
        })
        .unwrap();
    let projection_with_getters = machine.proof_attempt.query_trace();
    assert_eq!(projection_without_getters, (2, 2, 1, 1, 1));
    assert_eq!(projection_with_getters, projection_without_getters);

    let mut publication = machine.new_publication_evaluation_round();
    machine.proof_attempt.reset_query_trace();
    machine
        .with_publication_projection_query(&mut publication, |query| Ok(query.complete(())))
        .unwrap();
    let publication_without_getters = machine.proof_attempt.query_trace();

    machine.proof_attempt.reset_query_trace();
    machine
        .with_publication_projection_query(&mut publication, |query| {
            assert!(query.view().is_empty_shadow());
            assert!(query.view().is_empty_shadow());
            Ok(query.complete(()))
        })
        .unwrap();
    let publication_with_getters = machine.proof_attempt.query_trace();
    assert_eq!(publication_without_getters, (2, 2, 1, 1, 1));
    assert_eq!(publication_with_getters, publication_without_getters);
}

#[test]
fn cpk_sv_d_ss1_rf_post_scope_kernel_recheck_precedes_publication() {
    let mut machine = ConstraintMachine::new();
    let mut round = machine.new_projection_evaluation_round();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    machine
        .proof_attempt
        .inject_post_scope_failure(failure.clone());
    machine.proof_attempt.reset_query_trace();
    let invoked = std::cell::Cell::new(false);
    let result = machine.with_projection_query(&mut round, |query| {
        invoked.set(true);
        Ok(query.complete(99_u64))
    });
    assert!(invoked.get());
    assert_eq!(result, Err(failure));
    assert_eq!(machine.proof_attempt.query_trace(), (2, 1, 1, 1, 1));
}

#[test]
fn cpk_sv_d_ss1_rf_publication_post_scope_kernel_recheck_precedes_publication() {
    let mut machine = ConstraintMachine::new();
    let mut round = machine.new_publication_evaluation_round();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    machine
        .proof_attempt
        .inject_post_scope_failure(failure.clone());
    machine.proof_attempt.reset_query_trace();
    let invoked = std::cell::Cell::new(false);
    let result = machine.with_publication_projection_query(&mut round, |query| {
        invoked.set(true);
        Ok(query.complete(99_u64))
    });
    assert!(invoked.get());
    assert_eq!(result, Err(failure));
    assert_eq!(machine.proof_attempt.query_trace(), (2, 1, 1, 1, 1));
}

#[test]
fn cpk_sv_d_ss1_all_29_shadow_commands_finish_changed() {
    let mut kernel = ProofAttemptKernel::new();
    kernel
        .try_with_structural_preparation_scope(|scope| {
            for intent in ALL_INTENTS {
                let prepared = scope.prepare(intent)?;
                assert!(scope.commit(prepared)?.was_changed());
            }
            Ok(())
        })
        .unwrap();

    let (family_counts, snapshot, arena, tickets, outstanding, pins) =
        kernel.shadow_state().shadow_counts();
    assert_eq!(family_counts, [13, 4, 4, 7, 2]);
    assert_eq!(snapshot, 29);
    assert_eq!((arena, tickets, outstanding, pins), (0, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_scope_drop_and_explicit_cancel_release_prepared_tickets() {
    let mut kernel = ProofAttemptKernel::new();
    kernel
        .try_with_structural_preparation_scope(|scope| {
            let cancelled = scope.prepare(I::AdmitBound)?;
            scope.cancel(cancelled)?;
            let _dropped_with_scope = scope.prepare(I::AdmitConstraint)?;
            Ok(())
        })
        .unwrap();
    let (_, _, arena, tickets, outstanding, pins) = kernel.shadow_state().shadow_counts();
    assert_eq!((arena, tickets, outstanding, pins), (0, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_in_flight_guard_releases_on_early_error() {
    let mut kernel = ProofAttemptKernel::new();
    let result = kernel.try_with_structural_preparation_scope(|scope| {
        let prepared = scope.prepare(I::MoveUpperClaim)?;
        scope.commit_with_injected_exit(prepared, true, false)?;
        Ok(())
    });
    assert!(result.is_err());
    let (_, _, arena, tickets, outstanding, pins) = kernel.shadow_state().shadow_counts();
    assert_eq!((arena, tickets, outstanding, pins), (0, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_in_flight_guard_releases_on_panic() {
    let mut kernel = ProofAttemptKernel::new();
    let panic = catch_unwind(AssertUnwindSafe(|| {
        let _ = kernel.try_with_structural_preparation_scope(|scope| {
            let prepared = scope.prepare(I::TransitionLiveCoverage)?;
            scope.commit_with_injected_exit(prepared, false, true)?;
            Ok(())
        });
    }));
    assert!(panic.is_err());
    let (_, _, arena, tickets, outstanding, pins) = kernel.shadow_state().shadow_counts();
    assert_eq!((arena, tickets, outstanding, pins), (0, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_terminal_attempt_rejects_shadow_preparation() {
    let mut kernel = ProofAttemptKernel::new();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerPreflight,
    };
    kernel.mark_terminal_failure(ProofOperation::ProjectLowerPreflight, failure.clone());
    let result = kernel.try_with_structural_preparation_scope(|_| Ok(()));
    assert_eq!(result, Err(ProofAccessError::Terminal(failure)));
    assert_eq!(kernel.shadow_state().shadow_counts().1, 0);
}

#[test]
fn cpk_sv_d_ss1_multi_domain_ticket_flows_through_verified_ports() {
    let mut kernel = ProofAttemptKernel::new();
    kernel
        .try_with_structural_preparation_scope(|scope| {
            let prepared = scope.prepare(I::AdmitProjectionFormulaClause)?;
            let (_, _, arena, tickets, outstanding, pins) = scope.shadow_counts();
            assert_eq!((arena, tickets, outstanding, pins), (1, 1, 2, 0));
            assert!(scope.commit(prepared)?.was_changed());
            Ok(())
        })
        .unwrap();
    let (publications, snapshot, arena, tickets, outstanding, pins) =
        kernel.shadow_state().shadow_counts();
    assert_eq!(publications, [2, 0, 0, 0, 0]);
    assert_eq!(snapshot, 1);
    assert_eq!((arena, tickets, outstanding, pins), (0, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_gateway_rejects_a_reserved_operation_for_the_wrong_domain() {
    let mut kernel = ProofAttemptKernel::new();
    kernel
        .try_with_structural_preparation_scope(|scope| {
            let prepared = scope.prepare(I::AppendProofOccurrence)?;
            scope.corrupt_first_reserved_domain_for_test(&prepared)?;
            assert_eq!(
                scope.commit(prepared),
                Err(ProofAccessError::InvalidReservedOperation)
            );
            Ok(())
        })
        .unwrap();
    let (publications, snapshot, arena, tickets, outstanding, pins) =
        kernel.shadow_state().shadow_counts();
    assert_eq!(publications, [0; 5]);
    assert_eq!(snapshot, 0);
    assert_eq!((arena, tickets, outstanding, pins), (0, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_multi_domain_verification_finishes_before_first_publication() {
    let mut kernel = ProofAttemptKernel::new();
    kernel
        .try_with_structural_preparation_scope(|scope| {
            let prepared = scope.prepare(I::AdmitProjectionFormulaClause)?;
            scope.corrupt_projection_formula_secondary_domain_for_test(&prepared)?;
            assert_eq!(
                scope.commit(prepared),
                Err(ProofAccessError::InvalidReservedOperation)
            );
            Ok(())
        })
        .unwrap();
    let (publications, snapshot, arena, tickets, outstanding, pins) =
        kernel.shadow_state().shadow_counts();
    assert_eq!(publications, [0; 5]);
    assert_eq!(snapshot, 0);
    assert_eq!((arena, tickets, outstanding, pins), (0, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_snapshot_exhaustion_fails_before_publication() {
    let mut kernel = ProofAttemptKernel::new();
    kernel
        .try_with_structural_preparation_scope(|scope| {
            scope.exhaust_snapshot_for_test();
            let prepared = scope.prepare(I::AppendProofOccurrence)?;
            assert_eq!(
                scope.commit(prepared),
                Err(ProofAccessError::StructuralSnapshotExhausted)
            );
            Ok(())
        })
        .unwrap();
    let (publications, snapshot, arena, tickets, outstanding, pins) =
        kernel.shadow_state().shadow_counts();
    assert_eq!(publications, [0; 5]);
    assert_eq!(snapshot, u64::MAX);
    assert_eq!((arena, tickets, outstanding, pins), (0, 0, 0, 0));
}

#[test]
fn cpk_sv_d_ss1_active_check_failure_keeps_raii_ownership_until_guard_take() {
    let mut kernel = ProofAttemptKernel::new();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerPreflight,
    };
    let result = kernel.try_with_structural_preparation_scope(|scope| {
        let prepared = scope.prepare(I::MoveUpperClaim)?;
        scope.inject_terminal_failure(failure.clone());
        assert_eq!(
            scope.commit(prepared),
            Err(ProofAccessError::Terminal(failure.clone()))
        );
        Ok(())
    });
    assert_eq!(result, Ok(()));
    let (_, snapshot, arena, tickets, outstanding, pins) = kernel.shadow_state().shadow_counts();
    assert_eq!(snapshot, 0);
    assert_eq!((arena, tickets, outstanding, pins), (0, 0, 0, 0));
}
