use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::Command;
use std::time::{Duration, Instant};
use std::{cell::Cell, rc::Rc};

use poly::expr::DefId;
use poly::roles::{RoleConstraint, RoleConstraintArg};
use poly::types::{Neg, NegId, Neu, NeuId, Pos, PosId, SubtractId, Subtractability, TypeVar};
use rustc_hash::FxHashSet;

use super::commands::StructuralMutationIntent as I;
use super::{ProofAccessError, ProofAttemptKernel};
use crate::analysis::begin_owner_dependency_reads;
use crate::constraints::mutation::DependencyKey;
use crate::constraints::proof::{ProofFailure, ProofOperation};
use crate::constraints::{
    BoundDerivation, BoundRecordId, ConstraintEffectFamily, ConstraintMachine, ConstraintRecordId,
    ConstraintWeights, DerivedUnaryCarrier, GeneralizationParent, GeneralizedSchemeRecordId,
    GeneralizedWitnessRole, LowerFilterRecordId, OriginId, ProjectionProofCarrier, ProofPremise,
    ProvenanceCompleteness, RecordProofClause, RecordProofClauseLinkAdmission, RowDerivationId,
    SchemeProjectionProof, SchemeProjectionProofSupport, StructuralDerivation,
    StructuralDerivationRule, SubtractFact, TypeLevel, UnweightedRowReductionRecordId,
    UpperReplayClaimId, UpperReplayClaimKind,
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

struct Row5ProductionPathFixture {
    machine: ConstraintMachine,
    result: ConstraintRecordId,
    lower: PosId,
    upper: NegId,
    parent_claim: UpperReplayClaimId,
    derivation: RowDerivationId,
    dependents: [BoundRecordId; 2],
}

fn row5_production_path_fixture() -> Row5ProductionPathFixture {
    let mut machine = crate::constraints::with_semantic_execution_snapshot_capture_for_new_machines(
        ConstraintMachine::new,
    );
    let source = TypeVar(98_150);
    let target = TypeVar(98_151);
    let parent_source = TypeVar(98_152);
    let lower = machine.alloc_pos(Pos::Var(source));
    let upper = machine.alloc_neg(Neg::Var(target));
    let origin = OriginId::unknown_internal();
    assert!(machine.enqueue_root_subtype(
        lower,
        ConstraintWeights::empty(),
        upper,
        origin,
    ));
    let result = machine
        .constraint_record_id(lower, ConstraintWeights::empty(), upper)
        .expect("the row-5 fixture constraint must be canonical");
    let primary = machine
        .bounds
        .add_lower(
            target,
            lower,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(result),
        )
        .id;
    let parent_record = machine
        .bounds
        .add_upper(
            parent_source,
            upper,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(origin),
        )
        .id;
    let registration = machine.original_upper_replay_claim(
        parent_record,
        ConstraintRecordId(98_153),
        UpperReplayClaimKind::Direct,
    );
    machine
        .apply_scheme_projection_mutation(registration.scheme_projection_mutation)
        .expect("the row-5 fixture claim support must commit");
    machine
        .exercise_row7_self_cycle_clause_link_for_test(primary)
        .expect("the row-5 fixture primary exclusion must commit");
    assert!(!machine.scheme_projection_record_is_included(primary));

    let dependents = [98_154, 98_156].map(|seed| {
        let dependent = add_row4_test_lower(&mut machine, seed);
        let carrier = ProjectionProofCarrier::Origin(origin);
        let support = SchemeProjectionProofSupport::Independent(carrier);
        machine.proof_store.record_projection_supports(
            dependent,
            &[SchemeProjectionProof {
                lower_record: dependent,
                support,
            }],
        );
        machine.register_cpk_projection_clause_for_test(
            dependent,
            RecordProofClauseLinkAdmission::independent(
                support,
                RecordProofClause::DerivedUnary {
                    carrier: DerivedUnaryCarrier::Structural(StructuralDerivation {
                        parent: result,
                        rule: StructuralDerivationRule::FunctionReturn,
                    }),
                    premise: ProofPremise::Constraint(result),
                },
            ),
        );
        assert!(!machine.scheme_projection_record_is_included(dependent));
        dependent
    });
    assert_eq!(machine.proof_store.qualified_parent_count(result), 0);

    Row5ProductionPathFixture {
        machine,
        result,
        lower,
        upper,
        parent_claim: registration.claim,
        derivation: RowDerivationId(98_157),
        dependents,
    }
}

fn row5_semantic_snapshot(
    machine: &ConstraintMachine,
) -> crate::constraints::SemanticExecutionSnapshot {
    let scc = crate::scc::SccMachine::new();
    machine.semantic_execution_snapshot(
        crate::constraints::SccExecutionSnapshot::new(scc.stats(), Vec::new()),
        crate::constraints::SemanticOutputSnapshot::default(),
    )
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
                machine
                    .proof_attempt
                    .inject_query_scope_failure_after_successful_scopes(2, failure);
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
// Coverage note: this proves one fence drain, correct aggregate transitions, and correct
// owner targeting -- it does not prove the fence's row-5 intent is published as exactly one
// semantic publication action (a regression that split it into multiple per-owner publish
// calls during the same drain could still pass). Accepted as a documented residual gap;
// production behavior itself has been independently reviewed clean across 4 rounds.
fn cpk_sv_d_ss2_p0_row5_real_qualified_admission_commits_then_publishes_three_transitions_once() {
    let mut fixture = row5_production_path_fixture();
    let before = row5_semantic_snapshot(&fixture.machine).publication;
    fixture.machine.reset_row5_publication_trace_for_test();

    fixture
        .machine
        .register_valid_reduction_route_claim_parent_for_test(
            fixture.lower,
            fixture.upper,
            fixture.derivation,
            fixture.parent_claim,
        );

    assert_eq!(
        fixture
            .machine
            .proof_store
            .qualified_parent_count(fixture.result),
        1,
        "the authoritative replay-qualified-parent commit must happen exactly once",
    );
    assert!(fixture
        .dependents
        .iter()
        .all(|record| fixture.machine.scheme_projection_record_is_included(*record)));
    assert_eq!(
        fixture.machine.row5_publication_trace_for_test(),
        (1, 1, 1),
        "row 5 must construct one lane, append its intent once, and publish its fence once",
    );
    let after = row5_semantic_snapshot(&fixture.machine).publication;
    let transitions = &after.projectability_transitions[before.projectability_transitions.len()..];
    assert_eq!(transitions.len(), 3);
    assert!(transitions
        .iter()
        .all(|transition| !transition.was_included && transition.is_included));
    assert!(fixture.dependents.iter().all(|record| {
        transitions.iter().any(|transition| {
            transition.lower_record == *record
                && !transition.was_included
                && transition.is_included
        })
    }));
    let invalidations = &after.owner_invalidations[before.owner_invalidations.len()..];
    let mut expected_owners = transitions
        .iter()
        .map(|transition| {
            fixture
                .machine
                .bounds
                .record(transition.lower_record)
                .expect("every production-path transition must retain its owner")
                .owner()
        })
        .collect::<Vec<_>>();
    expected_owners.sort_unstable_by_key(|owner| owner.0);
    let mut invalidated_owners = invalidations
        .iter()
        .map(|invalidation| invalidation.owner)
        .collect::<Vec<_>>();
    invalidated_owners.sort_unstable_by_key(|owner| owner.0);
    assert_eq!(invalidated_owners, expected_owners);
}

#[test]
fn cpk_sv_d_ss2_p0_row5_real_snapshot_map_constructs_one_shared_lane() {
    let mut fixture = row5_production_path_fixture();
    fixture.machine.reset_row5_publication_trace_for_test();

    fixture
        .machine
        .register_valid_reduction_route_claim_parent_for_test(
            fixture.lower,
            fixture.upper,
            fixture.derivation,
            fixture.parent_claim,
        );

    assert!(fixture
        .dependents
        .iter()
        .all(|record| fixture.machine.scheme_projection_record_is_included(*record)));
    assert_eq!(
        fixture.machine.row5_publication_trace_for_test().0,
        1,
        "one row-5 evaluator lane must serve the complete multi-record snapshot",
    );
}

#[test]
fn cpk_sv_d_ss2_p0_row6_real_snapshot_producer_uses_one_precommit_lane() {
    let mut fixture = row5_production_path_fixture();
    fixture
        .machine
        .reset_row6_publication_lane_trace_for_test();

    fixture
        .machine
        .register_valid_reduction_route_claim_parent_for_test(
            fixture.lower,
            fixture.upper,
            fixture.derivation,
            fixture.parent_claim,
        );

    assert_eq!(
        fixture
            .machine
            .proof_store
            .qualified_parent_count(fixture.result),
        1,
        "the real qualified-parent commit must follow the row-6 snapshot",
    );
    assert!(fixture
        .dependents
        .iter()
        .all(|record| fixture.machine.scheme_projection_record_is_included(*record)));
    let (lane_constructions, mut evaluated_records) =
        fixture.machine.row6_publication_lane_trace_for_test();
    evaluated_records.sort_unstable_by_key(|record| record.0);
    let mut expected_records = fixture.dependents.to_vec();
    expected_records.sort_unstable_by_key(|record| record.0);
    assert_eq!(lane_constructions, 1);
    assert_eq!(
        evaluated_records, expected_records,
        "the one row-6 lane must evaluate every record in the real dependent set exactly once",
    );
}

#[test]
fn cpk_sv_d_ss2_p0_row6_real_precommit_denial_blocks_qualified_parent_commit() {
    for failure in [
        ProofFailure::TerminalLatchBusy,
        foreign_publication_round_failure(),
    ] {
        let mut fixture = row5_production_path_fixture();
        fixture
            .machine
            .reset_row6_publication_lane_trace_for_test();
        fixture.machine.reset_row5_publication_trace_for_test();
        fixture
            .machine
            .proof_attempt
            .inject_query_scope_failure(failure);

        fixture
            .machine
            .register_valid_reduction_route_claim_parent_for_test(
                fixture.lower,
                fixture.upper,
                fixture.derivation,
                fixture.parent_claim,
            );

        assert_eq!(
            fixture
                .machine
                .proof_store
                .qualified_parent_count(fixture.result),
            0,
        );
        assert_eq!(
            fixture.machine.row6_publication_lane_trace_for_test(),
            (0, Vec::new())
        );
        assert_eq!(fixture.machine.row5_publication_trace_for_test(), (0, 0, 0));
        assert_eq!(fixture.machine.proof_terminal_failure(), None);
    }

    let mut fixture = row5_production_path_fixture();
    fixture
        .machine
        .reset_row6_publication_lane_trace_for_test();
    fixture.machine.reset_row5_publication_trace_for_test();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    fixture
        .machine
        .inject_row6_caller_failure_for_test(failure.clone());

    fixture
        .machine
        .register_valid_reduction_route_claim_parent_for_test(
            fixture.lower,
            fixture.upper,
            fixture.derivation,
            fixture.parent_claim,
        );

    assert_eq!(
        fixture
            .machine
            .proof_store
            .qualified_parent_count(fixture.result),
        0,
    );
    let (lane_constructions, evaluated_records) =
        fixture.machine.row6_publication_lane_trace_for_test();
    assert_eq!(lane_constructions, 1);
    assert_eq!(evaluated_records.len(), fixture.dependents.len());
    assert_eq!(fixture.machine.row5_publication_trace_for_test(), (0, 0, 0));
    assert_eq!(fixture.machine.proof_terminal_failure(), Some(failure));
}

#[test]
fn cpk_sv_d_ss2_p0_row6_precommit_denial_blocks_add_lower_bound_commit() {
    for failure in [
        ProofFailure::TerminalLatchBusy,
        foreign_publication_round_failure(),
    ] {
        let mut fixture = row5_production_path_fixture();
        let target = TypeVar(98_160);
        let endpoint = fixture.machine.alloc_pos(Pos::Var(TypeVar(98_161)));
        fixture.machine.register_type_var(target, TypeLevel::root());
        fixture
            .machine
            .reset_row6_publication_lane_trace_for_test();
        fixture
            .machine
            .proof_attempt
            .inject_query_scope_failure(failure);

        fixture.machine.add_lower_bound(
            target,
            endpoint,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(fixture.result),
        );

        assert!(fixture.machine.bounds.of(target).is_none());
        assert_eq!(
            fixture.machine.row6_publication_lane_trace_for_test(),
            (0, Vec::new())
        );
        assert_eq!(fixture.machine.proof_terminal_failure(), None);
    }

    let mut fixture = row5_production_path_fixture();
    let target = TypeVar(98_162);
    let endpoint = fixture.machine.alloc_pos(Pos::Var(TypeVar(98_163)));
    fixture.machine.register_type_var(target, TypeLevel::root());
    fixture
        .machine
        .reset_row6_publication_lane_trace_for_test();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    fixture
        .machine
        .inject_row6_caller_failure_for_test(failure.clone());

    fixture.machine.add_lower_bound(
        target,
        endpoint,
        ConstraintWeights::empty(),
        BoundDerivation::Constraint(fixture.result),
    );

    assert!(fixture.machine.bounds.of(target).is_none());
    assert_eq!(fixture.machine.row6_publication_lane_trace_for_test().0, 1);
    assert_eq!(fixture.machine.proof_terminal_failure(), Some(failure));
}

#[test]
fn cpk_sv_d_ss2_p0_row7_add_lower_postcommit_snapshot_uses_one_lane_for_every_record() {
    let mut fixture = row5_production_path_fixture();
    let target = TypeVar(98_164);
    let endpoint = fixture.machine.alloc_pos(Pos::Var(TypeVar(98_165)));
    fixture.machine.register_type_var(target, TypeLevel::root());
    let before = row5_semantic_snapshot(&fixture.machine).publication;
    fixture
        .machine
        .reset_row7_snapshot_publication_lane_trace_for_test();

    fixture.machine.add_lower_bound(
        target,
        endpoint,
        ConstraintWeights::empty(),
        BoundDerivation::Constraint(fixture.result),
    );

    assert!(
        fixture.machine.bounds.of(target).is_some(),
        "the real add-lower commit must precede the post-commit snapshot evaluation",
    );
    let (lane_constructions, mut evaluated_records) = fixture
        .machine
        .row7_snapshot_publication_lane_trace_for_test();
    evaluated_records.sort_unstable_by_key(|record| record.0);
    let mut expected_records = fixture.dependents.to_vec();
    expected_records.sort_unstable_by_key(|record| record.0);
    assert_eq!(lane_constructions, 1);
    assert_eq!(
        evaluated_records, expected_records,
        "one row-7 post-commit lane must evaluate every record from the real pre-commit snapshot exactly once",
    );

    let after = row5_semantic_snapshot(&fixture.machine).publication;
    let transitions = &after.projectability_transitions[before.projectability_transitions.len()..];
    assert_eq!(transitions.len(), expected_records.len());
    assert!(transitions.iter().all(|transition| {
        expected_records.contains(&transition.lower_record)
            && !transition.was_included
            && transition.is_included
    }));
    let mut expected_owners = expected_records
        .iter()
        .map(|record| {
            fixture
                .machine
                .bounds
                .record(*record)
                .expect("every transitioned record must retain its owner")
                .owner()
        })
        .collect::<Vec<_>>();
    expected_owners.sort_unstable_by_key(|owner| owner.0);
    let mut invalidated_owners = after.owner_invalidations
        [before.owner_invalidations.len()..]
        .iter()
        .map(|invalidation| invalidation.owner)
        .collect::<Vec<_>>();
    invalidated_owners.sort_unstable_by_key(|owner| owner.0);
    assert_eq!(invalidated_owners, expected_owners);
}

#[test]
fn cpk_sv_d_ss2_p0_row7_add_lower_postcommit_denials_publish_nothing() {
    for (offset, failure) in [
        ProofFailure::TerminalLatchBusy,
        foreign_publication_round_failure(),
    ]
    .into_iter()
    .enumerate()
    {
        let mut fixture = row5_production_path_fixture();
        let target = TypeVar(98_166 + offset as u32 * 2);
        let endpoint = fixture
            .machine
            .alloc_pos(Pos::Var(TypeVar(target.0 + 1)));
        fixture.machine.register_type_var(target, TypeLevel::root());
        let before = row5_semantic_snapshot(&fixture.machine).publication;
        fixture
            .machine
            .reset_row7_snapshot_publication_lane_trace_for_test();
        fixture
            .machine
            .proof_attempt
            .inject_query_scope_failure_after_successful_scopes(1, failure);

        let panic = catch_unwind(AssertUnwindSafe(|| {
            fixture.machine.add_lower_bound(
                target,
                endpoint,
                ConstraintWeights::empty(),
                BoundDerivation::Constraint(fixture.result),
            );
        }));

        assert_row4_row7_canary_panic(
            panic.expect_err("the row-7 add-lower post-commit canary must panic"),
        );
        assert!(
            fixture.machine.bounds.of(target).is_some(),
            "the authoritative add-lower commit must precede the denied post-commit scope",
        );
        assert_eq!(
            fixture
                .machine
                .row7_snapshot_publication_lane_trace_for_test(),
            (0, Vec::new()),
        );
        assert_eq!(fixture.machine.proof_terminal_failure(), None);
        let after = row5_semantic_snapshot(&fixture.machine).publication;
        assert_eq!(after.owner_invalidations, before.owner_invalidations);
        assert_eq!(
            after.projectability_transitions,
            before.projectability_transitions,
        );
    }

    let mut fixture = row5_production_path_fixture();
    let target = TypeVar(98_170);
    let endpoint = fixture.machine.alloc_pos(Pos::Var(TypeVar(98_171)));
    fixture.machine.register_type_var(target, TypeLevel::root());
    let before = row5_semantic_snapshot(&fixture.machine).publication;
    fixture
        .machine
        .reset_row7_snapshot_publication_lane_trace_for_test();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    fixture
        .machine
        .proof_attempt
        .inject_query_scope_failure_after_successful_scopes(1, failure.clone());

    fixture.machine.add_lower_bound(
        target,
        endpoint,
        ConstraintWeights::empty(),
        BoundDerivation::Constraint(fixture.result),
    );

    assert!(fixture.machine.bounds.of(target).is_some());
    assert_eq!(fixture.machine.proof_terminal_failure(), Some(failure));
    assert_eq!(
        fixture
            .machine
            .row7_snapshot_publication_lane_trace_for_test(),
        (0, Vec::new()),
    );
    let after = row5_semantic_snapshot(&fixture.machine).publication;
    assert_eq!(after.owner_invalidations, before.owner_invalidations);
    assert_eq!(
        after.projectability_transitions,
        before.projectability_transitions,
    );
}

#[test]
fn cpk_sv_d_ss2_p0_row6_precommit_denial_blocks_replay_qualified_parent_commit() {
    for failure in [
        ProofFailure::TerminalLatchBusy,
        foreign_publication_round_failure(),
    ] {
        let mut machine = ConstraintMachine::new();
        machine.reset_row6_publication_lane_trace_for_test();

        let committed = machine.exercise_row6_replay_qualified_parent_commit_for_test(|machine| {
            machine.proof_attempt.inject_query_scope_failure(failure);
        });

        assert_eq!(committed, 0);
        assert_eq!(
            machine.row6_publication_lane_trace_for_test(),
            (0, Vec::new())
        );
        assert_eq!(machine.proof_terminal_failure(), None);
    }

    let mut machine = ConstraintMachine::new();
    machine.reset_row6_publication_lane_trace_for_test();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };

    let committed = machine.exercise_row6_replay_qualified_parent_commit_for_test(|machine| {
        machine.inject_row6_caller_failure_for_test(failure.clone());
    });

    assert_eq!(committed, 0);
    assert_eq!(machine.row6_publication_lane_trace_for_test().0, 1);
    assert_eq!(machine.proof_terminal_failure(), Some(failure));
}

#[test]
fn cpk_sv_d_ss2_p0_row5_real_postcommit_denials_preserve_commit_publication_boundary() {
    for failure in [
        ProofFailure::TerminalLatchBusy,
        foreign_publication_round_failure(),
    ] {
        let mut fixture = row5_production_path_fixture();
        let before = row5_semantic_snapshot(&fixture.machine).publication;
        fixture.machine.reset_row5_publication_trace_for_test();
        fixture
            .machine
            .proof_attempt
            .inject_query_scope_failure_after_successful_scopes(1, failure);

        let panic = catch_unwind(AssertUnwindSafe(|| {
            fixture
                .machine
                .register_valid_reduction_route_claim_parent_for_test(
                    fixture.lower,
                    fixture.upper,
                    fixture.derivation,
                    fixture.parent_claim,
                );
        }));
        assert_row4_row7_canary_panic(panic.expect_err("the row-5 canary must panic"));
        assert_eq!(
            fixture
                .machine
                .proof_store
                .qualified_parent_count(fixture.result),
            1,
            "the authoritative commit must precede the denied row-5 scope",
        );
        assert_eq!(fixture.machine.proof_terminal_failure(), None);
        assert_eq!(
            fixture.machine.row5_publication_trace_for_test(),
            (0, 0, 0),
        );
        let after = row5_semantic_snapshot(&fixture.machine).publication;
        assert_eq!(after.owner_invalidations, before.owner_invalidations);
        assert_eq!(
            after.projectability_transitions,
            before.projectability_transitions,
        );
    }

    let mut fixture = row5_production_path_fixture();
    let before = row5_semantic_snapshot(&fixture.machine).publication;
    fixture.machine.reset_row5_publication_trace_for_test();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    fixture
        .machine
        .proof_attempt
        .inject_query_scope_failure_after_successful_scopes(1, failure.clone());
    fixture
        .machine
        .register_valid_reduction_route_claim_parent_for_test(
            fixture.lower,
            fixture.upper,
            fixture.derivation,
            fixture.parent_claim,
        );
    assert_eq!(
        fixture
            .machine
            .proof_store
            .qualified_parent_count(fixture.result),
        1,
    );
    assert_eq!(fixture.machine.proof_terminal_failure(), Some(failure));
    assert_eq!(
        fixture.machine.row5_publication_trace_for_test(),
        (0, 0, 0),
    );
    let after = row5_semantic_snapshot(&fixture.machine).publication;
    assert_eq!(after.owner_invalidations, before.owner_invalidations);
    assert_eq!(
        after.projectability_transitions,
        before.projectability_transitions,
    );
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

fn row1_witness_empty_generalized_root() -> crate::generalize::GeneralizedCompactRoot {
    crate::generalize::GeneralizedCompactRoot {
        compact: crate::compact::CompactRoot::default(),
        role_predicates: Vec::new(),
        quantifiers: Vec::new(),
        stack_quantifiers: Vec::new(),
        substitutions: Vec::new(),
        sandwiches: Vec::new(),
    }
}

#[test]
fn cpk_sv_d_ss2_p0_row1_witness_capture_uses_one_scope_with_success_parity() {
    let (mut machine, owner, direct, transitive) =
        ConstraintMachine::ordinary_no_claim_positive_alias_fixture();
    let record_for = |machine: &ConstraintMachine, owner, endpoint| {
        machine
            .bounds
            .of(owner)
            .into_iter()
            .flat_map(crate::constraints::VarBounds::generalized_projection_lowers)
            .find_map(|(record, bound)| {
                matches!(machine.types.pos(bound.pos), Pos::Var(found) if *found == endpoint)
                    .then_some(record)
            })
            .expect("ordinary witness fixture has its expected lower record")
    };
    let owner_record = record_for(&machine, owner, direct);
    let direct_record = record_for(&machine, direct, transitive);

    machine.proof_attempt.reset_query_trace();
    let (drafts, completeness) = crate::generalize::capture_generalized_witnesses(
        &mut machine,
        owner,
        &row1_witness_empty_generalized_root(),
    );

    assert_eq!(completeness, ProvenanceCompleteness::Incomplete);
    let lower = drafts
        .iter()
        .find(|draft| {
            draft.path == crate::constraints::GeneralizedTypePath::default()
                && draft.role == GeneralizedWitnessRole::LowerBound
        })
        .expect("ordinary projectable lower retains its root witness");
    assert_eq!(
        lower
            .incoming
            .iter()
            .flat_map(|edge| &edge.parents)
            .collect::<Vec<_>>(),
        vec![
            &GeneralizationParent::Bound(owner_record),
            &GeneralizationParent::Bound(direct_record),
        ]
    );
    assert_eq!(
        machine.proof_attempt.query_trace(),
        (2, 2, 1, 1, 1),
        "the top-level witness traversal enters one scope and no nested scope"
    );

    let production_source = include_str!("../../generalize/provenance.rs")
        .split("#[cfg(test)]")
        .next()
        .expect("production witness source precedes its tests");
    let production_identifiers = production_source
        .split(|character: char| !(character.is_ascii_alphanumeric() || character == '_'))
        .collect::<Vec<_>>();
    for forbidden in [
        "scheme_projectable_lowers",
        "scheme_projectable_lowers_in_round",
    ] {
        assert!(
            !production_identifiers.contains(&forbidden),
            "production witness capture must not call old direct helper identifier {forbidden}"
        );
    }
}

#[test]
fn cpk_sv_d_ss2_p0_row1_witness_denial_latches_before_empty_incomplete_poison() {
    let (mut machine, owner, _, _) = ConstraintMachine::ordinary_no_claim_positive_alias_fixture();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    machine
        .proof_attempt
        .inject_query_scope_failure(failure.clone());
    machine.proof_attempt.reset_query_trace();

    let (drafts, completeness) = crate::generalize::capture_generalized_witnesses(
        &mut machine,
        owner,
        &row1_witness_empty_generalized_root(),
    );

    assert!(
        drafts.is_empty(),
        "denial must not leak partial witness drafts"
    );
    assert_eq!(completeness, ProvenanceCompleteness::Incomplete);
    assert_eq!(machine.proof_terminal_failure(), Some(failure));
    assert_eq!(
        machine.proof_attempt.query_trace(),
        (1, 1, 1, 0, 0),
        "the injected real gateway denial precedes scope entry and poison construction"
    );
}

struct Row1OwnedReadScalingFixture {
    machine: ConstraintMachine,
    absent_owner: TypeVar,
    present_upper_owner: TypeVar,
    present_neighbor_owner: TypeVar,
    present_pre_pop_owner: TypeVar,
    present_subtract_owner: TypeVar,
    positive: PosId,
    negative: NegId,
    neutral: NeuId,
    role: RoleConstraint,
}

#[derive(Clone, Copy, Debug)]
enum Row1OwnedReadScalingProbe {
    UpperRecordsAbsent,
    UpperRecordsPresent,
    PosShape,
    NegShape,
    NeuShape,
    RoleRawVars,
    VarNeighborsAbsent,
    VarNeighborsPresent,
    PrePopFamiliesAbsent,
    PrePopFamiliesPresent,
    SubtractFactsAbsent,
    SubtractFactsPresent,
}

const ROW1_OWNED_READ_SCALING_PROBES: [Row1OwnedReadScalingProbe; 12] = [
    Row1OwnedReadScalingProbe::UpperRecordsAbsent,
    Row1OwnedReadScalingProbe::UpperRecordsPresent,
    Row1OwnedReadScalingProbe::PosShape,
    Row1OwnedReadScalingProbe::NegShape,
    Row1OwnedReadScalingProbe::NeuShape,
    Row1OwnedReadScalingProbe::RoleRawVars,
    Row1OwnedReadScalingProbe::VarNeighborsAbsent,
    Row1OwnedReadScalingProbe::VarNeighborsPresent,
    Row1OwnedReadScalingProbe::PrePopFamiliesAbsent,
    Row1OwnedReadScalingProbe::PrePopFamiliesPresent,
    Row1OwnedReadScalingProbe::SubtractFactsAbsent,
    Row1OwnedReadScalingProbe::SubtractFactsPresent,
];

fn row1_owned_read_scaling_fixture(unrelated_entries: u32) -> Row1OwnedReadScalingFixture {
    let mut machine = ConstraintMachine::new();
    let origin = OriginId::unknown_internal();

    for index in 0..unrelated_entries {
        let unrelated = TypeVar(index);
        let unrelated_pos = machine.alloc_pos(Pos::Var(TypeVar(10_000 + index * 2)));
        let unrelated_neg = machine.alloc_neg(Neg::Var(TypeVar(10_001 + index * 2)));
        let unrelated_neu = machine.alloc_neu(Neu::Bounds(unrelated_pos, unrelated_neg));
        machine.bounds.add_upper(
            unrelated,
            unrelated_neg,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(origin),
        );
        machine
            .var_adjacency
            .entry(unrelated)
            .or_default()
            .insert(TypeVar(20_000 + index), 1);
        machine.pre_pop_effect_families.insert(
            unrelated,
            vec![ConstraintEffectFamily {
                path: vec!["row1_scaling_effect".into()],
                args: vec![unrelated_neu],
            }],
        );
        machine
            .subtracts
            .facts
            .entry(unrelated)
            .or_default()
            .push(SubtractFact {
                id: SubtractId(index),
                subtractability: Subtractability::Set(
                    vec!["row1_scaling_subtract".into()],
                    vec![unrelated_neu],
                ),
            });
    }

    let lower = machine.alloc_pos(Pos::Var(TypeVar(30_000)));
    let upper = machine.alloc_neg(Neg::Var(TypeVar(30_001)));
    let neutral = machine.alloc_neu(Neu::Bounds(lower, upper));
    let positive = machine.alloc_pos(Pos::Con(
        vec!["row1_scaling_target_pos".into()],
        vec![neutral],
    ));
    let negative = machine.alloc_neg(Neg::Con(
        vec!["row1_scaling_target_neg".into()],
        vec![neutral],
    ));
    let role = RoleConstraint {
        role: vec!["row1_scaling_target_role".into()],
        inputs: vec![RoleConstraintArg {
            lower: positive,
            upper: negative,
        }],
        associated: Vec::new(),
    };

    // Bounds use the TypeVar as a direct Vec index. Add the present owner after the unrelated
    // range so its indexed record is last and a regression to `iter().nth(var.0)` must traverse
    // the whole corpus before cloning the record.
    let present_upper_owner = TypeVar(unrelated_entries);
    machine.bounds.add_upper(
        present_upper_owner,
        negative,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );

    // FxHashMap insertion order is not iteration order. Select each backing map's actual final
    // iteration key, then replace its value after all unrelated data exists. A hypothetical
    // `iter().find(...)` present-key regression must therefore visit the entire map, while each
    // target still has the same one-element payload at both fixture sizes.
    let present_neighbor_owner = machine
        .var_adjacency
        .keys()
        .copied()
        .last()
        .expect("scaling fixture has neighbor entries");
    machine.var_adjacency.insert(
        present_neighbor_owner,
        [(TypeVar(40_000), 1)].into_iter().collect(),
    );
    let present_pre_pop_owner = machine
        .pre_pop_effect_families
        .keys()
        .copied()
        .last()
        .expect("scaling fixture has pre-pop entries");
    machine.pre_pop_effect_families.insert(
        present_pre_pop_owner,
        vec![ConstraintEffectFamily {
            path: vec!["row1_scaling_target_effect".into()],
            args: vec![neutral],
        }],
    );
    let present_subtract_owner = machine
        .subtracts
        .facts
        .keys()
        .copied()
        .last()
        .expect("scaling fixture has subtract entries");
    machine.subtracts.facts.insert(
        present_subtract_owner,
        vec![SubtractFact {
            id: SubtractId(unrelated_entries),
            subtractability: Subtractability::Set(
                vec!["row1_scaling_target_subtract".into()],
                vec![neutral],
            ),
        }],
    );

    Row1OwnedReadScalingFixture {
        machine,
        absent_owner: TypeVar(u32::MAX),
        present_upper_owner,
        present_neighbor_owner,
        present_pre_pop_owner,
        present_subtract_owner,
        positive,
        negative,
        neutral,
        role,
    }
}

fn row1_owned_read_surface_best_elapsed(
    machine: &mut ConstraintMachine,
    absent_owner: TypeVar,
    present_upper_owner: TypeVar,
    present_neighbor_owner: TypeVar,
    present_pre_pop_owner: TypeVar,
    present_subtract_owner: TypeVar,
    positive: PosId,
    negative: NegId,
    neutral: NeuId,
    role: &RoleConstraint,
    probe: Row1OwnedReadScalingProbe,
) -> Duration {
    const SAMPLES: usize = 5;
    const READS_PER_SAMPLE: usize = 2_048;

    (0..SAMPLES)
        .map(|_| {
            let mut round = machine.new_projection_evaluation_round();
            let started = Instant::now();
            let checksum = machine
                .with_legacy_projection_query(&mut round, |query| {
                    let mut checksum = 0_usize;
                    for _ in 0..READS_PER_SAMPLE {
                        let observed = match probe {
                            Row1OwnedReadScalingProbe::UpperRecordsAbsent => std::hint::black_box(
                                query.projection_upper_records_in_scope(absent_owner),
                            )
                            .len(),
                            Row1OwnedReadScalingProbe::UpperRecordsPresent => std::hint::black_box(
                                query.projection_upper_records_in_scope(present_upper_owner),
                            )
                            .len(),
                            Row1OwnedReadScalingProbe::PosShape => {
                                let _ = std::hint::black_box(query.pos_shape_in_scope(positive));
                                0
                            }
                            Row1OwnedReadScalingProbe::NegShape => {
                                let _ = std::hint::black_box(query.neg_shape_in_scope(negative));
                                0
                            }
                            Row1OwnedReadScalingProbe::NeuShape => {
                                let _ = std::hint::black_box(query.neu_shape_in_scope(neutral));
                                0
                            }
                            Row1OwnedReadScalingProbe::RoleRawVars => {
                                std::hint::black_box(query.role_constraint_raw_vars_in_scope(role))
                                    .len()
                            }
                            Row1OwnedReadScalingProbe::VarNeighborsAbsent => {
                                std::hint::black_box(query.var_neighbors_in_scope(absent_owner))
                                    .len()
                            }
                            Row1OwnedReadScalingProbe::VarNeighborsPresent => std::hint::black_box(
                                query.var_neighbors_in_scope(present_neighbor_owner),
                            )
                            .len(),
                            Row1OwnedReadScalingProbe::PrePopFamiliesAbsent => {
                                std::hint::black_box(
                                    query.pre_pop_effect_families_in_scope(absent_owner),
                                )
                                .len()
                            }
                            Row1OwnedReadScalingProbe::PrePopFamiliesPresent => {
                                std::hint::black_box(
                                    query.pre_pop_effect_families_in_scope(present_pre_pop_owner),
                                )
                                .len()
                            }
                            Row1OwnedReadScalingProbe::SubtractFactsAbsent => {
                                std::hint::black_box(query.subtract_facts_in_scope(absent_owner))
                                    .len()
                            }
                            Row1OwnedReadScalingProbe::SubtractFactsPresent => {
                                std::hint::black_box(
                                    query.subtract_facts_in_scope(present_subtract_owner),
                                )
                                .len()
                            }
                        };
                        checksum = checksum.wrapping_add(observed + 1);
                    }
                    Ok(query.complete(checksum))
                })
                .expect("repeated row-1 owned reads remain available");
            assert_ne!(checksum, 0);
            started.elapsed()
        })
        .min()
        .expect("at least one scaling sample")
}

fn assert_row1_owned_read_scaling_present_targets(fixture: &mut Row1OwnedReadScalingFixture) {
    let mut round = fixture.machine.new_projection_evaluation_round();
    let observed = fixture
        .machine
        .with_legacy_projection_query(&mut round, |query| {
            let lengths = (
                query
                    .projection_upper_records_in_scope(fixture.present_upper_owner)
                    .len(),
                query
                    .var_neighbors_in_scope(fixture.present_neighbor_owner)
                    .len(),
                query
                    .pre_pop_effect_families_in_scope(fixture.present_pre_pop_owner)
                    .len(),
                query
                    .subtract_facts_in_scope(fixture.present_subtract_owner)
                    .len(),
            );
            Ok(query.complete(lengths))
        })
        .expect("present-key scaling targets remain readable");
    assert_eq!(observed, (1, 1, 1, 1));
}

#[test]
fn cpk_sv_d_ss2_p0_row1_owned_read_surface_matches_legacy_reads_and_is_bounded() {
    let mut machine = ConstraintMachine::new();
    let owner = TypeVar(10);
    let lower_var = TypeVar(11);
    let upper_var = TypeVar(12);
    let neighbor_a = TypeVar(13);
    let neighbor_b = TypeVar(14);
    let lower = machine.alloc_pos(Pos::Var(lower_var));
    let upper = machine.alloc_neg(Neg::Var(upper_var));
    let neutral = machine.alloc_neu(Neu::Bounds(lower, upper));
    let positive_shape = Pos::Con(vec!["row1_owned_pos".into()], vec![neutral]);
    let negative_shape = Neg::Con(vec!["row1_owned_neg".into()], vec![neutral]);
    let positive = machine.alloc_pos(positive_shape.clone());
    let negative = machine.alloc_neg(negative_shape.clone());
    let ordinary_negative = machine.alloc_neg(Neg::Var(TypeVar(15)));
    let origin = OriginId::unknown_internal();
    let evidence_record = machine
        .bounds
        .add_evidence_upper(
            owner,
            negative,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(origin),
        )
        .id;
    let ordinary_record = machine
        .bounds
        .add_upper(
            owner,
            ordinary_negative,
            ConstraintWeights::empty(),
            BoundDerivation::Origin(origin),
        )
        .id;
    machine
        .var_adjacency
        .entry(owner)
        .or_default()
        .extend([(neighbor_a, 1), (neighbor_b, 1)]);
    let family = ConstraintEffectFamily {
        path: vec!["row1_owned_effect".into()],
        args: vec![neutral],
    };
    machine
        .pre_pop_effect_families
        .insert(owner, vec![family.clone()]);
    let subtract = SubtractFact {
        id: SubtractId(16),
        subtractability: Subtractability::Set(vec!["row1_owned_subtract".into()], vec![neutral]),
    };
    machine.subtract_fact(owner, subtract.id, subtract.subtractability.clone());
    let role = RoleConstraint {
        role: vec!["row1_owned_role".into()],
        inputs: vec![RoleConstraintArg {
            lower: positive,
            upper: negative,
        }],
        associated: Vec::new(),
    };

    let expected_upper_records = machine
        .bounds()
        .of(owner)
        .expect("row-1 fixture has upper records")
        .generalized_projection_uppers()
        .map(|(record, bound)| (record, bound.clone()))
        .collect::<Vec<_>>();
    let expected_neighbors = machine.var_neighbors(owner).collect::<Vec<_>>();
    let expected_pre_pop = machine.pre_pop_effect_families(owner).to_vec();
    let expected_subtracts = machine.subtracts().facts(owner).to_vec();
    let expected_role_vars = role.raw_vars(machine.types());

    let legacy_guard = begin_owner_dependency_reads();
    let _ = machine.bounds().of(owner);
    let _ = machine.var_neighbors(owner).collect::<Vec<_>>();
    let _ = machine.pre_pop_effect_families(owner);
    let _ = machine.subtracts().facts(owner);
    let legacy_reads = legacy_guard.finish();
    let legacy_hook_calls = legacy_reads.logical_read_hook_calls();
    let legacy_read_keys = legacy_reads
        .constraint_dependency_keys()
        .into_iter()
        .collect::<FxHashSet<_>>();

    machine.proof_attempt.reset_query_trace();
    let scoped_guard = begin_owner_dependency_reads();
    let mut round = machine.new_projection_evaluation_round();
    let actual = machine
        .with_legacy_projection_query(&mut round, |query| {
            let output = (
                query.projection_upper_records_in_scope(owner),
                query.pos_shape_in_scope(positive),
                query.neg_shape_in_scope(negative),
                query.neu_shape_in_scope(neutral),
                query.role_constraint_raw_vars_in_scope(&role),
                query.var_neighbors_in_scope(owner),
                query.pre_pop_effect_families_in_scope(owner),
                query.subtract_facts_in_scope(owner),
            );
            Ok(query.complete(output))
        })
        .expect("all eight row-1 owned reads complete in one scope");
    let scoped_reads = scoped_guard.finish();
    let scoped_hook_calls = scoped_reads.logical_read_hook_calls();
    let scoped_read_keys = scoped_reads
        .constraint_dependency_keys()
        .into_iter()
        .collect::<FxHashSet<_>>();

    assert_eq!(actual.0, expected_upper_records);
    assert_eq!(actual.0[0].0, evidence_record);
    assert_eq!(actual.0[1].0, ordinary_record);
    assert_eq!(actual.1, positive_shape);
    assert_eq!(actual.2, negative_shape);
    assert_eq!(actual.3, Neu::Bounds(lower, upper));
    assert_eq!(actual.4, expected_role_vars);
    assert_eq!(actual.5, expected_neighbors);
    assert_eq!(actual.6, expected_pre_pop);
    assert_eq!(actual.7, expected_subtracts);
    assert_eq!(actual.0.len(), 2);
    assert_eq!(actual.5.len(), 2);
    assert_eq!(actual.6.len(), 1);
    assert_eq!(actual.7.len(), 1);
    assert_eq!(scoped_read_keys, legacy_read_keys);
    // Bounds, neighbors, pre-pop families, and subtract facts have one hook each. Shape and
    // role-raw-var getters intentionally have none.
    assert_eq!(legacy_hook_calls, 4);
    assert_eq!(scoped_hook_calls, 4);
    assert_eq!(
        scoped_read_keys,
        [
            DependencyKey::ConstraintBounds(owner),
            DependencyKey::ConstraintNeighbors(owner),
            DependencyKey::ConstraintSubtractFacts(owner),
            DependencyKey::ConstraintPrePopFamilies(owner),
        ]
        .into_iter()
        .collect()
    );
    assert_eq!(machine.proof_attempt.query_trace(), (2, 2, 1, 1, 1));

    // This is a key-local complexity guard, not the slice 4/5 full-pipeline cold/warm wall/RSS
    // gate. Collection getters have both absent-key probes, which cannot stop at an early match,
    // and present-key probes whose one-element payloads sit at the final Vec index / final actual
    // FxHashMap iteration position. Thus a hypothetical sequential scan must traverse all
    // 256/4096 entries on both paths instead of hiding behind an early target or an empty fast
    // path. The Pos/Neg/Neu targets are allocated after every unrelated node, putting them last
    // in their arenas too. Every getter/path is timed as a separate probe, so one O(n) regression
    // cannot hide behind constant-time reads: it would grow toward 16x and fail the 4x ceiling.
    // The real keyed lookup/indexing path remains relative to target data and should stay near
    // constant. Slice 4/5 still owns the full-pipeline cold/warm wall/RSS landing gate.
    let mut small_fixture = row1_owned_read_scaling_fixture(256);
    let mut large_fixture = row1_owned_read_scaling_fixture(4_096);
    assert_row1_owned_read_scaling_present_targets(&mut small_fixture);
    assert_row1_owned_read_scaling_present_targets(&mut large_fixture);
    for probe in ROW1_OWNED_READ_SCALING_PROBES {
        let small_fixture_elapsed = row1_owned_read_surface_best_elapsed(
            &mut small_fixture.machine,
            small_fixture.absent_owner,
            small_fixture.present_upper_owner,
            small_fixture.present_neighbor_owner,
            small_fixture.present_pre_pop_owner,
            small_fixture.present_subtract_owner,
            small_fixture.positive,
            small_fixture.negative,
            small_fixture.neutral,
            &small_fixture.role,
            probe,
        );
        let large_fixture_elapsed = row1_owned_read_surface_best_elapsed(
            &mut large_fixture.machine,
            large_fixture.absent_owner,
            large_fixture.present_upper_owner,
            large_fixture.present_neighbor_owner,
            large_fixture.present_pre_pop_owner,
            large_fixture.present_subtract_owner,
            large_fixture.positive,
            large_fixture.negative,
            large_fixture.neutral,
            &large_fixture.role,
            probe,
        );
        let maximum_key_local_growth = small_fixture_elapsed.as_nanos().saturating_mul(4);
        assert!(
            large_fixture_elapsed.as_nanos() <= maximum_key_local_growth,
            "16x unrelated-data growth made {probe:?} grow more than 4x: small={small_fixture_elapsed:?}, large={large_fixture_elapsed:?}"
        );
    }
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
