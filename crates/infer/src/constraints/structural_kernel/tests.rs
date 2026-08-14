use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::Command;

use super::commands::StructuralMutationIntent as I;
use super::{ProofAccessError, ProofAttemptKernel, ProofQueryError};
use crate::constraints::ConstraintMachine;
use crate::constraints::proof::{ProofFailure, ProofOperation};

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
            "cannot move out of `query` because it is borrowed",
        ),
        (
            "cpk_sv_d_ss1_rf_ui_same_kernel_mutation",
            "cannot borrow `*machine` as mutable because it is also borrowed as immutable",
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
        Err(ProofQueryError::Access(
            ProofAccessError::ForeignAttemptRoundState { expected, actual }
        ))
    );
    assert!(!invoked.get());
}

#[test]
fn cpk_sv_d_ss1_rf_foreign_publication_round_is_access_denial() {
    let first = ConstraintMachine::new();
    let mut foreign_round = first.new_publication_evaluation_round();
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
        Err(ProofQueryError::Access(
            ProofAccessError::ForeignAttemptRoundState { expected, actual }
        ))
    );
    assert!(!invoked.get());
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
fn cpk_sv_d_ss1_rf_query_failure_stays_separate_from_access_denial() {
    let mut machine = ConstraintMachine::new();
    let mut round = machine.new_projection_evaluation_round();
    let failure = ProofFailure::ResourceExhausted {
        operation: ProofOperation::ProjectLowerEvaluation,
    };
    let result: Result<(), ProofQueryError> =
        machine.with_projection_query(&mut round, |_| Err(failure.clone()));
    assert_eq!(result, Err(ProofQueryError::Failure(failure.clone())));

    let result = machine.with_projection_query(&mut round, |query| Ok(query.complete(())));
    assert_eq!(
        result,
        Err(ProofQueryError::Access(ProofAccessError::Terminal(failure)))
    );
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
    let result: Result<(), ProofQueryError> = machine.with_projection_query(&mut round, |query| {
        invoked.set(true);
        Ok(query.complete(()))
    });
    assert_eq!(result, Err(ProofQueryError::Failure(failure.clone())));
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
    let result: Result<(), ProofQueryError> =
        machine.with_publication_projection_query(&mut round, |query| {
            invoked.set(true);
            Ok(query.complete(()))
        });
    assert_eq!(result, Err(ProofQueryError::Failure(failure.clone())));
    assert!(!invoked.get());
    assert_eq!(machine.proof_terminal_failure(), Some(failure));
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
