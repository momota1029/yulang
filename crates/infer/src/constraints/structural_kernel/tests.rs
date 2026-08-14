use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::Command;

use super::commands::StructuralMutationIntent as I;
use super::{ProofAccessError, ProofAttemptKernel};
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
