use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::Command;

use super::commands::StructuralMutationIntent as I;
use super::{ProofAccessError, ProofAttemptKernel};
use crate::constraints::proof::{ProofFailure, ProofOperation};
use crate::constraints::{ConstraintMachine, ConstraintRecordId, OriginId};

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
            "module `legacy_read_view` is private",
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
    machine
        .proof_store
        .record_constraint_root(ConstraintRecordId(0), OriginId::unknown_internal());

    let mut projection_round = machine.new_projection_evaluation_round();
    let projection_counts = machine
        .with_legacy_projection_query(&mut projection_round, |mut query| {
            assert!(!query.shadow_check_target(7));
            assert!(query.shadow_check_target(7));
            let counts = query.legacy_storage_counts();
            Ok(query.complete(counts))
        })
        .expect("legacy projection scope reads production owners");
    assert_eq!(projection_counts, (1, 0, 0, 0, 2));

    let mut publication_round = machine.new_publication_evaluation_round();
    let publication_counts = machine
        .with_legacy_publication_query(&mut publication_round, |mut query| {
            assert!(!query.shadow_check_target(11));
            assert!(query.shadow_check_target(11));
            let counts = query.legacy_storage_counts();
            Ok(query.complete(counts))
        })
        .expect("legacy publication scope reads production owners");
    assert_eq!(publication_counts, projection_counts);
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
fn cpk_sv_d_ss1_rf_busy_terminal_latch_uses_exact_proof_failure_surface() {
    let machine = ConstraintMachine::new();
    assert_eq!(
        machine.proof_attempt.query_latch_busy_failure_for_test(),
        ProofFailure::TerminalLatchBusy
    );
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
