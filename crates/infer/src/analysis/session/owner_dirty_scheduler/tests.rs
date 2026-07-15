use super::*;

use poly::expr::Arena as PolyArena;
use std::panic::{AssertUnwindSafe, catch_unwind};

#[test]
fn production_constraint_capture_does_not_pollute_the_exact_shadow_frontier() {
    let exact_var = TypeVar(10);
    let production_var = TypeVar(20);
    let guard = begin_owner_dependency_reads();

    record_owner_bound_read(exact_var);
    record_owner_dependency_read(DependencyKey::ConstraintNeighbors(production_var));

    let reads = guard.finish();
    assert_eq!(
        reads.constraint_dependency_keys(),
        vec![DependencyKey::ConstraintBounds(exact_var)]
    );
    assert_eq!(
        reads.production_constraint_dependencies,
        [DependencyKey::ConstraintNeighbors(production_var)]
            .into_iter()
            .collect()
    );
}

#[test]
fn every_dependency_key_wakes_its_owner_and_preserves_unrelated_clean_reuse() {
    let owner = DefId(1);
    let unrelated_owner = DefId(2);
    let dependencies = every_dependency_key(owner);
    assert_eq!(dependencies.len(), 13);

    for (index, dependency) in dependencies.into_iter().enumerate() {
        let unrelated = DependencyKey::ConstraintBounds(TypeVar(10_000 + index as u32));
        let mut scheduler = skipping_scheduler_with_records([
            (owner, dependency.clone()),
            (unrelated_owner, unrelated),
        ]);

        scheduler.begin_pass(&[owner, unrelated_owner], &MethodTaintIndex::default());
        assert_eq!(
            scheduler.prepare_owner(owner, true, None),
            OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
            "{dependency:?}: an unchanged terminal record must exercise the real skip path",
        );
        assert_eq!(
            scheduler.prepare_owner(unrelated_owner, true, None),
            OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
        );

        scheduler.begin_pass(&[owner, unrelated_owner], &MethodTaintIndex::default());
        scheduler.drain_mutations(
            vec![MethodRoleMutation::Changed {
                serial: MutationSerial::new(1),
                key: dependency.clone(),
            }],
            true,
        );
        assert_eq!(
            scheduler.prepare_owner(owner, true, None),
            OwnerScheduleDecision::Solve,
            "{dependency:?}: its subscribed owner must wake",
        );
        scheduler.finish_owner(
            owner,
            OwnerSolveOutcome::NoProgress,
            vec![dependency.clone()],
            Duration::ZERO,
            true,
        );
        assert_eq!(
            scheduler.prepare_owner(unrelated_owner, true, None),
            OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
            "{dependency:?}: an independently subscribed owner must remain clean",
        );

        scheduler.begin_pass(&[owner, unrelated_owner], &MethodTaintIndex::default());
        assert_eq!(
            scheduler.prepare_owner(owner, true, None),
            OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
            "{dependency:?}: the real no-progress solve must republish a reusable terminal",
        );
        assert_eq!(
            scheduler.prepare_owner(unrelated_owner, true, None),
            OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
        );
        assert_eq!(scheduler.metrics.real_solves, 1);
        assert_eq!(scheduler.metrics.clean_skips, 5);
    }
}

#[test]
fn candidate_prerequisite_dependencies_invalidate_transitively_and_locally() {
    let reader = DefId(1);
    let non_reader = DefId(2);
    let buckets =
        ["A", "B", "C"].map(|name| DependencyKey::CandidateBucket(vec![name.to_string()]));
    let unread = DependencyKey::CandidateBucket(vec!["D".to_string()]);

    for changed in buckets.iter().cloned() {
        let mut scheduler = MethodRoleOwnerDirtyScheduler {
            permit_owner_skips: true,
            ..Default::default()
        };
        scheduler.publish_record(reader, OwnerSolveOutcome::NoProgress, buckets.to_vec());
        scheduler.publish_record(
            non_reader,
            OwnerSolveOutcome::NoProgress,
            vec![unread.clone()],
        );
        scheduler.begin_pass(&[reader, non_reader], &MethodTaintIndex::default());
        scheduler.drain_mutations(
            vec![MethodRoleMutation::Changed {
                serial: MutationSerial::new(1),
                key: changed.clone(),
            }],
            true,
        );
        assert_eq!(
            scheduler.prepare_owner(reader, true, None),
            OwnerScheduleDecision::Solve
        );
        assert_eq!(
            scheduler.prepare_owner(non_reader, true, None),
            OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
            "unread owner changed for transitive bucket {changed:?}",
        );
    }

    let mut scheduler = MethodRoleOwnerDirtyScheduler {
        permit_owner_skips: true,
        ..Default::default()
    };
    scheduler.publish_record(reader, OwnerSolveOutcome::NoProgress, buckets.to_vec());
    scheduler.begin_pass(&[reader], &MethodTaintIndex::default());
    scheduler.drain_mutations(
        vec![MethodRoleMutation::Changed {
            serial: MutationSerial::new(1),
            key: unread,
        }],
        true,
    );
    assert_eq!(
        scheduler.prepare_owner(reader, true, None),
        OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
        "an unread prerequisite bucket must not destroy locality",
    );
}

#[test]
fn method_taint_and_cross_owner_selection_projection_control_skip_eligibility() {
    let reader = DefId(1);
    let queried = TypeVar(10);
    let unqueried = TypeVar(11);
    let cross_owner_selection = SelectId(12);
    let dependencies = vec![
        DependencyKey::MethodTaint(queried),
        DependencyKey::Selection(cross_owner_selection),
    ];

    for changed in dependencies.iter().cloned() {
        let mut scheduler = MethodRoleOwnerDirtyScheduler {
            permit_owner_skips: true,
            ..Default::default()
        };
        scheduler.publish_record(reader, OwnerSolveOutcome::NoProgress, dependencies.clone());
        scheduler.begin_pass(&[reader], &MethodTaintIndex::default());
        scheduler.drain_mutations(
            vec![MethodRoleMutation::Changed {
                serial: MutationSerial::new(1),
                key: changed,
            }],
            true,
        );
        assert_eq!(
            scheduler.prepare_owner(reader, true, None),
            OwnerScheduleDecision::Solve
        );
    }

    let mut scheduler = MethodRoleOwnerDirtyScheduler {
        permit_owner_skips: true,
        ..Default::default()
    };
    scheduler.publish_record(reader, OwnerSolveOutcome::NoProgress, dependencies);
    scheduler.begin_pass(&[reader], &MethodTaintIndex::default());
    scheduler.drain_mutations(
        vec![MethodRoleMutation::Changed {
            serial: MutationSerial::new(1),
            key: DependencyKey::MethodTaint(unqueried),
        }],
        true,
    );
    assert_eq!(
        scheduler.prepare_owner(reader, true, None),
        OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
    );

    let previous = [(queried, vec![SelectId(1)]), (unqueried, vec![SelectId(2)])]
        .into_iter()
        .collect();
    let current = [(unqueried, vec![SelectId(2)])].into_iter().collect();
    assert_eq!(
        diff_method_taint(&previous, &current),
        vec![queried],
        "a disappeared earlier short-circuit taint entry must wake its readers",
    );
}

#[test]
fn every_fail_closed_reason_refuses_all_owner_skips() {
    let reasons = [
        InvalidateAllReason::UnrecognizedMutation {
            site: "stage4-unknown",
        },
        InvalidateAllReason::JournalOverflow,
        InvalidateAllReason::MutationSerialOverflow,
        InvalidateAllReason::MutationGenerationOverflow,
        InvalidateAllReason::AuditFenceDisagreement {
            site: "stage4-audit",
        },
        InvalidateAllReason::ContractVersionMismatch,
        InvalidateAllReason::JournalTruncated,
    ];

    for reason in reasons {
        let first = DefId(1);
        let second = DefId(2);
        let mut scheduler = skipping_scheduler_with_records([
            (first, DependencyKey::ConstraintBounds(TypeVar(10))),
            (second, DependencyKey::ConstraintBounds(TypeVar(20))),
        ]);
        scheduler.begin_pass(&[first, second], &MethodTaintIndex::default());
        scheduler.drain_mutations(
            vec![MethodRoleMutation::InvalidateAll {
                serial: MutationSerial::new(1),
                reason: reason.clone(),
            }],
            false,
        );
        assert_eq!(
            scheduler.prepare_owner(first, true, None),
            OwnerScheduleDecision::Solve
        );
        assert_eq!(
            scheduler.prepare_owner(second, true, None),
            OwnerScheduleDecision::Solve
        );
        assert_eq!(scheduler.metrics.clean_skips, 0, "{reason:?}");
        assert_eq!(scheduler.metrics.real_solves, 2, "{reason:?}");
    }
}

#[test]
fn missing_journal_serial_and_generation_overflow_refuse_real_skips() {
    let owner = DefId(1);
    let dependency = DependencyKey::ConstraintBounds(TypeVar(10));

    let mut lost = skipping_scheduler_with_records([(owner, dependency.clone())]);
    lost.begin_pass(&[owner], &MethodTaintIndex::default());
    lost.drain_mutations(
        vec![MethodRoleMutation::Changed {
            serial: MutationSerial::new(2),
            key: dependency.clone(),
        }],
        true,
    );
    assert_eq!(
        lost.prepare_owner(owner, true, None),
        OwnerScheduleDecision::Solve
    );
    assert!(matches!(
        lost.metrics.invalidate_all_reasons.as_slice(),
        [InvalidateAllReason::JournalTruncated]
    ));

    let mut overflow = skipping_scheduler_with_records([(owner, dependency.clone())]);
    overflow
        .generations
        .insert(dependency.clone(), MutationGeneration::new(u64::MAX));
    overflow.begin_pass(&[owner], &MethodTaintIndex::default());
    overflow.drain_mutations(
        vec![MethodRoleMutation::Changed {
            serial: MutationSerial::new(1),
            key: dependency,
        }],
        true,
    );
    assert_eq!(
        overflow.prepare_owner(owner, true, None),
        OwnerScheduleDecision::Solve
    );
    assert!(matches!(
        overflow.metrics.invalidate_all_reasons.as_slice(),
        [InvalidateAllReason::MutationGenerationOverflow]
    ));
}

#[test]
fn owner_runs_at_most_once_per_pass_and_progress_never_enters_the_cache() {
    let owner = DefId(1);
    let dependency = DependencyKey::ConstraintBounds(TypeVar(10));
    let mut scheduler = skipping_scheduler_with_records([(owner, dependency.clone())]);
    scheduler.begin_pass(&[owner], &MethodTaintIndex::default());
    assert_eq!(
        scheduler.prepare_owner(owner, true, None),
        OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress)
    );
    let duplicate = catch_unwind(AssertUnwindSafe(|| {
        let _ = scheduler.prepare_owner(owner, true, None);
    }));
    assert!(duplicate.is_err());

    let progress_cache = catch_unwind(AssertUnwindSafe(|| {
        scheduler.publish_record(owner, OwnerSolveOutcome::Progress, vec![dependency]);
    }));
    assert!(progress_cache.is_err());
}

#[test]
fn record_replacement_removes_old_reverse_subscriptions() {
    let owner = DefId(1);
    let old = DependencyKey::ConstraintBounds(TypeVar(10));
    let retained = DependencyKey::ConstraintLevel(TypeVar(11));
    let new = DependencyKey::CandidateBucket(vec!["New".into()]);
    let mut scheduler = MethodRoleOwnerDirtyScheduler::default();

    scheduler.publish_record(
        owner,
        OwnerSolveOutcome::NoProgress,
        vec![old.clone(), retained.clone()],
    );
    scheduler.publish_record(
        owner,
        OwnerSolveOutcome::NoProgress,
        vec![retained.clone(), new.clone()],
    );

    assert!(!scheduler.reverse_subscriptions.contains_key(&old));
    assert_eq!(
        scheduler.reverse_subscriptions.get(&retained),
        Some(&[owner].into_iter().collect())
    );
    assert_eq!(
        scheduler.reverse_subscriptions.get(&new),
        Some(&[owner].into_iter().collect())
    );
    assert_eq!(scheduler.reverse_edge_count(), 2);
    assert_eq!(scheduler.metrics.record_replacements, 1);
}

#[test]
fn pass_ordering_drains_earlier_mutation_before_later_owner_eligibility() {
    let earlier = DefId(1);
    let later = DefId(2);
    let later_dependency = DependencyKey::ConstraintBounds(TypeVar(20));
    let mut scheduler = scheduler_with_records([
        (earlier, DependencyKey::ConstraintBounds(TypeVar(10))),
        (later, later_dependency.clone()),
    ]);
    scheduler.permit_owner_skips = true;
    scheduler.dirty.insert(earlier);
    scheduler.begin_pass(&[earlier, later], &MethodTaintIndex::default());

    assert_eq!(
        scheduler.prepare_owner(earlier, true, None),
        OwnerScheduleDecision::Solve
    );
    scheduler.finish_owner(
        earlier,
        OwnerSolveOutcome::Progress,
        Vec::new(),
        Duration::ZERO,
        true,
    );
    scheduler.drain_mutations(
        vec![MethodRoleMutation::Changed {
            serial: MutationSerial::new(1),
            key: later_dependency,
        }],
        true,
    );
    assert_eq!(
        scheduler.prepare_owner(later, true, None),
        OwnerScheduleDecision::Solve
    );

    let prediction = scheduler
        .current_predictions
        .get(&later)
        .expect("later owner prediction");
    assert!(!prediction.clean);
    assert_eq!(prediction.reason, OwnerPredictionReason::TouchedDependency);
    assert_eq!(scheduler.metrics.owner_checks, 2);
}

#[test]
fn pass_ordering_leaves_earlier_owner_dirty_for_the_next_pass() {
    let earlier = DefId(1);
    let later = DefId(2);
    let earlier_dependency = DependencyKey::ConstraintBounds(TypeVar(10));
    let mut scheduler = scheduler_with_records([
        (earlier, earlier_dependency.clone()),
        (later, DependencyKey::ConstraintBounds(TypeVar(20))),
    ]);
    scheduler.permit_owner_skips = true;
    scheduler.dirty.insert(later);
    scheduler.begin_pass(&[earlier, later], &MethodTaintIndex::default());

    assert_eq!(
        scheduler.prepare_owner(earlier, true, None),
        OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
    );
    assert_eq!(
        scheduler.prepare_owner(later, true, None),
        OwnerScheduleDecision::Solve
    );
    scheduler.drain_mutations(
        vec![MethodRoleMutation::Changed {
            serial: MutationSerial::new(1),
            key: earlier_dependency,
        }],
        true,
    );
    scheduler.finish_owner(
        later,
        OwnerSolveOutcome::Progress,
        Vec::new(),
        Duration::ZERO,
        true,
    );

    assert!(scheduler.dirty.contains(&earlier));
    scheduler.begin_pass(&[earlier, later], &MethodTaintIndex::default());
    assert_eq!(
        scheduler.prepare_owner(earlier, true, None),
        OwnerScheduleDecision::Solve
    );
    let prediction = scheduler
        .current_predictions
        .get(&earlier)
        .expect("next-pass earlier prediction");
    assert!(!prediction.clean);
    assert_eq!(prediction.reason, OwnerPredictionReason::TouchedDependency);
    assert_eq!(scheduler.metrics.owner_checks, 3);
}

#[test]
fn invalidate_all_and_generation_overflow_force_every_owner_dirty() {
    let owner = DefId(1);
    let other = DefId(2);
    let dependency = DependencyKey::ConstraintBounds(TypeVar(10));
    let mut scheduler = scheduler_with_records([
        (owner, dependency.clone()),
        (other, DependencyKey::ConstraintBounds(TypeVar(20))),
    ]);
    scheduler.begin_pass(&[owner, other], &MethodTaintIndex::default());
    let mut outbox = crate::constraints::mutation::MethodRoleMutationOutbox::with_capacity(0);
    let activation = outbox.activate();
    outbox.record(DependencyKey::ConstraintBounds(TypeVar(99)));
    let owner_eligibility = outbox.owner_eligibility();
    scheduler.drain_mutations(outbox.take(), owner_eligibility);
    activation.finish();
    scheduler.prepare_owner(owner, true, None);
    scheduler.prepare_owner(other, true, None);
    assert!(
        scheduler
            .current_predictions
            .values()
            .all(|prediction| !prediction.clean
                && prediction.reason == OwnerPredictionReason::FullInvalidation)
    );

    let mut overflow = scheduler_with_records([(owner, dependency.clone())]);
    overflow
        .generations
        .insert(dependency.clone(), MutationGeneration::new(u64::MAX));
    overflow.begin_pass(&[owner], &MethodTaintIndex::default());
    overflow.drain_mutations(
        vec![MethodRoleMutation::Changed {
            serial: MutationSerial::new(1),
            key: dependency,
        }],
        true,
    );
    overflow.prepare_owner(owner, true, None);
    assert_eq!(
        overflow.current_predictions[&owner].reason,
        OwnerPredictionReason::FullInvalidation
    );
    assert!(matches!(
        overflow.metrics.invalidate_all_reasons.as_slice(),
        [InvalidateAllReason::MutationGenerationOverflow]
    ));
}

#[test]
fn inactive_window_change_is_fail_closed_but_a_stable_window_reuses_records() {
    let owner = DefId(1);
    let dependency = DependencyKey::ConstraintBounds(TypeVar(10));
    let mut scheduler = scheduler_with_records([(owner, dependency)]);
    let session = AnalysisSession::new(PolyArena::new());
    let stable = session.method_role_pass_input_snapshot();

    scheduler.finish_journal_window(stable);
    scheduler.begin_journal_window(stable);
    scheduler.begin_pass(&[owner], &MethodTaintIndex::default());
    scheduler.prepare_owner(owner, true, None);
    assert!(scheduler.current_predictions[&owner].clean);

    scheduler.current_predictions.clear();
    scheduler.publish_record(
        owner,
        OwnerSolveOutcome::NoProgress,
        vec![DependencyKey::ConstraintBounds(TypeVar(10))],
    );
    let mut changed = stable;
    changed.input_generation += 1;
    scheduler.finish_journal_window(stable);
    scheduler.begin_journal_window(changed);
    scheduler.begin_pass(&[owner], &MethodTaintIndex::default());
    scheduler.prepare_owner(owner, true, None);
    assert_eq!(
        scheduler.current_predictions[&owner].reason,
        OwnerPredictionReason::FullInvalidation
    );
    assert!(matches!(
        scheduler.metrics.invalidate_all_reasons.last(),
        Some(InvalidateAllReason::UnrecognizedMutation {
            site: "inactive method-role journal window"
        })
    ));
}

#[test]
fn resolved_and_quantified_owners_leave_no_reverse_subscription_tombstones() {
    let resolved_owner = DefId(1);
    let quantified_owner = DefId(2);
    let mut session = AnalysisSession::new(PolyArena::new());
    session.owner_dirty_scheduler = Some(MethodRoleOwnerDirtyScheduler::default());
    let selection = SelectId(1);
    let var = session.infer.fresh_type_var();
    session.selections.insert(
        selection,
        SelectionUse {
            parent: resolved_owner,
            method_value: var,
            selected_value: var,
            receiver_value: var,
            receiver_effect: var,
            local_method_scope: None,
            recursive_self_value: None,
        },
    );
    session
        .owner_dirty_scheduler
        .as_mut()
        .expect("scheduler")
        .publish_record(
            resolved_owner,
            OwnerSolveOutcome::NoProgress,
            vec![DependencyKey::OwnerSelections(resolved_owner)],
        );
    session.remove_unresolved_selection(selection);

    let root = session.infer.fresh_type_var();
    session.apply_scc_input(SccInput::RegisterDef {
        def: quantified_owner,
        root,
    });
    session
        .owner_dirty_scheduler
        .as_mut()
        .expect("scheduler")
        .publish_record(
            quantified_owner,
            OwnerSolveOutcome::NoProgress,
            vec![DependencyKey::SccRoot(quantified_owner)],
        );
    session.apply_scc_input(SccInput::DefFinished {
        def: quantified_owner,
    });
    session.route_scc_events();

    let report = session.owner_dirty_scheduler_report().expect("report");
    assert_eq!(report.live_records, 0);
    assert_eq!(report.live_dependency_keys, 0);
    assert_eq!(report.live_reverse_edges, 0);
    assert_eq!(report.lifecycle_evictions, 2);
}

#[test]
fn method_taint_diff_is_sorted_and_detects_add_change_and_removal() {
    let first = TypeVar(1);
    let second = TypeVar(2);
    let previous = [(second, vec![SelectId(2)]), (first, vec![SelectId(1)])]
        .into_iter()
        .collect();
    let current = [(second, vec![SelectId(3)]), (TypeVar(3), vec![SelectId(4)])]
        .into_iter()
        .collect();

    assert_eq!(
        diff_method_taint(&previous, &current),
        vec![first, second, TypeVar(3)]
    );
}

#[test]
fn benchmark_mode_is_disabled_by_default_and_restored_after_return_or_unwind() {
    assert!(MethodRoleOwnerDirtyScheduler::for_new_session().is_none());

    with_owner_dirty_scheduler_benchmark_for_new_sessions(|| {
        let scheduler = MethodRoleOwnerDirtyScheduler::for_new_session()
            .expect("explicit benchmark scope enables new sessions");
        assert!(scheduler.permit_owner_skips);
    });
    assert!(MethodRoleOwnerDirtyScheduler::for_new_session().is_none());

    let unwind = catch_unwind(AssertUnwindSafe(|| {
        with_owner_dirty_scheduler_benchmark_for_new_sessions(|| {
            assert!(MethodRoleOwnerDirtyScheduler::for_new_session().is_some());
            panic!("exercise benchmark mode unwind cleanup");
        });
    }));
    assert!(unwind.is_err());
    assert!(MethodRoleOwnerDirtyScheduler::for_new_session().is_none());
}

#[test]
fn approved_production_budget_uses_the_stage5_caps() {
    let budget = OwnerDirtySchedulerBudget::default();
    assert_eq!(budget.max_owners, Some(1_000));
    assert_eq!(budget.max_dependency_keys, Some(250_000));
    assert_eq!(budget.max_dependencies_per_owner, Some(2_000));
    assert_eq!(budget.max_reverse_edges, Some(25_000));
    assert_eq!(budget.max_journal_burst, Some(500_000));
    assert_eq!(budget.max_retained_bytes, Some(33_554_432));
}

#[test]
fn dependencies_per_owner_cap_rejects_only_the_oversized_owner() {
    let cacheable_owner = DefId(1);
    let oversized_owner = DefId(2);
    let mut scheduler = skipping_scheduler_with_budget(OwnerDirtySchedulerBudget {
        max_dependencies_per_owner: Some(1),
        ..OwnerDirtySchedulerBudget::default()
    });
    scheduler.publish_record(
        cacheable_owner,
        OwnerSolveOutcome::NoProgress,
        vec![DependencyKey::ConstraintBounds(TypeVar(1))],
    );
    scheduler.publish_record(
        oversized_owner,
        OwnerSolveOutcome::NoProgress,
        vec![
            DependencyKey::ConstraintBounds(TypeVar(2)),
            DependencyKey::ConstraintNeighbors(TypeVar(2)),
        ],
    );

    assert_eq!(scheduler.metrics.per_owner_cap_rejections, 1);
    assert_eq!(scheduler.metrics.global_cap_fallbacks, 0);
    assert_eq!(
        scheduler.prepare_owner(cacheable_owner, true, None),
        OwnerScheduleDecision::Reuse(OwnerSolveOutcome::NoProgress),
    );
    assert_eq!(
        scheduler.prepare_owner(oversized_owner, true, None),
        OwnerScheduleDecision::Solve,
    );
}

#[test]
fn owners_cap_forces_every_owner_through_the_real_solve() {
    let mut scheduler = skipping_scheduler_with_budget(OwnerDirtySchedulerBudget {
        max_owners: Some(0),
        ..OwnerDirtySchedulerBudget::default()
    });
    scheduler.publish_record(
        DefId(1),
        OwnerSolveOutcome::NoProgress,
        vec![DependencyKey::ConstraintBounds(TypeVar(1))],
    );

    assert_global_cap_refuses_all_skips(&mut scheduler);
}

#[test]
fn dependency_keys_cap_forces_every_owner_through_the_real_solve() {
    let dependency = DependencyKey::ConstraintBounds(TypeVar(1));
    let mut scheduler = skipping_scheduler_with_budget(OwnerDirtySchedulerBudget {
        max_dependency_keys: Some(0),
        ..OwnerDirtySchedulerBudget::default()
    });
    scheduler.drain_mutations(
        vec![MethodRoleMutation::Changed {
            serial: MutationSerial::new(1),
            key: dependency.clone(),
        }],
        true,
    );
    scheduler.publish_record(DefId(1), OwnerSolveOutcome::NoProgress, vec![dependency]);

    assert_global_cap_refuses_all_skips(&mut scheduler);
}

#[test]
fn reverse_edges_cap_forces_every_owner_through_the_real_solve() {
    let mut scheduler = skipping_scheduler_with_budget(OwnerDirtySchedulerBudget {
        max_reverse_edges: Some(0),
        ..OwnerDirtySchedulerBudget::default()
    });
    scheduler.publish_record(
        DefId(1),
        OwnerSolveOutcome::NoProgress,
        vec![DependencyKey::ConstraintBounds(TypeVar(1))],
    );

    assert_global_cap_refuses_all_skips(&mut scheduler);
}

#[test]
fn journal_burst_cap_forces_every_owner_through_the_real_solve() {
    let mut scheduler = skipping_scheduler_with_budget(OwnerDirtySchedulerBudget {
        max_journal_burst: Some(0),
        ..OwnerDirtySchedulerBudget::default()
    });
    scheduler.drain_mutations(
        vec![MethodRoleMutation::Changed {
            serial: MutationSerial::new(1),
            key: DependencyKey::ConstraintBounds(TypeVar(1)),
        }],
        true,
    );

    assert_eq!(scheduler.metrics.peak_journal_burst, 1);
    assert_global_cap_refuses_all_skips(&mut scheduler);
}

#[test]
fn retained_bytes_cap_forces_every_owner_through_the_real_solve() {
    let mut scheduler = skipping_scheduler_with_budget(OwnerDirtySchedulerBudget {
        max_retained_bytes: Some(0),
        ..OwnerDirtySchedulerBudget::default()
    });
    scheduler.publish_record(
        DefId(1),
        OwnerSolveOutcome::NoProgress,
        vec![DependencyKey::ConstraintBounds(TypeVar(1))],
    );

    assert_global_cap_refuses_all_skips(&mut scheduler);
}

#[test]
fn capped_global_fallback_preserves_production_poly_output() {
    let source = "role Display 'a:\n  our x.display: unit\nmy show = \\x -> x.display\n";
    let always_solve = crate::dump::dump_source(source);
    let capped = with_new_session_budget(
        OwnerDirtySchedulerBudget {
            max_owners: Some(0),
            ..OwnerDirtySchedulerBudget::default()
        },
        || {
            with_owner_dirty_scheduler_benchmark_for_new_sessions(|| {
                crate::dump::dump_source(source)
            })
        },
    );

    assert_eq!(capped.text, always_solve.text);
    assert_eq!(capped.lowering.errors, always_solve.lowering.errors);
    let scheduler = capped
        .lowering
        .session
        .owner_dirty_scheduler
        .as_ref()
        .expect("capped compile scheduler");
    assert!(scheduler.metrics.global_cap_fallbacks > 0);
    assert!(scheduler.metrics.full_fallbacks > 0);
}

fn with_new_session_budget<T>(budget: OwnerDirtySchedulerBudget, f: impl FnOnce() -> T) -> T {
    struct BudgetGuard(Option<OwnerDirtySchedulerBudget>);
    impl Drop for BudgetGuard {
        fn drop(&mut self) {
            NEW_SESSION_BUDGET_OVERRIDE.with(|current| current.set(self.0));
        }
    }

    let previous = NEW_SESSION_BUDGET_OVERRIDE.with(|current| current.replace(Some(budget)));
    let _guard = BudgetGuard(previous);
    f()
}

fn skipping_scheduler_with_budget(
    budget: OwnerDirtySchedulerBudget,
) -> MethodRoleOwnerDirtyScheduler {
    MethodRoleOwnerDirtyScheduler {
        permit_owner_skips: true,
        budget,
        ..MethodRoleOwnerDirtyScheduler::default()
    }
}

fn assert_global_cap_refuses_all_skips(scheduler: &mut MethodRoleOwnerDirtyScheduler) {
    assert!(scheduler.records.is_empty());
    assert!(scheduler.force_all_dirty_this_pass);
    assert_eq!(scheduler.metrics.full_fallbacks, 1);
    assert_eq!(scheduler.metrics.global_cap_fallbacks, 1);
    for owner in [DefId(1), DefId(2)] {
        assert_eq!(
            scheduler.prepare_owner(owner, true, None),
            OwnerScheduleDecision::Solve,
        );
    }
}

fn scheduler_with_records<const N: usize>(
    records: [(DefId, DependencyKey); N],
) -> MethodRoleOwnerDirtyScheduler {
    let mut scheduler = MethodRoleOwnerDirtyScheduler::default();
    for (owner, dependency) in records {
        scheduler.publish_record(owner, OwnerSolveOutcome::NoProgress, vec![dependency]);
    }
    scheduler
}

fn skipping_scheduler_with_records<const N: usize>(
    records: [(DefId, DependencyKey); N],
) -> MethodRoleOwnerDirtyScheduler {
    let mut scheduler = scheduler_with_records(records);
    scheduler.permit_owner_skips = true;
    scheduler
}

fn every_dependency_key(owner: DefId) -> Vec<DependencyKey> {
    let role = CompactRoleConstraint {
        role: vec!["Applied".to_string()],
        inputs: Vec::new(),
        associated: Vec::new(),
    };
    vec![
        DependencyKey::SccRoot(owner),
        DependencyKey::OwnerRawRoles(owner),
        DependencyKey::OwnerSelections(owner),
        DependencyKey::Selection(SelectId(4)),
        DependencyKey::ConstraintBounds(TypeVar(5)),
        DependencyKey::ConstraintNeighbors(TypeVar(6)),
        DependencyKey::ConstraintSubtractFacts(TypeVar(7)),
        DependencyKey::ConstraintLevel(TypeVar(8)),
        DependencyKey::ConstraintBirthLevel(TypeVar(9)),
        DependencyKey::ConstraintPrePopFamilies(TypeVar(10)),
        DependencyKey::MethodTaint(TypeVar(11)),
        DependencyKey::CandidateBucket(vec!["Candidate".to_string()]),
        DependencyKey::AppliedResolution(RoleResolutionKey {
            demand: role.clone(),
            candidate: role,
        }),
    ]
}
