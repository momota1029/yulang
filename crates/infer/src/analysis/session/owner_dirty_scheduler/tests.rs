use super::*;

use poly::expr::Arena as PolyArena;

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
    scheduler.begin_pass(&[earlier, later], &MethodTaintIndex::default());

    scheduler.prepare_owner(earlier, true, None);
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
    scheduler.prepare_owner(later, true, None);

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
    scheduler.begin_pass(&[earlier, later], &MethodTaintIndex::default());

    scheduler.prepare_owner(earlier, true, None);
    scheduler.finish_owner(
        earlier,
        OwnerSolveOutcome::NoProgress,
        vec![earlier_dependency.clone()],
        Duration::ZERO,
        true,
    );
    scheduler.prepare_owner(later, true, None);
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
    scheduler.prepare_owner(earlier, true, None);
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

fn scheduler_with_records<const N: usize>(
    records: [(DefId, DependencyKey); N],
) -> MethodRoleOwnerDirtyScheduler {
    let mut scheduler = MethodRoleOwnerDirtyScheduler::default();
    for (owner, dependency) in records {
        scheduler.publish_record(owner, OwnerSolveOutcome::NoProgress, vec![dependency]);
    }
    scheduler
}
