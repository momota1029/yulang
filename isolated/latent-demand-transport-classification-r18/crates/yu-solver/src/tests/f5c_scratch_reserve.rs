use super::*;

#[test]
fn f5c_scratch_changed_failed_reserves_sample_and_retry() {
    let lanes = [
        F5bCapacityLane::InstantiationSubstitution,
        F5bCapacityLane::InstantiationPositiveMemo,
        F5bCapacityLane::InstantiationNegativeMemo,
        F5bCapacityLane::InstantiationPositiveEffects,
        F5bCapacityLane::InstantiationNegativeEffects,
        F5bCapacityLane::InstantiationParts,
        F5bCapacityLane::InstantiationWork,
    ];
    for (index, lane) in lanes.into_iter().enumerate() {
        let (mut session, routes) = f5c_shared_closed_incoming_fixture("scratch-post-reserve");
        let before = RouteCheckpoint::capture(&session);
        let initial_capacity = session.resource_ledger.instantiation_lanes[index].actual_capacity;
        let initial_growths = session.resource_ledger.instantiation_lanes[index].capacity_growths;
        let samples = session.resource_boundary_samples;
        let outer = session.incoming_post_rollback_sample_attempts;
        incoming_sample_trace::start();
        inject_next_f5b_post_reserve_failure(lane);

        assert_eq!(
            session.route_incoming(&routes[0]),
            Err(SolveAvailabilityError::IdentityExhausted),
            "{lane:?}"
        );
        assert_eq!(
            F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
            None
        );
        before.assert_restored(&session);
        let physical = &session.resource_ledger.instantiation_lanes[index];
        assert!(physical.actual_capacity > initial_capacity, "{lane:?}");
        assert_eq!(physical.capacity_growths, initial_growths + 1, "{lane:?}");
        assert_eq!(session.incoming_post_rollback_sample_attempts, outer + 1);
        let trace = incoming_sample_trace::finish("scratch-post-reserve", 1);
        assert_eq!(trace.attempts, 1, "{lane:?}");
        assert_eq!(
            trace
                .event_lanes
                .get(&("InstantiationScratch".into(), format!("{lane:?}"))),
            Some(&1),
            "failed reserve growth must have an event sample: {lane:?}"
        );
        assert_eq!(
            trace.named_samples.get("route_incoming_inner-scratch-peak"),
            Some(&1),
            "{lane:?}"
        );
        assert_eq!(
            trace.named_samples.get("post-rollback"),
            Some(&1),
            "{lane:?}"
        );
        assert_eq!(
            session.resource_boundary_samples,
            samples + trace.samples,
            "event samples plus separate scratch-peak and post-rollback samples: {lane:?}"
        );
        assert_eq!(trace.samples, trace.event_samples + 2, "{lane:?}");
        assert_eq!(
            session
                .execution_counters
                .instantiation_substitution_retained_bytes,
            session
                .instantiation_scratch
                .checked_retained_bytes()
                .unwrap()
        );
        assert_eq!(
            session.resource_ledger.inference_session_retained_bytes,
            session.execution_counters.inference_session_retained_bytes
        );
        session.route_incoming(&routes[0]).unwrap();
        assert_eq!(session.store.facts().len(), 1, "{lane:?}");
    }
}

#[test]
fn f5c_scratch_no_growth_reserve_ignores_exhausted_growth_counters() {
    let mut target = Vec::<u8>::with_capacity(1);
    let mut requested = 0;
    let mut growths = usize::MAX;
    let mut lane_requested = [0; 7];
    let mut lane_growths = [usize::MAX; 7];
    let mut growth_sample_pending = false;

    assert_eq!(
        reserve_instantiation(
            &mut target,
            0,
            F5bCapacityLane::InstantiationWork,
            Vec::capacity,
            &mut requested,
            &mut growths,
            &mut lane_requested,
            &mut lane_growths,
            &mut growth_sample_pending,
        ),
        Ok(false)
    );
    assert_eq!(target.capacity(), 1);
    assert!(!growth_sample_pending);
}

#[test]
fn f5c_scratch_growth_counter_overflow_keeps_physical_change_pending() {
    let mut target = Vec::<u8>::new();
    let mut requested = 0;
    let mut growths = usize::MAX;
    let mut lane_requested = [0; 7];
    let mut lane_growths = [0; 7];
    let mut growth_sample_pending = false;
    inject_next_f5b_post_reserve_failure(F5bCapacityLane::InstantiationWork);
    assert_eq!(
        reserve_instantiation(
            &mut target,
            1,
            F5bCapacityLane::InstantiationWork,
            Vec::capacity,
            &mut requested,
            &mut growths,
            &mut lane_requested,
            &mut lane_growths,
            &mut growth_sample_pending,
        ),
        Err(SolveAvailabilityError::IdentityExhausted)
    );
    assert_eq!(
        F5B_INJECTED_POST_RESERVE_FAILURE.with(|failure| failure.get()),
        None
    );
    assert!(target.capacity() > 0);
    assert!(growth_sample_pending);
    assert_eq!(growths, usize::MAX);
    assert_eq!(lane_growths[6], 0);
}
