use super::*;

#[test]
fn unit_comparison_keeps_primitive_shapes_distinct() {
    let batch = collect(module("my f = 1", "unit-comparison"));
    let mut session = InferenceSession::new(batch);
    let argument = session.batch.collected_leaf_term(Leaf::IntNegative);
    let argument_effect = session.batch.collected_leaf_term(Leaf::EmptyEffectNegative);
    let result_effect = session.batch.collected_leaf_term(Leaf::EffectBottomPositive);
    let result = session.batch.collected_leaf_term(Leaf::IntPositive);
    let function = session.positive_function_term(argument, argument_effect, result_effect, result).unwrap();
    let negative = session.negative_function_term(result, result_effect, argument_effect, argument).unwrap();
    for (lower, upper, shapes) in [
        (ValueEndpointKey::UnitPositive, ValueEndpointKey::IntNegative, Some((ValueShape::Unit, ValueShape::Int))),
        (ValueEndpointKey::IntPositive, ValueEndpointKey::UnitNegative, Some((ValueShape::Int, ValueShape::Unit))),
        (ValueEndpointKey::UnitPositive, ValueEndpointKey::NegativeFunction(negative), Some((ValueShape::Unit, ValueShape::Function))),
        (ValueEndpointKey::PositiveFunction(function), ValueEndpointKey::UnitNegative, Some((ValueShape::Function, ValueShape::Unit))),
        (ValueEndpointKey::UnitPositive, ValueEndpointKey::BottomNegative, Some((ValueShape::Unit, ValueShape::Bottom))),
        (ValueEndpointKey::UnitPositive, ValueEndpointKey::UnitNegative, None),
        (ValueEndpointKey::UnitPositive, ValueEndpointKey::TopNegative, None),
        (ValueEndpointKey::BottomPositive, ValueEndpointKey::UnitNegative, None),
    ] {
        assert_eq!(InferenceSession::incompatible_value_shapes(CanonicalValuePairKey { lower, upper }), shapes);
        assert_eq!(session.apply_value_task(CanonicalValuePairKey { lower, upper }).unwrap(), 0);
    }
}

#[test]
fn unit_generalization_normalization_and_closed_roundtrip() {
    let meter = DraftHeapMeter::default();
    let batch = collect(module("my f = 1", "unit-generalization"));
    let mut session = InferenceSession::new(batch);
    let definition = session.batch.definitions[0].definition.clone();
    let root = session.batch.definitions[0].root.clone();
    let row = session.live_components[session.batch.root_component_positions[&root].component].ordinal;
    session.apply_value_task(CanonicalValuePairKey { lower: ValueEndpointKey::UnitPositive, upper: ValueEndpointKey::ValueRow(row) }).unwrap();
    let draft = session.generalization_draft(&meter, &definition).unwrap();
    assert_eq!(draft.predicate, F5cPositive::Unit);
    let mut drafts = [draft];
    let mut stats = f5c_normalization::NormalizationStats::default();
    f5c_normalization::normalize_component_with_stats(&meter, &mut drafts, &mut stats).unwrap();
    assert_eq!(drafts[0].predicate, F5cPositive::Unit);
    let mut closed = ClosedTypeFinalizationSession::try_new().unwrap();
    let finalized = InferenceSession::finalize_generalization_draft(&mut closed, &drafts[0], false).unwrap();
    let (scheme, _) = finalized.into_parts();
    let decoded = InferenceSession::decode_closed_scheme(&meter, &closed, &scheme).unwrap();
    assert_eq!(decoded.predicate, F5cPositive::Unit);
}

#[test]
fn unit_bound_summary_and_fresh_rows_roll_back_atomically() {
    let batch = collect(module("my f = 1", "unit-rollback"));
    let mut session = InferenceSession::new(batch);
    let row = session.fresh_value_at_level(1).unwrap();
    let count = session.bounds.len();
    let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 201);
    let cause = CauseId::for_occurrence(occurrence.clone());
    let result: Result<(), SolveAvailabilityError> = session.with_route_transaction(|session| {
        session.constrain_live_value(CanonicalValuePairKey { lower: ValueEndpointKey::UnitPositive, upper: ValueEndpointKey::ValueRow(row) }, &occurrence, &cause)?;
        assert!(session.bounds[row as usize].has_unit_positive_lower);
        session.fresh_value_at_level(1)?;
        Err(SolveAvailabilityError::IdentityExhausted)
    });
    assert_eq!(result, Err(SolveAvailabilityError::IdentityExhausted));
    assert_eq!(session.bounds.len(), count);
    assert!(!session.bounds[row as usize].has_unit_positive_lower);
    assert!(session.bounds[row as usize].exact_non_variable_lowers.is_empty());
    session.constrain_live_value(CanonicalValuePairKey { lower: ValueEndpointKey::UnitPositive, upper: ValueEndpointKey::ValueRow(row) }, &occurrence, &cause).unwrap();
    assert!(session.bounds[row as usize].has_unit_positive_lower);
}

#[test]
fn unit_diagnostic_buckets_keep_kind_and_distance_order_and_replay() {
    let terminal = CanonicalValuePairKey {
        lower: ValueEndpointKey::UnitPositive,
        upper: ValueEndpointKey::IntNegative,
    };
    let witness = |lower, upper, distance| DiagnosticWitness {
        terminal,
        kind: SolverErrorKind::IncompatibleValue { lower, upper },
        distance,
        first_field: None,
    };
    let int_unit = witness(ValueShape::Int, ValueShape::Unit, 0);
    let function_bottom = witness(ValueShape::Function, ValueShape::Bottom, 0);
    let unit_int = witness(ValueShape::Unit, ValueShape::Int, 0);
    let bucket = |w| InferenceSession::diagnostic_bucket(w, 0, 4).unwrap();
    assert!(bucket(int_unit) < bucket(function_bottom));
    assert!(bucket(function_bottom) < bucket(unit_int));
    assert!(bucket(witness(ValueShape::Unit, ValueShape::Unit, 0))
        < bucket(witness(ValueShape::Bottom, ValueShape::Bottom, 1)));
    assert_eq!(InferenceSession::diagnostic_bucket(
        witness(ValueShape::Function, ValueShape::Function, 1), 0, 3).unwrap(), 89);

    let mut session = InferenceSession::new(collect(module("my f = 1", "unit-diagnostic")));
    for (index, key) in [terminal, CanonicalValuePairKey {
        lower: ValueEndpointKey::IntPositive,
        upper: ValueEndpointKey::UnitNegative,
    }, terminal].into_iter().enumerate() {
        let occurrence = ConstraintOccurrenceId::new(session.batch.projection_order[0].clone(), 211 + index as u8);
        let cause = CauseId::for_occurrence(occurrence.clone());
        session.constrain_live_value(key, &occurrence, &cause).unwrap();
        assert_eq!(session.errors[index].kind, SolverErrorKind::IncompatibleValue {
            lower: if index == 1 { ValueShape::Int } else { ValueShape::Unit },
            upper: if index == 1 { ValueShape::Unit } else { ValueShape::Int },
        });
    }
}

#[test]
fn unit_flat_generalization_normalization_and_closed_parity() {
    let meter = DraftHeapMeter::default();
    let mut sessions = Vec::new();
    for flat in [false, true] {
        let mut session = InferenceSession::new(collect(module("my f = 1", "unit-flat-parity")));
        let root = session.batch.definitions[0].root.clone();
        let row = session.live_components[session.batch.root_component_positions[&root].component].ordinal;
        session.apply_value_task(CanonicalValuePairKey {
            lower: ValueEndpointKey::UnitPositive,
            upper: ValueEndpointKey::ValueRow(row),
        }).unwrap();
        if flat {
            let mut generalizer = F5cGeneralizer::with_source_meter(&session, &meter);
            let candidate = generalizer.build_flat_candidate(row, false).unwrap();
            let predicate = candidate.draft.predicate.unwrap();
            assert!(matches!(candidate.draft.positive_nodes[predicate.0 as usize], crate::f5c_draft::PositiveNode::Unit));
            generalizer.release_normalized_candidate(candidate);
        }
        session.flat_candidate_enabled = flat;
        session.execute_scc_plan().unwrap();
        let scheme = session.schemes[0].as_ref().unwrap();
        let decoded = InferenceSession::decode_closed_scheme(&meter, session.finalization.as_ref().unwrap(), scheme).unwrap();
        assert_eq!(decoded.predicate, F5cPositive::Unit);
        if flat { assert_eq!(session.resource_ledger.flat_finalizer_calls, 1); }
        sessions.push(session);
    }
    let boxed = &sessions[0];
    let flat = &sessions[1];
    assert!(boxed.finalization.as_ref().unwrap().scheme_view(boxed.schemes[0].as_ref().unwrap()).unwrap()
        .alpha_eq(flat.finalization.as_ref().unwrap().scheme_view(flat.schemes[0].as_ref().unwrap()).unwrap()));
}
