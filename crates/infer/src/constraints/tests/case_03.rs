use super::*;

#[test]
fn duplicate_bound_provenance_merges_without_semantic_progress() {
    let mut machine = ConstraintMachine::new();
    let first = machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    let second = machine
        .alloc_source_boundary(ConstraintOriginKind::Return)
        .origin();
    let target = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["value".into()], vec![]));

    machine.constrain_pos_to_var_direct_many([(lower, target)], first);
    let semantic_epoch = machine.epoch();
    let provenance_epoch = machine.provenance_epoch();
    let event_count = machine.events().len();
    let ConstraintEvent::LowerBoundAdded { record, .. } = machine.events()[0] else {
        panic!("lower-bound event")
    };

    machine.constrain_pos_to_var_direct_many([(lower, target)], second);

    assert_eq!(machine.epoch(), semantic_epoch);
    assert!(machine.provenance_epoch() > provenance_epoch);
    assert_eq!(machine.events().len(), event_count);
    let record = machine
        .bounds()
        .record(record)
        .expect("stable bound record");
    assert_eq!(record.state(), BoundRecordState::Ordinary);
    assert_eq!(
        record.derivations(),
        &[
            BoundDerivation::Origin(first),
            BoundDerivation::Origin(second)
        ]
    );
    assert_eq!(
        machine
            .timing()
            .stable_records
            .lower_duplicate_provenance_merges,
        1
    );
}

#[test]
fn evidence_promotion_preserves_bound_record_identity() {
    let mut machine = ConstraintMachine::new();
    let target = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Var(TypeVar(1)));
    let weights = ConstraintWeights::empty();
    let evidence = machine.bounds.add_evidence_lower(
        target,
        lower,
        weights.clone(),
        BoundDerivation::ReplayEvidence(BinaryReplayDerivation {
            pivot: target,
            lower: BoundRecordId(0),
            upper: BoundRecordId(1),
            rule: ReplayRule::LowerBoundAdded,
        }),
    );
    machine.record_bound_provenance(evidence, BoundDirection::Lower, true);
    machine.record_effective_bounds_mutation(target);

    let promoted = machine.bounds.add_lower(
        target,
        lower,
        weights,
        BoundDerivation::Origin(OriginId::unknown_internal()),
    );
    machine.record_bound_provenance(promoted, BoundDirection::Lower, false);
    machine.record_effective_bounds_mutation(target);

    assert_eq!(promoted.id, evidence.id);
    assert!(promoted.promoted);
    assert_eq!(
        machine.bounds().record(promoted.id).unwrap().state(),
        BoundRecordState::Ordinary
    );
    let bounds = machine.bounds().of(target).unwrap();
    assert_eq!(bounds.evidence_lower_count(), 0);
    assert_eq!(bounds.lowers().len(), 1);
    assert_eq!(
        machine
            .timing()
            .stable_records
            .promotions_identity_preserved,
        1
    );
}

#[test]
fn genuine_replay_chain_keeps_both_exact_bound_parents() {
    let mut machine = ConstraintMachine::new();
    let origin = machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["genuine-lower".into()], vec![]));
    let upper = machine.alloc_neg(Neg::Con(vec!["genuine-upper".into()], vec![]));

    machine.constrain_pos_to_var_direct_many([(lower, pivot)], origin);
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    machine.subtype(pivot_pos, upper, origin);

    let witnesses = machine
        .debug_nominal_replay_witnesses(&["genuine-lower".into()], &["genuine-upper".into()]);
    assert_eq!(witnesses.len(), 1);
    let witness = &witnesses[0];
    assert_eq!(witness.edge.derivation.pivot, pivot);
    assert_eq!(witness.lower.owner, pivot);
    assert_eq!(witness.upper.owner, pivot);
    assert!(witness.lower.origins.contains(&origin));
    assert!(witness.upper.origins.contains(&origin));
    assert!(witness.lower.source_origins.contains(&origin));
    assert!(witness.upper.source_origins.contains(&origin));

    let provenance_epoch = machine.provenance_epoch();
    assert!(!machine.merge_replay_derivation(witness.edge.result, witness.edge.derivation,));
    assert_eq!(machine.provenance_epoch(), provenance_epoch);
}

#[test]
fn duplicate_subtract_declaration_merges_origin_without_semantic_progress() {
    let mut machine = ConstraintMachine::new();
    let first = machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    let second = machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    let effect = TypeVar(0);
    let id = SubtractId(0);
    let fact = SubtractFact {
        id,
        subtractability: Subtractability::All,
    };

    machine.declared_subtract_fact_with_origin(effect, id, Subtractability::All, first);
    let semantic_epoch = machine.epoch();
    let provenance_epoch = machine.provenance_epoch();
    let event_count = machine.events().len();
    let record = machine
        .subtracts()
        .record_id(effect, &fact)
        .expect("stable fact record");

    machine.declared_subtract_fact_with_origin(effect, id, Subtractability::All, second);

    assert_eq!(machine.epoch(), semantic_epoch);
    assert!(machine.provenance_epoch() > provenance_epoch);
    assert_eq!(machine.events().len(), event_count);
    assert_eq!(machine.subtract_declaration_origins(id), &[first, second]);
    assert_eq!(
        machine.subtracts().record(record).unwrap().derivations(),
        &[
            SubtractFactDerivation::Declaration(first),
            SubtractFactDerivation::Declaration(second),
        ]
    );
}

#[test]
fn duplicate_root_origins_share_one_semantic_record() {
    let mut machine = ConstraintMachine::new();
    let application = machine.alloc_source_boundary(ConstraintOriginKind::ApplicationArgument);
    let annotation = machine.alloc_source_boundary(ConstraintOriginKind::Annotation);
    assert_ne!(application.boundary(), annotation.boundary());
    assert_ne!(application.origin(), annotation.origin());

    let lower = machine.alloc_pos(Pos::Con(vec!["lower".into()], vec![]));
    let upper = machine.alloc_neg(Neg::Con(vec!["upper".into()], vec![]));
    machine.subtype(lower, upper, application.origin());
    machine.subtype(lower, upper, annotation.origin());

    assert_eq!(machine.canonical_constraints.len(), 1);
    assert_eq!(machine.constraint_records.len(), 1);
    assert_eq!(
        machine.constraint_records[0].root_origins,
        vec![application.origin(), annotation.origin()]
    );
    assert_eq!(
        machine.timing().root_origins,
        ConstraintOriginCoverage {
            application_argument: 1,
            annotation: 1,
            ..ConstraintOriginCoverage::default()
        }
    );
}

#[test]
fn union_child_traces_to_root_origin() {
    let mut machine = ConstraintMachine::new();
    let origin = machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    let left = machine.alloc_pos(Pos::Con(vec!["left".into()], vec![]));
    let right = machine.alloc_pos(Pos::Con(vec!["right".into()], vec![]));
    let lower = machine.alloc_pos(Pos::Union(left, right));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], vec![]));
    machine.subtype(lower, upper, origin);

    assert_direct_structural_trace(
        &machine,
        left,
        upper,
        StructuralDerivationRule::UnionBranch {
            branch: StructuralIndex(0),
        },
        origin,
    );
}

#[test]
fn tuple_child_trace_retains_element_index() {
    let mut machine = ConstraintMachine::new();
    let origin = machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    let first_lower = machine.alloc_pos(Pos::Con(vec!["first_lower".into()], vec![]));
    let second_lower = machine.alloc_pos(Pos::Con(vec!["second_lower".into()], vec![]));
    let first_upper = machine.alloc_neg(Neg::Con(vec!["first_upper".into()], vec![]));
    let second_upper = machine.alloc_neg(Neg::Con(vec!["second_upper".into()], vec![]));
    let lower = machine.alloc_pos(Pos::Tuple(vec![first_lower, second_lower]));
    let upper = machine.alloc_neg(Neg::Tuple(vec![first_upper, second_upper]));
    machine.subtype(lower, upper, origin);

    assert_direct_structural_trace(
        &machine,
        second_lower,
        second_upper,
        StructuralDerivationRule::TupleElement {
            index: StructuralIndex(1),
        },
        origin,
    );
}

#[test]
fn function_argument_child_traces_contravariant_position() {
    let mut machine = ConstraintMachine::new();
    let origin = machine
        .alloc_source_boundary(ConstraintOriginKind::ApplicationArgument)
        .origin();
    let expected_arg = machine.alloc_neg(Neg::Con(vec!["expected".into()], vec![]));
    let actual_arg = machine.alloc_pos(Pos::Con(vec!["actual".into()], vec![]));
    let top = machine.alloc_neg(Neg::Top);
    let bot = machine.alloc_pos(Pos::Bot);
    let lower = machine.alloc_pos(Pos::Fun {
        arg: expected_arg,
        arg_eff: top,
        ret_eff: bot,
        ret: bot,
    });
    let upper = machine.alloc_neg(Neg::Fun {
        arg: actual_arg,
        arg_eff: bot,
        ret_eff: top,
        ret: top,
    });
    machine.subtype(lower, upper, origin);

    assert_direct_structural_trace(
        &machine,
        actual_arg,
        expected_arg,
        StructuralDerivationRule::FunctionArgument,
        origin,
    );
}

fn assert_direct_structural_trace(
    machine: &ConstraintMachine,
    lower: PosId,
    upper: NegId,
    rule: StructuralDerivationRule,
    origin: OriginId,
) {
    let child = machine
        .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
        .expect("derived child record");
    let trace = machine.debug_trace_constraint(child);
    assert_eq!(trace.len(), 2);
    assert_eq!(trace[0].record, child);
    assert_eq!(trace[0].key.lower, lower);
    assert_eq!(trace[0].key.upper, upper);
    assert_eq!(trace[0].structural_derivations.len(), 1);
    assert_eq!(trace[0].structural_derivations[0].rule, rule);
    let parent = trace[0].structural_derivations[0].parent;
    assert_eq!(trace[1].record, parent);
    assert_eq!(trace[1].root_origins, vec![origin]);
}

#[test]
fn neg_stack_peel_composes_stack_before_existing_right_weight() {
    let mut machine = ConstraintMachine::new();
    let target = TypeVar(0);
    let subtract = SubtractId(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["value".into()], vec![]));
    let inner = machine.alloc_neg(Neg::Var(target));
    let upper = machine.alloc_neg(Neg::Stack {
        inner,
        weight: StackWeight::push(
            subtract,
            Subtractability::Set(vec!["io".into()], Vec::new()),
        ),
    });
    let weights = ConstraintWeights {
        left: LeftConstraintWeight::empty(),
        right: RightConstraintWeight::pop(subtract),
    };

    machine.weighted_subtype(
        lower,
        weights,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let bounds = machine.bounds().of(target).expect("target bounds");
    assert_eq!(
        bounds.lowers(),
        &[WeightedLowerBound {
            pos: lower,
            weights: ConstraintWeights::empty()
        }]
    );
}

#[test]
fn non_subtract_adds_left_weight_before_continuing() {
    let mut machine = ConstraintMachine::new();
    machine.register_effect_family_path(vec!["io".into()]);
    let target = TypeVar(0);
    let inner = machine.alloc_pos(Pos::Con(vec!["io".into()], vec![]));
    let subtract = SubtractId(0);
    let lower = machine.alloc_pos(Pos::NonSubtract(inner, StackWeight::pop(subtract)));
    let upper = machine.alloc_neg(Neg::Var(target));

    machine.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let bounds = machine.bounds().of(target).expect("target bounds");
    assert_eq!(
        bounds.lowers(),
        &[WeightedLowerBound {
            pos: inner,
            weights: ConstraintWeights {
                left: LeftConstraintWeight::from_ids([subtract]),
                right: RightConstraintWeight::empty()
            }
        }]
    );
}
