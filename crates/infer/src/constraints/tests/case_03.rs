use super::*;

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
