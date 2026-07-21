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
