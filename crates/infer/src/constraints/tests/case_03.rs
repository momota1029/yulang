use super::*;

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
        left: StackWeight::empty(),
        right: StackWeight::pop(subtract),
    };

    machine.weighted_subtype(lower, weights, upper);

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
    let lower = machine.alloc_pos(Pos::NonSubtract(inner, subtract));
    let upper = machine.alloc_neg(Neg::Var(target));

    machine.subtype(lower, upper);

    let bounds = machine.bounds().of(target).expect("target bounds");
    assert_eq!(
        bounds.lowers(),
        &[WeightedLowerBound {
            pos: inner,
            weights: ConstraintWeights {
                left: ConstraintWeight::from_ids([subtract]),
                right: ConstraintWeight::empty()
            }
        }]
    );
}
