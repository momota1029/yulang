use super::*;

use crate::arena::Arena;
use crate::roles::RoleConstraintArg;
use poly::types::{Neg, NegId, Pos, PosId};

#[test]
fn role_input_rejects_variable_only_aliases_and_top() {
    let mut infer = Arena::new();
    let positive_var = infer.fresh_type_var();
    let negative_var = infer.fresh_type_var();
    let positive_alias = infer.alloc_pos(Pos::Var(positive_var));
    let negative_alias = infer.alloc_neg(Neg::Var(negative_var));
    let bottom = infer.alloc_pos(Pos::Bot);
    let top = infer.alloc_neg(Neg::Top);

    let inputs = [
        compact_role_input(&infer, positive_alias, top),
        compact_role_input(&infer, bottom, negative_alias),
        compact_role_input(&infer, bottom, top),
    ];

    assert!(
        inputs
            .iter()
            .all(|input| !role_input_has_concrete_component(input))
    );
}

#[test]
fn role_input_accepts_each_concrete_component_shape() {
    let mut infer = Arena::new();
    let bottom = infer.alloc_pos(Pos::Bot);
    let top = infer.alloc_neg(Neg::Top);
    let never = infer.alloc_neg(Neg::Bot);
    let builtin = infer.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let positive_con = infer.alloc_pos(Pos::Con(vec!["PositiveNominal".into()], Vec::new()));
    let negative_con = infer.alloc_neg(Neg::Con(vec!["NegativeNominal".into()], Vec::new()));
    let function = infer.alloc_pos(Pos::Fun {
        arg: top,
        arg_eff: top,
        ret_eff: bottom,
        ret: bottom,
    });
    let record = infer.alloc_pos(Pos::Record(Vec::new()));
    let record_spread = infer.alloc_pos(Pos::RecordTailSpread {
        fields: Vec::new(),
        tail: bottom,
    });
    let poly_variant = infer.alloc_pos(Pos::PolyVariant(Vec::new()));
    let tuple = infer.alloc_pos(Pos::Tuple(Vec::new()));
    let row_item = infer.alloc_pos(Pos::Con(vec!["effect".into()], Vec::new()));
    let row = infer.alloc_pos(Pos::Row(vec![row_item]));

    let inputs = [
        ("Never/bottom", compact_role_input(&infer, bottom, never)),
        ("builtin", compact_role_input(&infer, builtin, top)),
        ("Pos::Con", compact_role_input(&infer, positive_con, top)),
        ("Neg::Con", compact_role_input(&infer, bottom, negative_con)),
        ("function", compact_role_input(&infer, function, top)),
        ("record", compact_role_input(&infer, record, top)),
        (
            "record spread",
            compact_role_input(&infer, record_spread, top),
        ),
        (
            "polymorphic variant",
            compact_role_input(&infer, poly_variant, top),
        ),
        ("tuple", compact_role_input(&infer, tuple, top)),
        ("row", compact_role_input(&infer, row, top)),
    ];

    for (shape, input) in inputs {
        assert!(
            role_input_has_concrete_component(&input),
            "{shape} should be a concrete role input component"
        );
    }
}

#[test]
fn role_constraint_could_resolve_requires_concrete_information_for_every_input() {
    let mut infer = Arena::new();
    let first_var = infer.fresh_type_var();
    let second_var = infer.fresh_type_var();
    let first_alias = infer.alloc_pos(Pos::Var(first_var));
    let second_alias = infer.alloc_neg(Neg::Var(second_var));
    let bottom = infer.alloc_pos(Pos::Bot);
    let top = infer.alloc_neg(Neg::Top);
    let builtin = infer.alloc_pos(Pos::Con(vec!["int".into()], Vec::new()));
    let nominal = infer.alloc_neg(Neg::Con(vec!["Concrete".into()], Vec::new()));

    let all_variable = role_constraint(vec![
        compact_role_input(&infer, first_alias, top),
        compact_role_input(&infer, bottom, second_alias),
    ]);
    let concrete = role_constraint(vec![
        compact_role_input(&infer, builtin, top),
        compact_role_input(&infer, bottom, nominal),
    ]);

    assert!(!role_constraint_could_resolve(&all_variable));
    assert!(role_constraint_could_resolve(&concrete));
}

fn compact_role_input(infer: &Arena, lower: PosId, upper: NegId) -> CompactRoleArg {
    compact_role_constraint(
        infer.constraints(),
        &RoleConstraint {
            role: vec!["TestRole".into()],
            inputs: vec![RoleConstraintArg { lower, upper }],
            associated: Vec::new(),
        },
    )
    .inputs
    .into_iter()
    .next()
    .expect("test role should contain one input")
}

fn role_constraint(inputs: Vec<CompactRoleArg>) -> CompactRoleConstraint {
    CompactRoleConstraint {
        role: vec!["TestRole".into()],
        inputs,
        associated: Vec::new(),
    }
}
