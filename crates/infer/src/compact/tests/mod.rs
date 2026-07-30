use super::analysis::{
    coalesce_by_co_occurrence, eliminate_polar_variables, sandwich_compact_root,
    sandwich_compact_root_with_roles,
};

use poly::types::{Neg, Pos, StackWeight, SubtractId};

use super::*;
use crate::compact::merge::{merge_compact_types_with_sink, singleton_row_item_map};
use crate::constraints::{
    ConstraintMachine, ConstraintWeights, LeftConstraintWeight, RightConstraintWeight, TypeLevel,
};
use crate::roles::{RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg};

fn invariant_var(machine: &mut ConstraintMachine, var: TypeVar) -> NeuId {
    let lower = machine.alloc_pos(Pos::Var(var));
    let upper = machine.alloc_neg(Neg::Var(var));
    machine.alloc_neu(Neu::Bounds(lower, upper))
}

fn apply_merge_constraints_until_quiescent(machine: &mut ConstraintMachine, root: TypeVar) -> bool {
    let mut applied = FxHashSet::<CompactMergeConstraintKey>::default();
    let mut saw_change = false;
    for _ in 0..8 {
        let (_, constraints) = compact_type_var_recording_merge_constraints(&*machine, root);
        let changed = apply_compact_merge_constraints(machine, constraints, &mut applied);
        saw_change |= changed;
        if !changed {
            return saw_change;
        }
    }
    panic!("compact merge constraints did not reach quiescence");
}

#[test]
fn raw_and_scheme_projection_collectors_are_identical_while_mode_is_inert() {
    let mut machine = ConstraintMachine::new();
    let root = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["value".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Var(root));
    machine.subtype(
        lower,
        upper,
        crate::constraints::OriginId::unknown_internal(),
    );

    let raw = CompactCollector::new(&machine).compact_root(root);
    let scheme = CompactCollector::new_for_scheme(&machine).compact_root(root);
    assert_eq!(raw, scheme);

    let raw = CompactCollector::new_recording(&machine).compact_root_with_merge_constraints(root);
    let scheme = CompactCollector::new_recording_for_scheme(&machine)
        .compact_root_with_merge_constraints(root);
    assert_eq!(raw, scheme);
}

mod case_01;
mod case_02;

use case_02::{compact_path_is, compact_row_contains_path, compact_type_contains_var, role_arg};
