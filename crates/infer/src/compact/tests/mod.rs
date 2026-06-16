use super::analysis::{
    coalesce_by_co_occurrence, eliminate_polar_variables, sandwich_compact_root,
    sandwich_compact_root_with_roles,
};

use poly::types::{Neg, Pos, StackWeight, SubtractId};

use super::*;
use crate::constraints::{ConstraintMachine, ConstraintWeights, TypeLevel};
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

mod case_01;
mod case_02;
