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
    let scheme = compact_type_var_for_scheme(&mut machine, root);
    assert_eq!(raw, scheme);

    let raw = CompactCollector::new_recording(&machine).compact_root_with_merge_constraints(root);
    let scheme = compact_type_var_recording_merge_constraints_for_scheme(&mut machine, root);
    assert_eq!(raw, scheme);
}

#[test]
fn scheme_compaction_excludes_covered_lower_while_raw_compaction_keeps_it() {
    let (mut machine, covered, owner, _) =
        ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(false);

    let raw = compact_type_var(&machine, owner);
    let raw_covered = raw
        .root
        .vars
        .iter()
        .filter(|var| var.var == covered)
        .collect::<Vec<_>>();
    assert_eq!(
        raw_covered.len(),
        1,
        "raw compaction keeps the covered lower as one positive component"
    );
    assert_eq!(
        raw_covered[0].origin,
        CompactVarOrigin::Secondary,
        "a Var lower remains secondary on the unchanged raw path"
    );

    let scheme = compact_type_var_for_scheme(&mut machine, owner);
    assert!(
        scheme.root.vars.iter().all(|var| var.var != covered),
        "scheme compaction excludes the lower while its only claim is covered"
    );
}

#[test]
fn scheme_compaction_projects_mixed_claim_lower_exactly_once() {
    let (mut machine, covered, owner, _) =
        ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(true);

    let scheme = compact_type_var_for_scheme(&mut machine, owner);
    let projected = scheme
        .root
        .vars
        .iter()
        .filter(|var| var.var == covered)
        .collect::<Vec<_>>();

    assert_eq!(
        projected.len(),
        1,
        "the independent claim keeps the canonical lower exactly once"
    );
    assert_eq!(projected[0].origin, CompactVarOrigin::Secondary);
}

#[test]
fn scheme_compaction_reprojects_lower_after_last_live_coverage_leaves() {
    let (mut machine, covered, owner, coverage_root) =
        ConstraintMachine::compact_scheme_projection_unmatched_route_fixture(false);

    let raw_before = compact_type_var(&machine, owner);
    let scheme_before = compact_type_var_for_scheme(&mut machine, owner);
    assert!(
        scheme_before.root.vars.iter().all(|var| var.var != covered),
        "the live covered claim initially suppresses the lower"
    );
    let epoch_before = machine.epoch();

    assert!(
        machine.remove_last_scheme_projection_coverage_for_compact_test(coverage_root),
        "the lifecycle transition removes the root's last live state"
    );
    assert!(
        machine.epoch() > epoch_before,
        "projectability transitions invalidate epoch-keyed compact caches"
    );

    let raw_after = compact_type_var(&machine, owner);
    let scheme_after = compact_type_var_for_scheme(&mut machine, owner);
    assert_eq!(
        raw_after, raw_before,
        "coverage liveness never changes the raw compact input"
    );
    assert_eq!(
        scheme_after
            .root
            .vars
            .iter()
            .filter(|var| var.var == covered)
            .count(),
        1,
        "a fresh scheme compaction call reprojects the newly uncovered lower"
    );
}

#[test]
fn no_claim_owner_has_byte_for_byte_identical_raw_and_scheme_compaction() {
    let mut machine = ConstraintMachine::new();
    let owner = TypeVar(0);
    let weighted_payload = invariant_var(&mut machine, TypeVar(1));
    let ordinary_payload = invariant_var(&mut machine, TypeVar(2));
    let weighted = machine.alloc_pos(Pos::Con(vec!["weighted".into()], vec![weighted_payload]));
    let ordinary = machine.alloc_pos(Pos::Con(vec!["ordinary".into()], vec![ordinary_payload]));
    let owner_upper = machine.alloc_neg(Neg::Var(owner));
    let origin = crate::constraints::OriginId::unknown_internal();

    machine.weighted_subtype(
        weighted,
        ConstraintWeights::empty().with_left(SubtractId(7)),
        owner_upper,
        origin,
    );
    machine.subtype(ordinary, owner_upper, origin);

    let raw = compact_type_var(&machine, owner);
    let scheme = compact_type_var_for_scheme(&mut machine, owner);
    assert_eq!(
        scheme, raw,
        "a no-claim owner preserves compact nodes, weights, and ordering exactly"
    );
}

mod case_01;
mod case_02;

use case_02::{compact_path_is, compact_row_contains_path, compact_type_contains_var, role_arg};
