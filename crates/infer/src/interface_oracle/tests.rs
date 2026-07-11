use poly::roles::{RoleConstraint, RoleConstraintArg, RoleImplCandidate};
use poly::types::{
    Neg, Neu, Pos, RolePredicate, RolePredicateArg, Scheme, SchemeRecursiveBound, StackWeight,
    SubtractId, Subtractability, TypeArena, TypeVar,
};

use super::*;

#[test]
fn scheme_scanner_rejects_unbound_type_and_stack_binders() {
    let mut arena = TypeArena::new();
    let var = TypeVar(17);
    let inner = arena.alloc_pos(Pos::Var(var));
    let predicate = arena.alloc_pos(Pos::Stack {
        inner,
        weight: StackWeight::pop(SubtractId(4)),
    });
    let scheme = scheme(predicate, Vec::new());

    let violations = scan_scheme_closure(&arena, &scheme, BoundaryInterface::EMPTY).unwrap_err();

    assert!(violations.contains(&InterfaceViolation::UnboundSchemeVariable { var }));
    assert!(violations.contains(&InterfaceViolation::UnboundSubtractId { id: SubtractId(4) }));
}

#[test]
fn scheme_scanner_reaches_stack_family_type_arguments() {
    let mut arena = TypeArena::new();
    let var = TypeVar(23);
    let lower = arena.alloc_pos(Pos::Var(var));
    let upper = arena.alloc_neg(Neg::Var(var));
    let argument = arena.alloc_neu(Neu::Bounds(lower, upper));
    let inner = arena.alloc_pos(Pos::Bot);
    let predicate = arena.alloc_pos(Pos::Stack {
        inner,
        weight: StackWeight::filter(Subtractability::Set(vec!["effect".into()], vec![argument])),
    });
    let scheme = scheme(predicate, Vec::new());

    let violations = scan_scheme_closure(&arena, &scheme, BoundaryInterface::EMPTY).unwrap_err();

    assert_eq!(
        violations,
        vec![InterfaceViolation::UnboundSchemeVariable { var }]
    );
}

#[test]
fn candidate_scanner_rejects_prerequisite_only_variable() {
    let mut arena = TypeArena::new();
    let head = constraint_arg(&mut arena, TypeVar(1));
    let prerequisite_only = constraint_arg(&mut arena, TypeVar(2));
    let candidate = RoleImplCandidate {
        impl_def: None,
        role: vec!["Candidate".into()],
        inputs: vec![head],
        associated: Vec::new(),
        prerequisites: vec![RoleConstraint {
            role: vec!["Required".into()],
            inputs: vec![prerequisite_only],
            associated: Vec::new(),
        }],
        methods: Vec::new(),
    };

    let violations =
        scan_candidate_closure(&arena, &candidate, BoundaryInterface::EMPTY).unwrap_err();

    assert_eq!(
        violations,
        vec![InterfaceViolation::UnboundCandidateVariable { var: TypeVar(2) }]
    );
}

#[test]
fn boundary_bound_rejects_scheme_local_dependency() {
    let mut arena = TypeArena::new();
    let local = TypeVar(3);
    let boundary_var = TypeVar(4);
    let predicate = arena.alloc_pos(Pos::Var(local));
    let boundary_lower = arena.alloc_pos(Pos::Var(local));
    let boundary_upper = arena.alloc_neg(Neg::Top);
    let scheme = scheme(predicate, vec![local]);
    let boundary_bound = BoundaryBound {
        var: boundary_var,
        lower: boundary_lower,
        upper: boundary_upper,
    };
    let boundary = BoundaryInterface {
        binders: &[boundary_var],
        bounds: &[boundary_bound],
    };

    let violations = scan_scheme_closure(&arena, &scheme, boundary).unwrap_err();

    assert_eq!(
        violations,
        vec![InterfaceViolation::BoundaryDependsOnLocalBinder {
            boundary: boundary_var,
            local,
        }]
    );
}

#[test]
fn scanner_inventories_recursive_binder_outside_quantifiers() {
    let mut arena = TypeArena::new();
    let recursive = TypeVar(31);
    let lower = arena.alloc_pos(Pos::Var(recursive));
    let upper = arena.alloc_neg(Neg::Var(recursive));
    let bounds = arena.alloc_neu(Neu::Bounds(lower, upper));
    let scheme = Scheme {
        quantifiers: Vec::new(),
        role_predicates: Vec::new(),
        recursive_bounds: vec![SchemeRecursiveBound {
            var: recursive,
            bounds,
        }],
        stack_quantifiers: Vec::new(),
        predicate: lower,
    };

    let inventory = scan_scheme_closure(&arena, &scheme, BoundaryInterface::EMPTY).unwrap();

    assert!(inventory.quantified.is_empty());
    assert_eq!(inventory.recursive, vec![recursive]);
}

#[test]
fn alpha_view_accepts_renaming_but_preserves_variable_sharing() {
    let (left_arena, left) = tuple_scheme(&[TypeVar(7), TypeVar(7)]);
    let (renamed_arena, renamed) = tuple_scheme(&[TypeVar(80), TypeVar(80)]);
    let (split_arena, split) = tuple_scheme(&[TypeVar(90), TypeVar(91)]);

    let left = SchemeAlphaView::from_scheme(&left_arena, &left, BoundaryInterface::EMPTY).unwrap();
    let renamed =
        SchemeAlphaView::from_scheme(&renamed_arena, &renamed, BoundaryInterface::EMPTY).unwrap();
    let split =
        SchemeAlphaView::from_scheme(&split_arena, &split, BoundaryInterface::EMPTY).unwrap();

    assert_eq!(left, renamed);
    assert_ne!(left, split);
}

#[test]
fn alpha_view_keeps_per_use_and_boundary_namespaces_distinct() {
    let mut per_use_arena = TypeArena::new();
    let per_use_var = TypeVar(5);
    let per_use_predicate = per_use_arena.alloc_pos(Pos::Var(per_use_var));
    let per_use_scheme = scheme(per_use_predicate, vec![per_use_var]);
    let per_use =
        SchemeAlphaView::from_scheme(&per_use_arena, &per_use_scheme, BoundaryInterface::EMPTY)
            .unwrap();

    let mut boundary_arena = TypeArena::new();
    let boundary_var = TypeVar(42);
    let boundary_predicate = boundary_arena.alloc_pos(Pos::Var(boundary_var));
    let lower = boundary_arena.alloc_pos(Pos::Bot);
    let upper = boundary_arena.alloc_neg(Neg::Top);
    let boundary_scheme = scheme(boundary_predicate, Vec::new());
    let bound = BoundaryBound {
        var: boundary_var,
        lower,
        upper,
    };
    let boundary = SchemeAlphaView::from_scheme(
        &boundary_arena,
        &boundary_scheme,
        BoundaryInterface {
            binders: &[boundary_var],
            bounds: &[bound],
        },
    )
    .unwrap();

    assert_ne!(per_use, boundary);
    assert_eq!(per_use.predicate, AlphaPos::Var(AlphaTypeBinder::PerUse(0)));
    assert_eq!(
        boundary.predicate,
        AlphaPos::Var(AlphaTypeBinder::Boundary(0))
    );
}

#[test]
fn strict_alpha_view_rejects_overlapping_per_use_and_boundary_binders() {
    let mut arena = TypeArena::new();
    let var = TypeVar(9);
    let predicate = arena.alloc_pos(Pos::Var(var));
    let lower = arena.alloc_pos(Pos::Bot);
    let upper = arena.alloc_neg(Neg::Top);
    let scheme = scheme(predicate, vec![var]);
    let bound = BoundaryBound { var, lower, upper };

    let violations = SchemeAlphaView::from_scheme(
        &arena,
        &scheme,
        BoundaryInterface {
            binders: &[var],
            bounds: &[bound],
        },
    )
    .unwrap_err();

    assert!(
        violations.contains(&InterfaceViolation::BoundaryDependsOnLocalBinder {
            boundary: var,
            local: var,
        })
    );
}

#[test]
fn alpha_view_canonicalizes_residual_role_predicate_order() {
    let (left_arena, left) = role_order_scheme(false);
    let (right_arena, right) = role_order_scheme(true);

    let left = SchemeAlphaView::from_scheme(&left_arena, &left, BoundaryInterface::EMPTY).unwrap();
    let right =
        SchemeAlphaView::from_scheme(&right_arena, &right, BoundaryInterface::EMPTY).unwrap();

    assert_eq!(left, right);
}

fn scheme(predicate: poly::types::PosId, quantifiers: Vec<TypeVar>) -> Scheme {
    Scheme {
        quantifiers,
        role_predicates: Vec::new(),
        recursive_bounds: Vec::new(),
        stack_quantifiers: Vec::new(),
        predicate,
    }
}

fn constraint_arg(arena: &mut TypeArena, var: TypeVar) -> RoleConstraintArg {
    RoleConstraintArg {
        lower: arena.alloc_pos(Pos::Var(var)),
        upper: arena.alloc_neg(Neg::Var(var)),
    }
}

fn tuple_scheme(vars: &[TypeVar]) -> (TypeArena, Scheme) {
    let mut arena = TypeArena::new();
    let items = vars
        .iter()
        .map(|var| arena.alloc_pos(Pos::Var(*var)))
        .collect();
    let predicate = arena.alloc_pos(Pos::Tuple(items));
    let mut quantifiers = vars.to_vec();
    quantifiers.sort_by_key(|var| var.0);
    quantifiers.dedup();
    let scheme = scheme(predicate, quantifiers);
    (arena, scheme)
}

fn role_order_scheme(reverse: bool) -> (TypeArena, Scheme) {
    let mut arena = TypeArena::new();
    let first = TypeVar(100);
    let second = TypeVar(200);
    let first_id = arena.alloc_pos(Pos::Var(first));
    let second_id = arena.alloc_pos(Pos::Var(second));
    let predicate = arena.alloc_pos(Pos::Tuple(vec![first_id, second_id]));
    let mut role_predicates = vec![
        RolePredicate {
            role: vec!["Alpha".into()],
            inputs: vec![RolePredicateArg::Covariant(first_id)],
            associated: Vec::new(),
        },
        RolePredicate {
            role: vec!["Beta".into()],
            inputs: vec![RolePredicateArg::Covariant(second_id)],
            associated: Vec::new(),
        },
    ];
    if reverse {
        role_predicates.reverse();
    }
    (
        arena,
        Scheme {
            quantifiers: vec![first, second],
            role_predicates,
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        },
    )
}
