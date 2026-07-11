use std::collections::{HashMap, HashSet};

use poly::roles::{RoleConstraint, RoleConstraintArg, RoleImplCandidate};
use poly::types::{
    Neg, NegId, Neu, NeuId, Pos, PosId, RolePredicateArg, Scheme, StackWeight, SubtractId,
    Subtractability, TypeArena, TypeVar,
};

/// One unit-owned boundary variable and its frozen interval.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BoundaryBound {
    pub var: TypeVar,
    pub lower: PosId,
    pub upper: NegId,
}

/// The explicit `B` namespace supplied to closure validation and alpha views.
#[derive(Debug, Clone, Copy)]
pub struct BoundaryInterface<'a> {
    pub binders: &'a [TypeVar],
    pub bounds: &'a [BoundaryBound],
}

impl BoundaryInterface<'static> {
    pub const EMPTY: Self = Self {
        binders: &[],
        bounds: &[],
    };
}

/// Structured reasons why a finalized interface is not closed under its binders.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InterfaceViolation {
    UnboundSchemeVariable { var: TypeVar },
    UnboundCandidateVariable { var: TypeVar },
    BoundaryDependsOnLocalBinder { boundary: TypeVar, local: TypeVar },
    MissingBoundaryBound { var: TypeVar },
    ConflictingBoundaryBound { var: TypeVar },
    UnboundSubtractId { id: SubtractId },
}

/// Read-only `Q/R/B` inventory for one scheme.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SchemeClosureInventory {
    pub quantified: Vec<TypeVar>,
    pub recursive: Vec<TypeVar>,
    pub boundary: Vec<TypeVar>,
    pub unbound: Vec<TypeVar>,
    pub stack_binders: Vec<SubtractId>,
    pub unbound_subtracts: Vec<SubtractId>,
}

/// Read-only head/`B` inventory for one role candidate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CandidateClosureInventory {
    pub head_binders: Vec<TypeVar>,
    pub boundary: Vec<TypeVar>,
    pub unbound: Vec<TypeVar>,
    pub subtracts: Vec<SubtractId>,
}

/// Traverse a scheme closure without changing the source arena or solver state.
pub fn scan_scheme_closure(
    arena: &TypeArena,
    scheme: &Scheme,
    boundary: BoundaryInterface<'_>,
) -> Result<SchemeClosureInventory, Vec<InterfaceViolation>> {
    let quantified = scheme.quantifiers.iter().copied().collect::<HashSet<_>>();
    let recursive = scheme
        .recursive_bounds
        .iter()
        .map(|bound| bound.var)
        .collect::<HashSet<_>>();
    let boundary_binders = boundary.binders.iter().copied().collect::<HashSet<_>>();
    let local = quantified
        .union(&recursive)
        .copied()
        .collect::<HashSet<_>>();

    let mut scan = ClosureScan::new(arena);
    scan.pos(scheme.predicate);
    for predicate in &scheme.role_predicates {
        scan.scheme_role_predicate(predicate);
    }
    for bound in &scheme.recursive_bounds {
        scan.vars.insert(bound.var);
        scan.neu(bound.bounds);
    }

    let mut unbound = scan
        .vars
        .difference(&local)
        .copied()
        .filter(|var| !boundary_binders.contains(var))
        .collect::<Vec<_>>();
    sort_type_vars(&mut unbound);

    let stack_binders = scheme
        .stack_quantifiers
        .iter()
        .copied()
        .collect::<HashSet<_>>();
    let mut unbound_subtracts = scan
        .subtracts
        .difference(&stack_binders)
        .copied()
        .collect::<Vec<_>>();
    sort_subtract_ids(&mut unbound_subtracts);

    let mut violations = unbound
        .iter()
        .copied()
        .map(|var| InterfaceViolation::UnboundSchemeVariable { var })
        .collect::<Vec<_>>();
    violations.extend(
        unbound_subtracts
            .iter()
            .copied()
            .map(|id| InterfaceViolation::UnboundSubtractId { id }),
    );
    violations.extend(local.intersection(&boundary_binders).copied().map(|var| {
        InterfaceViolation::BoundaryDependsOnLocalBinder {
            boundary: var,
            local: var,
        }
    }));
    violations.extend(validate_boundary_interface(arena, boundary, &local));
    sort_violations(&mut violations);

    let mut quantified_out = quantified.into_iter().collect::<Vec<_>>();
    let mut recursive_out = recursive.into_iter().collect::<Vec<_>>();
    let mut boundary_out = scan
        .vars
        .intersection(&boundary_binders)
        .copied()
        .collect::<Vec<_>>();
    let mut stack_binders_out = stack_binders.into_iter().collect::<Vec<_>>();
    sort_type_vars(&mut quantified_out);
    sort_type_vars(&mut recursive_out);
    sort_type_vars(&mut boundary_out);
    sort_subtract_ids(&mut stack_binders_out);

    if violations.is_empty() {
        Ok(SchemeClosureInventory {
            quantified: quantified_out,
            recursive: recursive_out,
            boundary: boundary_out,
            unbound,
            stack_binders: stack_binders_out,
            unbound_subtracts,
        })
    } else {
        Err(violations)
    }
}

/// Traverse a candidate head and prerequisites without role resolution.
pub fn scan_candidate_closure(
    arena: &TypeArena,
    candidate: &RoleImplCandidate,
    boundary: BoundaryInterface<'_>,
) -> Result<CandidateClosureInventory, Vec<InterfaceViolation>> {
    let boundary_binders = boundary.binders.iter().copied().collect::<HashSet<_>>();
    let mut head = ClosureScan::new(arena);
    head.role_constraint(&candidate.as_constraint());
    let head_binders = head
        .vars
        .difference(&boundary_binders)
        .copied()
        .collect::<HashSet<_>>();

    let mut all = ClosureScan::new(arena);
    all.role_constraint(&candidate.as_constraint());
    for prerequisite in &candidate.prerequisites {
        all.role_constraint(prerequisite);
    }
    let closed = head_binders
        .union(&boundary_binders)
        .copied()
        .collect::<HashSet<_>>();
    let mut unbound = all.vars.difference(&closed).copied().collect::<Vec<_>>();
    sort_type_vars(&mut unbound);

    let mut violations = unbound
        .iter()
        .copied()
        .map(|var| InterfaceViolation::UnboundCandidateVariable { var })
        .collect::<Vec<_>>();
    violations.extend(
        all.subtracts
            .iter()
            .copied()
            .map(|id| InterfaceViolation::UnboundSubtractId { id }),
    );
    violations.extend(validate_boundary_interface(arena, boundary, &head_binders));
    sort_violations(&mut violations);

    let mut head_out = head_binders.into_iter().collect::<Vec<_>>();
    let mut boundary_out = all
        .vars
        .intersection(&boundary_binders)
        .copied()
        .collect::<Vec<_>>();
    let mut subtracts = all.subtracts.into_iter().collect::<Vec<_>>();
    sort_type_vars(&mut head_out);
    sort_type_vars(&mut boundary_out);
    sort_subtract_ids(&mut subtracts);

    if violations.is_empty() {
        Ok(CandidateClosureInventory {
            head_binders: head_out,
            boundary: boundary_out,
            unbound,
            subtracts,
        })
    } else {
        Err(violations)
    }
}

fn validate_boundary_interface(
    arena: &TypeArena,
    boundary: BoundaryInterface<'_>,
    local_binders: &HashSet<TypeVar>,
) -> Vec<InterfaceViolation> {
    let boundary_binders = boundary.binders.iter().copied().collect::<HashSet<_>>();
    let mut bound_counts = HashMap::<TypeVar, usize>::new();
    for bound in boundary.bounds {
        *bound_counts.entry(bound.var).or_default() += 1;
    }

    let mut violations = Vec::new();
    for var in &boundary_binders {
        match bound_counts.get(var).copied().unwrap_or_default() {
            0 => violations.push(InterfaceViolation::MissingBoundaryBound { var: *var }),
            1 => {}
            _ => violations.push(InterfaceViolation::ConflictingBoundaryBound { var: *var }),
        }
    }

    for bound in boundary.bounds {
        let mut scan = ClosureScan::new(arena);
        scan.pos(bound.lower);
        scan.neg(bound.upper);
        for var in scan.vars {
            if local_binders.contains(&var) {
                violations.push(InterfaceViolation::BoundaryDependsOnLocalBinder {
                    boundary: bound.var,
                    local: var,
                });
            } else if !boundary_binders.contains(&var) {
                violations.push(InterfaceViolation::MissingBoundaryBound { var });
            }
        }
    }
    violations
}

pub(crate) struct ClosureScan<'a> {
    arena: &'a TypeArena,
    pub(crate) vars: HashSet<TypeVar>,
    pub(crate) subtracts: HashSet<SubtractId>,
    pos_seen: HashSet<PosId>,
    neg_seen: HashSet<NegId>,
    neu_seen: HashSet<NeuId>,
}

impl<'a> ClosureScan<'a> {
    pub(crate) fn new(arena: &'a TypeArena) -> Self {
        Self {
            arena,
            vars: HashSet::new(),
            subtracts: HashSet::new(),
            pos_seen: HashSet::new(),
            neg_seen: HashSet::new(),
            neu_seen: HashSet::new(),
        }
    }

    pub(crate) fn scheme_role_predicate(&mut self, predicate: &poly::types::RolePredicate) {
        for input in &predicate.inputs {
            match input {
                RolePredicateArg::Covariant(id) => self.pos(*id),
                RolePredicateArg::Contravariant(id) => self.neg(*id),
                RolePredicateArg::Invariant(id) => self.neu(*id),
            }
        }
        for associated in &predicate.associated {
            self.neu(associated.value);
        }
    }

    fn role_constraint(&mut self, constraint: &RoleConstraint) {
        for input in &constraint.inputs {
            self.role_constraint_arg(*input);
        }
        for associated in &constraint.associated {
            self.role_constraint_arg(associated.value);
        }
    }

    fn role_constraint_arg(&mut self, arg: RoleConstraintArg) {
        self.pos(arg.lower);
        self.neg(arg.upper);
    }

    pub(crate) fn pos(&mut self, id: PosId) {
        if !self.pos_seen.insert(id) {
            return;
        }
        match self.arena.pos(id) {
            Pos::Bot => {}
            Pos::Var(var) => {
                self.vars.insert(*var);
            }
            Pos::Con(_, args) => self.neu_slice(args),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.neg(*arg);
                self.neg(*arg_eff);
                self.pos(*ret_eff);
                self.pos(*ret);
            }
            Pos::Record(fields) => {
                for field in fields {
                    self.pos(field.value);
                }
            }
            Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { tail, fields } => {
                for field in fields {
                    self.pos(field.value);
                }
                self.pos(*tail);
            }
            Pos::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    for payload in payloads {
                        self.pos(*payload);
                    }
                }
            }
            Pos::Tuple(items) | Pos::Row(items) => {
                for item in items {
                    self.pos(*item);
                }
            }
            Pos::Stack { inner, weight } => {
                self.pos(*inner);
                self.weight(weight);
            }
            Pos::NonSubtract(inner, weight) => {
                self.pos(*inner);
                self.weight(weight);
            }
            Pos::Union(left, right) => {
                self.pos(*left);
                self.pos(*right);
            }
        }
    }

    pub(crate) fn neg(&mut self, id: NegId) {
        if !self.neg_seen.insert(id) {
            return;
        }
        match self.arena.neg(id) {
            Neg::Top | Neg::Bot => {}
            Neg::Var(var) => {
                self.vars.insert(*var);
            }
            Neg::Con(_, args) => self.neu_slice(args),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.pos(*arg);
                self.pos(*arg_eff);
                self.neg(*ret_eff);
                self.neg(*ret);
            }
            Neg::Record(fields) => {
                for field in fields {
                    self.neg(field.value);
                }
            }
            Neg::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    for payload in payloads {
                        self.neg(*payload);
                    }
                }
            }
            Neg::Tuple(items) => {
                for item in items {
                    self.neg(*item);
                }
            }
            Neg::Row(items, tail) => {
                for item in items {
                    self.neg(*item);
                }
                self.neg(*tail);
            }
            Neg::Stack { inner, weight } => {
                self.neg(*inner);
                self.weight(weight);
            }
            Neg::Intersection(left, right) => {
                self.neg(*left);
                self.neg(*right);
            }
        }
    }

    pub(crate) fn neu(&mut self, id: NeuId) {
        if !self.neu_seen.insert(id) {
            return;
        }
        match self.arena.neu(id) {
            Neu::Bounds(lower, upper) => {
                self.pos(*lower);
                self.neg(*upper);
            }
            Neu::Con(_, args) => self.neu_slice(args),
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.neu(*arg);
                self.neu(*arg_eff);
                self.neu(*ret_eff);
                self.neu(*ret);
            }
            Neu::Record(fields) => {
                for field in fields {
                    self.neu(field.value);
                }
            }
            Neu::PolyVariant(variants) => {
                for (_, payloads) in variants {
                    for payload in payloads {
                        self.neu(*payload);
                    }
                }
            }
            Neu::Tuple(items) => self.neu_slice(items),
        }
    }

    fn neu_slice(&mut self, ids: &[NeuId]) {
        for id in ids {
            self.neu(*id);
        }
    }

    fn weight(&mut self, weight: &StackWeight) {
        self.subtractability(weight.filter_set());
        for entry in weight.entries() {
            self.subtracts.insert(entry.id);
            for item in entry.floor.iter().chain(&entry.stack) {
                self.subtractability(item);
            }
        }
    }

    fn subtractability(&mut self, item: &Subtractability) {
        match item {
            Subtractability::Empty | Subtractability::All => {}
            Subtractability::AllExcept(_, args) | Subtractability::Set(_, args) => {
                self.neu_slice(args)
            }
            Subtractability::AllExceptMany(families) | Subtractability::SetMany(families) => {
                for (_, args) in families {
                    self.neu_slice(args);
                }
            }
        }
    }
}

fn sort_type_vars(vars: &mut [TypeVar]) {
    vars.sort_by_key(|var| var.0);
}

fn sort_subtract_ids(ids: &mut [SubtractId]) {
    ids.sort_by_key(|id| id.0);
}

fn sort_violations(violations: &mut [InterfaceViolation]) {
    violations.sort_by_key(|violation| format!("{violation:?}"));
}
