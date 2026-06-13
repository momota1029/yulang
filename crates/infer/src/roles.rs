//! Role constraints の raw table。
//!
//! lowering / annotation から来た role predicate は、まず solver arena 上の `PosId` / `NegId`
//! の不変引数として保持する。compact / role 解決は、この raw constraint を毎回現状の bounds から
//! collect し直して進める。

use poly::expr::DefId;
use poly::types::{Neg, NegId, Neu, NeuId, Pos, PosId, TypeArena, TypeVar};
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoleInputVariance {
    Unused,
    Covariant,
    Contravariant,
    Invariant,
}

impl RoleInputVariance {
    pub fn record(self, occurrence: RoleInputOccurrence) -> Self {
        match (self, occurrence) {
            (Self::Invariant, _) | (_, RoleInputOccurrence::Invariant) => Self::Invariant,
            (Self::Unused, RoleInputOccurrence::Covariant) => Self::Covariant,
            (Self::Unused, RoleInputOccurrence::Contravariant) => Self::Contravariant,
            (Self::Covariant, RoleInputOccurrence::Covariant) => Self::Covariant,
            (Self::Contravariant, RoleInputOccurrence::Contravariant) => Self::Contravariant,
            (Self::Covariant, RoleInputOccurrence::Contravariant)
            | (Self::Contravariant, RoleInputOccurrence::Covariant) => Self::Invariant,
        }
    }

    pub fn flipped_for_where(self) -> Self {
        match self {
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
            Self::Unused | Self::Invariant => self,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RoleInputOccurrence {
    Covariant,
    Contravariant,
    Invariant,
}

impl RoleInputOccurrence {
    pub fn flipped(self) -> Self {
        match self {
            Self::Covariant => Self::Contravariant,
            Self::Contravariant => Self::Covariant,
            Self::Invariant => Self::Invariant,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct RoleInputVarianceTable {
    variances: FxHashMap<Vec<String>, Vec<RoleInputVariance>>,
}

impl RoleInputVarianceTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, role: impl Into<Vec<String>>, variances: Vec<RoleInputVariance>) {
        self.variances.insert(role.into(), variances);
    }

    pub fn for_role(&self, role: &[String]) -> Option<&[RoleInputVariance]> {
        self.variances.get(role).map(Vec::as_slice)
    }

    pub fn input_or_invariant(&self, role: &[String], index: usize) -> RoleInputVariance {
        self.for_role(role)
            .and_then(|variances| variances.get(index).copied())
            .unwrap_or(RoleInputVariance::Invariant)
    }
}

#[derive(Debug, Clone, Default)]
pub struct RoleConstraintTable {
    constraints: FxHashMap<DefId, Vec<RoleConstraint>>,
}

impl RoleConstraintTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, owner: DefId, constraint: RoleConstraint) {
        self.constraints.entry(owner).or_default().push(constraint);
    }

    pub fn for_owner(&self, owner: DefId) -> &[RoleConstraint] {
        self.constraints
            .get(&owner)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
}

#[derive(Debug, Clone, Default)]
pub struct RoleImplTable {
    candidates: FxHashMap<Vec<String>, Vec<RoleImplCandidate>>,
}

impl RoleImplTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, candidate: RoleImplCandidate) {
        self.candidates
            .entry(candidate.role.clone())
            .or_default()
            .push(candidate);
    }

    pub fn candidates(&self, role: &[String]) -> &[RoleImplCandidate] {
        self.candidates.get(role).map(Vec::as_slice).unwrap_or(&[])
    }

    pub fn extend_prerequisites_for_impl(
        &mut self,
        impl_def: DefId,
        prerequisites: impl IntoIterator<Item = RoleConstraint>,
    ) {
        let prerequisites = prerequisites.into_iter().collect::<Vec<_>>();
        if prerequisites.is_empty() {
            return;
        }
        for candidates in self.candidates.values_mut() {
            for candidate in candidates {
                if candidate.impl_def != Some(impl_def) {
                    continue;
                }
                for prerequisite in &prerequisites {
                    if !candidate.prerequisites.contains(prerequisite) {
                        candidate.prerequisites.push(prerequisite.clone());
                    }
                }
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleImplCandidate {
    pub impl_def: Option<DefId>,
    pub role: Vec<String>,
    pub inputs: Vec<RoleConstraintArg>,
    pub associated: Vec<RoleAssociatedConstraint>,
    pub prerequisites: Vec<RoleConstraint>,
}

impl RoleImplCandidate {
    pub(crate) fn as_constraint(&self) -> RoleConstraint {
        RoleConstraint {
            role: self.role.clone(),
            inputs: self.inputs.clone(),
            associated: self.associated.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleConstraint {
    pub role: Vec<String>,
    pub inputs: Vec<RoleConstraintArg>,
    pub associated: Vec<RoleAssociatedConstraint>,
}

impl RoleConstraint {
    pub(crate) fn raw_vars(&self, types: &TypeArena) -> FxHashSet<TypeVar> {
        let mut vars = FxHashSet::default();
        for input in &self.inputs {
            input.collect_raw_vars(types, &mut vars);
        }
        for associated in &self.associated {
            associated.value.collect_raw_vars(types, &mut vars);
        }
        vars
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RoleConstraintArg {
    pub lower: PosId,
    pub upper: NegId,
}

impl RoleConstraintArg {
    fn collect_raw_vars(&self, types: &TypeArena, vars: &mut FxHashSet<TypeVar>) {
        collect_pos_vars(types, self.lower, vars);
        collect_neg_vars(types, self.upper, vars);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleAssociatedConstraint {
    pub name: String,
    pub value: RoleConstraintArg,
}

fn collect_pos_vars(types: &TypeArena, id: PosId, vars: &mut FxHashSet<TypeVar>) {
    match types.pos(id) {
        Pos::Bot => {}
        Pos::Var(var) => {
            vars.insert(*var);
        }
        Pos::Con(_, args) => collect_neu_vars_in_slice(types, args, vars),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neg_vars(types, *arg, vars);
            collect_neg_vars(types, *arg_eff, vars);
            collect_pos_vars(types, *ret_eff, vars);
            collect_pos_vars(types, *ret, vars);
        }
        Pos::Record(fields) => {
            for field in fields {
                collect_pos_vars(types, field.value, vars);
            }
        }
        Pos::RecordTailSpread { fields, tail } | Pos::RecordHeadSpread { tail, fields } => {
            for field in fields {
                collect_pos_vars(types, field.value, vars);
            }
            collect_pos_vars(types, *tail, vars);
        }
        Pos::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_pos_vars(types, *payload, vars);
                }
            }
        }
        Pos::Tuple(items) | Pos::Row(items) => {
            for item in items {
                collect_pos_vars(types, *item, vars);
            }
        }
        Pos::Stack { inner, .. } => collect_pos_vars(types, *inner, vars),
        Pos::NonSubtract(pos, _) => collect_pos_vars(types, *pos, vars),
        Pos::Union(left, right) => {
            collect_pos_vars(types, *left, vars);
            collect_pos_vars(types, *right, vars);
        }
    }
}

fn collect_neg_vars(types: &TypeArena, id: NegId, vars: &mut FxHashSet<TypeVar>) {
    match types.neg(id) {
        Neg::Top | Neg::Bot => {}
        Neg::Var(var) => {
            vars.insert(*var);
        }
        Neg::Con(_, args) => collect_neu_vars_in_slice(types, args, vars),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_pos_vars(types, *arg, vars);
            collect_pos_vars(types, *arg_eff, vars);
            collect_neg_vars(types, *ret_eff, vars);
            collect_neg_vars(types, *ret, vars);
        }
        Neg::Record(fields) => {
            for field in fields {
                collect_neg_vars(types, field.value, vars);
            }
        }
        Neg::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_neg_vars(types, *payload, vars);
                }
            }
        }
        Neg::Tuple(items) => {
            for item in items {
                collect_neg_vars(types, *item, vars);
            }
        }
        Neg::Row(items, tail) => {
            for item in items {
                collect_neg_vars(types, *item, vars);
            }
            collect_neg_vars(types, *tail, vars);
        }
        Neg::Stack { inner, .. } => collect_neg_vars(types, *inner, vars),
        Neg::Intersection(left, right) => {
            collect_neg_vars(types, *left, vars);
            collect_neg_vars(types, *right, vars);
        }
    }
}

fn collect_neu_vars_in_slice(types: &TypeArena, ids: &[NeuId], vars: &mut FxHashSet<TypeVar>) {
    for id in ids {
        collect_neu_vars(types, *id, vars);
    }
}

fn collect_neu_vars(types: &TypeArena, id: NeuId, vars: &mut FxHashSet<TypeVar>) {
    match types.neu(id) {
        Neu::Bounds(lower, upper) => {
            collect_pos_vars(types, *lower, vars);
            collect_neg_vars(types, *upper, vars);
        }
        Neu::Con(_, args) => collect_neu_vars_in_slice(types, args, vars),
        Neu::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neu_vars(types, *arg, vars);
            collect_neu_vars(types, *arg_eff, vars);
            collect_neu_vars(types, *ret_eff, vars);
            collect_neu_vars(types, *ret, vars);
        }
        Neu::Record(fields) => {
            for field in fields {
                collect_neu_vars(types, field.value, vars);
            }
        }
        Neu::PolyVariant(items) => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_neu_vars(types, *payload, vars);
                }
            }
        }
        Neu::Tuple(items) => {
            for item in items {
                collect_neu_vars(types, *item, vars);
            }
        }
    }
}
