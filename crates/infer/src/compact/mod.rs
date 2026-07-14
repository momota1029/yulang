//! Compact type は、solver の bounds table から `poly::Scheme` を作る前に使う簡約用の
//! 作業表現。
//!
//! `poly::Scheme` の主役は最終的な `PosId` であり、compact 表現は infer 内だけで
//! 極性消去・共起分析・sandwich を走らせるための中間表現として扱う。
//! Concrete shape には subtract weight を持たせず、展開時に変数 occurrence へ押し込む。
//! 通常の contravariant occurrence は空 weight だが、filter guard を持つ negative stack
//! occurrence は、その guard を落とさないため weight 付きのまま保持する。
//! principal 化では finalizer が filter 成分だけを剥がし、実際の pop/floor/push だけを出力へ戻す。

use std::{
    hash::{Hash, Hasher},
    mem,
};

use poly::types::{
    BuiltinType, Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, SchemeRecursiveBound,
    StackWeight, Subtractability, TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::constraints::{ConstraintMachine, ConstraintWeight, ConstraintWeights, VarBounds};
use crate::roles::{RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg};

mod analysis;
mod collect;
#[cfg(test)]
pub(crate) use analysis::collect_interval_dominance_constraints;
#[cfg(test)]
pub(crate) use analysis::simplify_compact_root;
pub(crate) use analysis::{
    IntervalDominanceMetrics, coalesce_floor_interval_equalities,
    coalesce_floor_variable_sandwiches, collect_interval_dominance_constraints_with_metrics,
    compact_root_has_interval_bounds, eliminate_floor_redundant_variables,
    normalize_var_substitutions, simplify_compact_root_with_role_variance_table_and_non_generic,
    simplify_compact_root_with_roles_and_non_generic,
};
#[cfg(test)]
pub(in crate::compact) use collect::CompactCollector;
mod casts;
mod finalize;
mod merge;
mod surface;
#[cfg(test)]
mod tests;
pub(crate) use casts::{
    CompactCastApplication, CompactCastKey, find_next_compact_cast, normalize_compact_casts,
};
#[cfg(test)]
pub(crate) use finalize::finalize_compact_type;
pub(crate) use finalize::{
    finalize_compact_bounds, finalize_compact_bounds_lower, finalize_compact_bounds_to_constraint,
    finalize_compact_bounds_upper, finalize_compact_root, finalize_compact_type_to_neg,
    finalize_compact_type_to_neg_constraint, finalize_compact_type_to_pos_constraint,
};
#[cfg(test)]
pub(crate) use merge::merge_compact_types_recording_merge_constraints;
pub(crate) use merge::{
    compact_con_entries, compact_row_item_entries,
    merge_compact_bounds_recording_merge_constraints, merge_compact_types, merge_cons,
};
pub(crate) use surface::{
    apply_compact_merge_constraints, apply_compact_subtype_constraints,
    compact_negative_type_var_for_scheme, compact_pos_surface,
    compact_reachable_role_constraints_from_seed_vars_recording_merge_constraints,
    compact_role_constraint, compact_role_constraint_recording_merge_constraints, compact_type_var,
    compact_type_var_boundary_bounds_recording_merge_constraints, compact_type_var_for_scheme,
    compact_type_var_recording_merge_constraints,
    compact_type_var_recording_merge_constraints_for_scheme,
};
#[cfg(test)]
pub(crate) use surface::{
    compact_negative_type_var_recording_merge_constraints, compact_reachable_role_constraints,
};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CompactRoot {
    pub(crate) root: CompactType,
    pub(crate) rec_vars: Vec<CompactRecursiveVar>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactMergeConstraint {
    key: CompactMergeConstraintKey,
    lhs: CompactBounds,
    rhs: CompactBounds,
}

impl CompactMergeConstraint {
    fn new(lhs: &CompactBounds, rhs: &CompactBounds) -> Option<Self> {
        let key = merge::compact_merge_constraint_key(lhs, rhs);
        Some(Self {
            key,
            lhs: lhs.clone(),
            rhs: rhs.clone(),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactSubtypeConstraint {
    key: CompactSubtypeConstraintKey,
    lower: CompactType,
    upper: CompactType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactSubtypeConstraintKey {
    lower: CompactType,
    upper: CompactType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(
    dead_code,
    reason = "Stage 2 compact boundary draft is consumed by a later artifact integration slice"
)]
pub(crate) struct CompactBoundaryCapture {
    pub(crate) bounds: CompactBounds,
    pub(crate) recursive: Vec<CompactRecursiveVar>,
}

#[allow(
    dead_code,
    reason = "Stage 2 strict audit is consumed by the pending cache-interface finalizer wiring"
)]
pub(crate) fn unapplied_compact_merge_constraint_count(
    constraints: &[CompactMergeConstraint],
    applied: &FxHashSet<CompactMergeConstraintKey>,
) -> usize {
    constraints
        .iter()
        .filter(|constraint| constraint.lhs != constraint.rhs && !applied.contains(&constraint.key))
        .count()
}

/// Count unapplied candidate constraints, accepting only direct tuple-product implication.
///
/// Invariance of equal-length tuples decomposes position-wise. A tuple wrapper therefore adds no
/// new fact when every direct element merge is already applied. This is deliberately not recursive
/// and does not extend to constructors, functions, records, variants, or associated-type carriers.
pub(crate) fn unapplied_compact_merge_constraint_count_with_tuple_implication(
    constraints: &[CompactMergeConstraint],
    applied: &FxHashSet<CompactMergeConstraintKey>,
) -> usize {
    constraints
        .iter()
        .filter(|constraint| {
            constraint.lhs != constraint.rhs
                && !applied.contains(&constraint.key)
                && !tuple_merge_is_implied_by_applied_elements(constraint, applied)
        })
        .count()
}

fn tuple_merge_is_implied_by_applied_elements(
    constraint: &CompactMergeConstraint,
    applied: &FxHashSet<CompactMergeConstraintKey>,
) -> bool {
    let (CompactBounds::Tuple { items }, CompactBounds::Tuple { items: right_items }) =
        (&constraint.lhs, &constraint.rhs)
    else {
        return false;
    };
    items.len() == right_items.len()
        && items.iter().zip(right_items).all(|(left, right)| {
            left == right || applied.contains(&merge::compact_merge_constraint_key(left, right))
        })
}

#[allow(
    dead_code,
    reason = "Stage 2 strict audit is consumed by the pending cache-interface finalizer wiring"
)]
pub(crate) fn unapplied_compact_subtype_constraint_count(
    constraints: &[CompactSubtypeConstraint],
    applied: &FxHashSet<CompactSubtypeConstraintKey>,
) -> usize {
    constraints
        .iter()
        .filter(|constraint| {
            constraint.lower != constraint.upper && !applied.contains(&constraint.key)
        })
        .count()
}

pub(crate) fn compact_subtype_constraint_keys(
    constraints: &[CompactSubtypeConstraint],
) -> FxHashSet<CompactSubtypeConstraintKey> {
    constraints
        .iter()
        .filter(|constraint| constraint.lower != constraint.upper)
        .map(|constraint| constraint.key.clone())
        .collect()
}

pub(crate) fn unapplied_compact_subtype_constraint_count_with_known(
    constraints: &[CompactSubtypeConstraint],
    applied: &FxHashSet<CompactSubtypeConstraintKey>,
    known: &FxHashSet<CompactSubtypeConstraintKey>,
) -> usize {
    constraints
        .iter()
        .filter(|constraint| {
            constraint.lower != constraint.upper
                && !applied.contains(&constraint.key)
                && !known.contains(&constraint.key)
        })
        .count()
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactMergeConstraintKey {
    lhs: CompactMergeConstraintShape,
    rhs: CompactMergeConstraintShape,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum CompactMergeConstraintShape {
    Interval {
        center: Option<TypeVar>,
    },
    Con {
        path: Vec<String>,
        args: Vec<CompactMergeConstraintShape>,
    },
    Tuple(Vec<CompactMergeConstraintShape>),
    Fun {
        arg: Box<CompactMergeConstraintShape>,
        arg_eff: Box<CompactMergeConstraintShape>,
        ret_eff: Box<CompactMergeConstraintShape>,
        ret: Box<CompactMergeConstraintShape>,
    },
    Record(Vec<CompactMergeConstraintFieldShape>),
    PolyVariant(Vec<(String, Vec<CompactMergeConstraintShape>)>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CompactMergeConstraintFieldShape {
    name: String,
    value: CompactMergeConstraintShape,
    optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompactRecursiveVar {
    pub(crate) var: TypeVar,
    pub(crate) bounds: CompactBounds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct CompactVarSubstitution {
    pub(crate) source: TypeVar,
    pub(crate) target: Option<TypeVar>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CompactSimplification {
    pub(crate) substitutions: Vec<CompactVarSubstitution>,
    pub(crate) sandwiches: Vec<CompactSandwich>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactSandwich {
    pub(crate) var: TypeVar,
    pub(crate) kind: CompactSandwichKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum CompactSandwichKind {
    Con { path: Vec<String>, arity: usize },
    Tuple { arity: usize },
    Fun,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactRoleConstraint {
    pub(crate) role: Vec<String>,
    pub(crate) inputs: Vec<CompactRoleArg>,
    pub(crate) associated: Vec<CompactRoleAssociatedType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactRoleArg {
    pub(crate) polarity: CompactRoleArgPolarity,
    pub(crate) bounds: CompactBounds,
}

impl CompactRoleArg {
    pub(crate) fn invariant(bounds: CompactBounds) -> Self {
        Self {
            polarity: CompactRoleArgPolarity::Invariant,
            bounds,
        }
    }

    pub(crate) fn with_polarity(mut self, polarity: CompactRoleArgPolarity) -> Self {
        self.polarity = polarity;
        self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum CompactRoleArgPolarity {
    Covariant,
    Contravariant,
    Invariant,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactRoleAssociatedType {
    pub(crate) name: String,
    pub(crate) value: CompactRoleArg,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FinalizedCompactRoot {
    pub(crate) root: PosId,
    pub(crate) rec_vars: Vec<SchemeRecursiveBound>,
}

pub(crate) type CompactConMap = FxHashMap<Vec<String>, Vec<CompactBounds>>;
pub(crate) type CompactRowItemMap = FxHashMap<Vec<String>, Vec<CompactBounds>>;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CompactType {
    pub(crate) vars: Vec<CompactVar>,
    pub(crate) never: bool,
    pub(crate) builtins: Vec<BuiltinType>,
    pub(crate) cons: CompactConMap,
    pub(crate) funs: Vec<CompactFun>,
    pub(crate) records: Vec<CompactRecord>,
    pub(crate) record_spreads: Vec<CompactRecordSpread>,
    pub(crate) poly_variants: Vec<CompactPolyVariant>,
    pub(crate) tuples: Vec<CompactTuple>,
    pub(crate) rows: Vec<CompactRow>,
}

impl Hash for CompactType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.vars.hash(state);
        self.never.hash(state);
        self.builtins.hash(state);
        compact_con_entries(&self.cons).hash(state);
        self.funs.hash(state);
        self.records.hash(state);
        self.record_spreads.hash(state);
        self.poly_variants.hash(state);
        self.tuples.hash(state);
        self.rows.hash(state);
    }
}

impl CompactType {
    pub(crate) fn from_var(var: CompactVar) -> Self {
        Self {
            vars: vec![var],
            ..Self::default()
        }
    }

    pub(crate) fn never() -> Self {
        Self {
            never: true,
            ..Self::default()
        }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.vars.is_empty()
            && !self.never
            && self.builtins.is_empty()
            && self.cons.is_empty()
            && self.funs.is_empty()
            && self.records.is_empty()
            && self.record_spreads.is_empty()
            && self.poly_variants.is_empty()
            && self.tuples.is_empty()
            && self.rows.is_empty()
    }

    pub(crate) fn from_builtin(builtin: BuiltinType) -> Self {
        Self {
            builtins: vec![builtin],
            ..Self::default()
        }
    }

    pub(crate) fn from_con(con: CompactCon) -> Self {
        let mut cons = CompactConMap::default();
        cons.insert(con.path, con.args);
        Self {
            cons,
            ..Self::default()
        }
    }

    pub(crate) fn from_fun(fun: CompactFun) -> Self {
        Self {
            funs: vec![fun],
            ..Self::default()
        }
    }

    pub(crate) fn from_record(record: CompactRecord) -> Self {
        Self {
            records: vec![record],
            ..Self::default()
        }
    }

    pub(crate) fn from_record_spread(spread: CompactRecordSpread) -> Self {
        Self {
            record_spreads: vec![spread],
            ..Self::default()
        }
    }

    pub(crate) fn from_poly_variant(variant: CompactPolyVariant) -> Self {
        Self {
            poly_variants: vec![variant],
            ..Self::default()
        }
    }

    pub(crate) fn from_tuple(tuple: CompactTuple) -> Self {
        Self {
            tuples: vec![tuple],
            ..Self::default()
        }
    }

    pub(crate) fn from_row(row: CompactRow) -> Self {
        Self {
            rows: vec![row],
            ..Self::default()
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactVar {
    pub(crate) var: TypeVar,
    pub(crate) weight: ConstraintWeight,
    pub(crate) origin: CompactVarOrigin,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum CompactVarOrigin {
    Primary,
    Secondary,
}

impl CompactVarOrigin {
    pub(crate) fn merged(self, other: Self) -> Self {
        match (self, other) {
            (Self::Secondary, _) | (_, Self::Secondary) => Self::Secondary,
            (Self::Primary, Self::Primary) => Self::Primary,
        }
    }
}

impl CompactVar {
    pub(crate) fn covariant(var: TypeVar, weight: ConstraintWeight) -> Self {
        Self {
            var,
            weight,
            origin: CompactVarOrigin::Primary,
        }
    }

    pub(crate) fn contravariant(var: TypeVar) -> Self {
        Self {
            var,
            weight: ConstraintWeight::empty(),
            origin: CompactVarOrigin::Primary,
        }
    }

    pub(crate) fn contravariant_with_weight(var: TypeVar, weight: ConstraintWeight) -> Self {
        Self {
            var,
            weight,
            origin: CompactVarOrigin::Primary,
        }
    }

    pub(crate) fn plain(var: TypeVar) -> Self {
        Self::contravariant(var)
    }

    pub(crate) fn with_origin(mut self, origin: CompactVarOrigin) -> Self {
        self.origin = origin;
        self
    }

    #[cfg(test)]
    pub(crate) fn secondary(mut self) -> Self {
        self.origin = CompactVarOrigin::Secondary;
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum CompactBounds {
    Interval {
        lower: CompactType,
        upper: CompactType,
    },
    Con {
        path: Vec<String>,
        args: Vec<CompactBounds>,
    },
    Fun {
        arg: Box<CompactBounds>,
        arg_eff: Box<CompactBounds>,
        ret_eff: Box<CompactBounds>,
        ret: Box<CompactBounds>,
    },
    Record {
        fields: Vec<RecordField<CompactBounds>>,
    },
    PolyVariant {
        items: Vec<(String, Vec<CompactBounds>)>,
    },
    Tuple {
        items: Vec<CompactBounds>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactCon {
    pub(crate) path: Vec<String>,
    pub(crate) args: Vec<CompactBounds>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactFun {
    pub(crate) arg: CompactType,
    pub(crate) arg_eff: CompactType,
    pub(crate) ret_eff: CompactType,
    pub(crate) ret: CompactType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactRecord {
    pub(crate) fields: Vec<RecordField<CompactType>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactRecordSpread {
    pub(crate) fields: Vec<RecordField<CompactType>>,
    pub(crate) tail: Box<CompactType>,
    pub(crate) tail_wins: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactPolyVariant {
    pub(crate) items: Vec<(String, Vec<CompactType>)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactTuple {
    pub(crate) items: Vec<CompactType>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompactRow {
    pub(crate) items: CompactRowItemMap,
    pub(crate) tail: Box<CompactType>,
}

impl Hash for CompactRow {
    fn hash<H: Hasher>(&self, state: &mut H) {
        compact_row_item_entries(&self.items).hash(state);
        self.tail.hash(state);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Polarity {
    Positive,
    Negative,
}

impl Polarity {
    fn flipped(self) -> Self {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }

    fn is_positive(self) -> bool {
        matches!(self, Self::Positive)
    }
}
