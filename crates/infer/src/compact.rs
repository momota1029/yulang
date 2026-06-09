//! Compact type は、solver の bounds table から `poly::Scheme` を作る前に使う簡約用の
//! 作業表現。
//!
//! `poly::Scheme` の主役は最終的な `PosId` であり、compact 表現は infer 内だけで
//! 極性消去・共起分析・sandwich を走らせるための中間表現として扱う。
//! Concrete shape には subtract weight を持たせず、展開時に covariant な変数 occurrence へ
//! 押し込む。contravariant な変数 occurrence では weight を持たない。

#![allow(dead_code)]

use std::mem;

use poly::types::{
    BuiltinType, Neg, NegId, Neu, NeuId, Pos, PosId, RecordField, TypeArena, TypeVar,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::constraints::{ConstraintMachine, ConstraintWeight, VarBounds};
use crate::roles::{RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg};

mod analysis;
#[cfg(test)]
pub(crate) use analysis::simplify_compact_root;
pub(crate) use analysis::simplify_compact_root_with_roles;
mod casts;
#[cfg(test)]
use analysis::{coalesce_by_co_occurrence, eliminate_polar_variables, sandwich_compact_root};
pub(crate) use casts::{
    CompactCastApplication, CompactCastKey, find_next_compact_cast, normalize_compact_casts,
};

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CompactRoot {
    pub(crate) root: CompactType,
    pub(crate) rec_vars: Vec<CompactRecursiveVar>,
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
    pub(crate) lower: CompactType,
    pub(crate) upper: CompactType,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactRoleAssociatedType {
    pub(crate) name: String,
    pub(crate) value: CompactRoleArg,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FinalizedCompactRoot {
    pub(crate) root: PosId,
    pub(crate) rec_vars: Vec<FinalizedCompactRecursiveVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FinalizedCompactRecursiveVar {
    pub(crate) var: TypeVar,
    pub(crate) bounds: NeuId,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub(crate) struct CompactType {
    pub(crate) vars: Vec<CompactVar>,
    pub(crate) never: bool,
    pub(crate) builtins: Vec<BuiltinType>,
    pub(crate) cons: Vec<CompactCon>,
    pub(crate) funs: Vec<CompactFun>,
    pub(crate) records: Vec<CompactRecord>,
    pub(crate) record_spreads: Vec<CompactRecordSpread>,
    pub(crate) poly_variants: Vec<CompactPolyVariant>,
    pub(crate) tuples: Vec<CompactTuple>,
    pub(crate) rows: Vec<CompactRow>,
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

    pub(crate) fn from_builtin(builtin: BuiltinType) -> Self {
        Self {
            builtins: vec![builtin],
            ..Self::default()
        }
    }

    pub(crate) fn from_con(con: CompactCon) -> Self {
        Self {
            cons: vec![con],
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

    pub(crate) fn plain(var: TypeVar) -> Self {
        Self::contravariant(var)
    }

    pub(crate) fn secondary(mut self) -> Self {
        self.origin = CompactVarOrigin::Secondary;
        self
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum CompactBounds {
    Interval {
        self_var: TypeVar,
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CompactRow {
    pub(crate) items: Vec<CompactType>,
    pub(crate) tail: Box<CompactType>,
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

pub(crate) fn compact_type_var(machine: &ConstraintMachine, root: TypeVar) -> CompactRoot {
    CompactCollector::new(machine).compact_root(root)
}

pub(crate) fn compact_reachable_role_constraints(
    machine: &ConstraintMachine,
    seed: &CompactRoot,
    constraints: &[RoleConstraint],
) -> Vec<CompactRoleConstraint> {
    CompactCollector::new(machine).compact_reachable_role_constraints(seed, constraints)
}

pub(crate) fn compact_role_constraint(
    machine: &ConstraintMachine,
    constraint: &RoleConstraint,
) -> CompactRoleConstraint {
    CompactCollector::new(machine).compact_role_constraint(constraint)
}

pub(crate) fn finalize_compact_root(
    types: &mut TypeArena,
    root: &CompactRoot,
) -> FinalizedCompactRoot {
    CompactFinalizer::new(types).finalize_root(root)
}

pub(crate) fn finalize_compact_type(types: &mut TypeArena, ty: &CompactType) -> PosId {
    CompactFinalizer::new(types).finalize_pos_type(ty)
}

pub(crate) fn finalize_compact_type_to_neg(types: &mut TypeArena, ty: &CompactType) -> NegId {
    CompactFinalizer::new(types).finalize_neg_type(ty)
}

pub(crate) fn finalize_compact_type_to_pos_constraint(
    machine: &mut ConstraintMachine,
    ty: &CompactType,
) -> PosId {
    CompactFinalizer::new(machine).finalize_pos_type(ty)
}

pub(crate) fn finalize_compact_type_to_neg_constraint(
    machine: &mut ConstraintMachine,
    ty: &CompactType,
) -> NegId {
    CompactFinalizer::new(machine).finalize_neg_type(ty)
}

pub(crate) fn finalize_compact_bounds(types: &mut TypeArena, bounds: &CompactBounds) -> NeuId {
    CompactFinalizer::new(types).finalize_bounds(bounds)
}

pub(crate) fn merge_compact_types(
    positive: bool,
    lhs: CompactType,
    rhs: CompactType,
) -> CompactType {
    if is_empty_compact_type(&lhs) {
        return rhs;
    }
    if is_empty_compact_type(&rhs) {
        return lhs;
    }
    if lhs == rhs {
        return lhs;
    }
    if !positive && (lhs.never || rhs.never) {
        return CompactType::never();
    }

    let CompactType {
        vars,
        never,
        builtins,
        cons,
        funs,
        records,
        record_spreads,
        poly_variants,
        tuples,
        rows,
    } = rhs;
    let mut lhs = lhs;
    if positive {
        lhs.never = lhs.never && never;
    } else {
        lhs.never |= never;
    }
    lhs.vars = merge_unique_owned(lhs.vars, vars);
    lhs.builtins = merge_unique_owned(lhs.builtins, builtins);
    lhs.cons = merge_cons(positive, lhs.cons, cons);
    lhs.funs = merge_funs(positive, lhs.funs, funs);
    lhs.records = merge_records(positive, lhs.records, records);
    lhs.record_spreads = merge_unique_owned(lhs.record_spreads, record_spreads);
    lhs.poly_variants = merge_variants(positive, lhs.poly_variants, poly_variants);
    lhs.tuples = merge_tuples(positive, lhs.tuples, tuples);
    lhs.rows = merge_rows(positive, lhs.rows, rows);
    lhs
}

fn is_empty_compact_type(ty: &CompactType) -> bool {
    !ty.never
        && ty.vars.is_empty()
        && ty.builtins.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn free_vars_in_root(root: &CompactRoot) -> FxHashSet<TypeVar> {
    let mut vars = FxHashSet::default();
    collect_free_vars_in_type(&root.root, &mut vars);
    for rec in &root.rec_vars {
        vars.insert(rec.var);
        collect_free_vars_in_bounds(&rec.bounds, &mut vars);
    }
    vars
}

fn free_vars_in_role_constraint(constraint: &CompactRoleConstraint) -> FxHashSet<TypeVar> {
    let mut vars = FxHashSet::default();
    for input in &constraint.inputs {
        collect_free_vars_in_role_arg(input, &mut vars);
    }
    for associated in &constraint.associated {
        collect_free_vars_in_role_arg(&associated.value, &mut vars);
    }
    vars
}

fn collect_free_vars_in_role_arg(arg: &CompactRoleArg, vars: &mut FxHashSet<TypeVar>) {
    collect_free_vars_in_type(&arg.lower, vars);
    collect_free_vars_in_type(&arg.upper, vars);
}

fn collect_free_vars_in_type(ty: &CompactType, vars: &mut FxHashSet<TypeVar>) {
    for var in &ty.vars {
        vars.insert(var.var);
    }
    for con in &ty.cons {
        for arg in &con.args {
            collect_free_vars_in_bounds(arg, vars);
        }
    }
    for fun in &ty.funs {
        collect_free_vars_in_type(&fun.arg, vars);
        collect_free_vars_in_type(&fun.arg_eff, vars);
        collect_free_vars_in_type(&fun.ret_eff, vars);
        collect_free_vars_in_type(&fun.ret, vars);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_free_vars_in_type(&field.value, vars);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_free_vars_in_type(&field.value, vars);
        }
        collect_free_vars_in_type(&spread.tail, vars);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_free_vars_in_type(payload, vars);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_free_vars_in_type(item, vars);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_free_vars_in_type(item, vars);
        }
        collect_free_vars_in_type(&row.tail, vars);
    }
}

fn collect_free_vars_in_bounds(bounds: &CompactBounds, vars: &mut FxHashSet<TypeVar>) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            vars.insert(*self_var);
            collect_free_vars_in_type(lower, vars);
            collect_free_vars_in_type(upper, vars);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_free_vars_in_bounds(arg, vars);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_free_vars_in_bounds(arg, vars);
            collect_free_vars_in_bounds(arg_eff, vars);
            collect_free_vars_in_bounds(ret_eff, vars);
            collect_free_vars_in_bounds(ret, vars);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_free_vars_in_bounds(&field.value, vars);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_free_vars_in_bounds(payload, vars);
                }
            }
        }
    }
}

trait CompactTypeStore {
    fn pos(&self, id: PosId) -> &Pos;
    fn neg(&self, id: NegId) -> &Neg;
    fn alloc_pos(&mut self, pos: Pos) -> PosId;
    fn alloc_neg(&mut self, neg: Neg) -> NegId;
    fn alloc_neu(&mut self, neu: Neu) -> NeuId;
}

impl CompactTypeStore for TypeArena {
    fn pos(&self, id: PosId) -> &Pos {
        TypeArena::pos(self, id)
    }

    fn neg(&self, id: NegId) -> &Neg {
        TypeArena::neg(self, id)
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        TypeArena::alloc_pos(self, pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        TypeArena::alloc_neg(self, neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        TypeArena::alloc_neu(self, neu)
    }
}

impl CompactTypeStore for ConstraintMachine {
    fn pos(&self, id: PosId) -> &Pos {
        self.types().pos(id)
    }

    fn neg(&self, id: NegId) -> &Neg {
        self.types().neg(id)
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        ConstraintMachine::alloc_pos(self, pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        ConstraintMachine::alloc_neg(self, neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        ConstraintMachine::alloc_neu(self, neu)
    }
}

struct CompactFinalizer<'a, T> {
    types: &'a mut T,
}

impl<'a, T: CompactTypeStore> CompactFinalizer<'a, T> {
    fn new(types: &'a mut T) -> Self {
        Self { types }
    }

    fn finalize_root(&mut self, root: &CompactRoot) -> FinalizedCompactRoot {
        let predicate = self.finalize_pos_type(&root.root);
        let rec_vars = root
            .rec_vars
            .iter()
            .map(|rec| FinalizedCompactRecursiveVar {
                var: rec.var,
                bounds: self.finalize_bounds(&rec.bounds),
            })
            .collect();
        FinalizedCompactRoot {
            root: predicate,
            rec_vars,
        }
    }

    fn finalize_pos_type(&mut self, ty: &CompactType) -> PosId {
        if self.is_positive_rowish(ty) {
            return self.finalize_pos_rowish_type(ty);
        }

        let mut parts = Vec::new();
        for var in &ty.vars {
            parts.push(self.alloc_pos(Pos::Var(var.var)));
        }
        for builtin in &ty.builtins {
            parts.push(self.alloc_pos(Pos::Con(builtin_path(*builtin), Vec::new())));
        }
        for con in &ty.cons {
            parts.push(self.finalize_pos_con(con));
        }
        for fun in &ty.funs {
            parts.push(self.finalize_pos_fun(fun));
        }
        for record in &ty.records {
            parts.push(self.finalize_pos_record(record));
        }
        for spread in &ty.record_spreads {
            parts.push(self.finalize_pos_record_spread(spread));
        }
        for variant in &ty.poly_variants {
            parts.push(self.finalize_pos_poly_variant(variant));
        }
        for tuple in &ty.tuples {
            parts.push(self.finalize_pos_tuple(tuple));
        }
        for row in &ty.rows {
            parts.push(self.finalize_pos_row(row));
        }
        self.union_pos(parts)
    }

    fn finalize_neg_type(&mut self, ty: &CompactType) -> NegId {
        if ty.never {
            return self.alloc_neg(Neg::Bot);
        }
        if self.is_negative_rowish(ty) {
            return self.finalize_neg_rowish_type(ty);
        }

        let mut parts = Vec::new();
        for var in &ty.vars {
            parts.push(self.alloc_neg(Neg::Var(var.var)));
        }
        for builtin in &ty.builtins {
            parts.push(self.alloc_neg(Neg::Con(builtin_path(*builtin), Vec::new())));
        }
        for con in &ty.cons {
            parts.push(self.finalize_neg_con(con));
        }
        for fun in &ty.funs {
            parts.push(self.finalize_neg_fun(fun));
        }
        for record in &ty.records {
            parts.push(self.finalize_neg_record(record));
        }
        for variant in &ty.poly_variants {
            parts.push(self.finalize_neg_poly_variant(variant));
        }
        for tuple in &ty.tuples {
            parts.push(self.finalize_neg_tuple(tuple));
        }
        for row in &ty.rows {
            parts.push(self.finalize_neg_row(row));
        }
        self.intersection_neg(parts)
    }

    fn finalize_bounds(&mut self, bounds: &CompactBounds) -> NeuId {
        match bounds {
            CompactBounds::Interval {
                self_var,
                lower,
                upper,
            } => {
                let lower = self.finalize_pos_type(lower);
                let upper = self.finalize_neg_type(upper);
                self.alloc_neu(Neu::Bounds(lower, *self_var, upper))
            }
            CompactBounds::Con { path, args } => {
                let args = args.iter().map(|arg| self.finalize_bounds(arg)).collect();
                self.alloc_neu(Neu::Con(path.clone(), args))
            }
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                let arg = self.finalize_bounds(arg);
                let arg_eff = self.finalize_bounds(arg_eff);
                let ret_eff = self.finalize_bounds(ret_eff);
                let ret = self.finalize_bounds(ret);
                self.alloc_neu(Neu::Fun {
                    arg,
                    arg_eff,
                    ret_eff,
                    ret,
                })
            }
            CompactBounds::Record { fields } => {
                let fields = fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.finalize_bounds(&field.value),
                        optional: field.optional,
                    })
                    .collect();
                self.alloc_neu(Neu::Record(fields))
            }
            CompactBounds::PolyVariant { items } => {
                let items = items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.finalize_bounds(payload))
                                .collect(),
                        )
                    })
                    .collect();
                self.alloc_neu(Neu::PolyVariant(items))
            }
            CompactBounds::Tuple { items } => {
                let items = items
                    .iter()
                    .map(|item| self.finalize_bounds(item))
                    .collect();
                self.alloc_neu(Neu::Tuple(items))
            }
        }
    }

    fn finalize_pos_con(&mut self, con: &CompactCon) -> PosId {
        let args = con
            .args
            .iter()
            .map(|arg| self.finalize_bounds(arg))
            .collect();
        self.alloc_pos(Pos::Con(con.path.clone(), args))
    }

    fn finalize_neg_con(&mut self, con: &CompactCon) -> NegId {
        let args = con
            .args
            .iter()
            .map(|arg| self.finalize_bounds(arg))
            .collect();
        self.alloc_neg(Neg::Con(con.path.clone(), args))
    }

    fn finalize_pos_fun(&mut self, fun: &CompactFun) -> PosId {
        let arg = self.finalize_neg_type(&fun.arg);
        let arg_eff = self.finalize_neg_type(&fun.arg_eff);
        let ret_eff = self.finalize_pos_type(&fun.ret_eff);
        let ret = self.finalize_pos_type(&fun.ret);
        self.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn finalize_neg_fun(&mut self, fun: &CompactFun) -> NegId {
        let arg = self.finalize_pos_type(&fun.arg);
        let arg_eff = self.finalize_pos_type(&fun.arg_eff);
        let ret_eff = self.finalize_neg_type(&fun.ret_eff);
        let ret = self.finalize_neg_type(&fun.ret);
        self.alloc_neg(Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn finalize_pos_record(&mut self, record: &CompactRecord) -> PosId {
        let fields = record
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: self.finalize_pos_type(&field.value),
                optional: field.optional,
            })
            .collect();
        self.alloc_pos(Pos::Record(fields))
    }

    fn finalize_neg_record(&mut self, record: &CompactRecord) -> NegId {
        let fields = record
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: self.finalize_neg_type(&field.value),
                optional: field.optional,
            })
            .collect();
        self.alloc_neg(Neg::Record(fields))
    }

    fn finalize_pos_record_spread(&mut self, spread: &CompactRecordSpread) -> PosId {
        let fields = spread
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: self.finalize_pos_type(&field.value),
                optional: field.optional,
            })
            .collect();
        let tail = self.finalize_pos_type(&spread.tail);
        if spread.tail_wins {
            self.alloc_pos(Pos::RecordTailSpread { fields, tail })
        } else {
            self.alloc_pos(Pos::RecordHeadSpread { tail, fields })
        }
    }

    fn finalize_pos_poly_variant(&mut self, variant: &CompactPolyVariant) -> PosId {
        let items = variant
            .items
            .iter()
            .map(|(name, payloads)| {
                (
                    name.clone(),
                    payloads
                        .iter()
                        .map(|payload| self.finalize_pos_type(payload))
                        .collect(),
                )
            })
            .collect();
        self.alloc_pos(Pos::PolyVariant(items))
    }

    fn finalize_neg_poly_variant(&mut self, variant: &CompactPolyVariant) -> NegId {
        let items = variant
            .items
            .iter()
            .map(|(name, payloads)| {
                (
                    name.clone(),
                    payloads
                        .iter()
                        .map(|payload| self.finalize_neg_type(payload))
                        .collect(),
                )
            })
            .collect();
        self.alloc_neg(Neg::PolyVariant(items))
    }

    fn finalize_pos_tuple(&mut self, tuple: &CompactTuple) -> PosId {
        let items = tuple
            .items
            .iter()
            .map(|item| self.finalize_pos_type(item))
            .collect();
        self.alloc_pos(Pos::Tuple(items))
    }

    fn finalize_neg_tuple(&mut self, tuple: &CompactTuple) -> NegId {
        let items = tuple
            .items
            .iter()
            .map(|item| self.finalize_neg_type(item))
            .collect();
        self.alloc_neg(Neg::Tuple(items))
    }

    fn finalize_pos_rowish_type(&mut self, ty: &CompactType) -> PosId {
        let mut items = ty
            .vars
            .iter()
            .map(|var| self.alloc_pos(Pos::Var(var.var)))
            .collect::<Vec<_>>();
        for row in &ty.rows {
            self.extend_pos_row_items(row, &mut items);
        }
        self.alloc_pos(Pos::Row(items))
    }

    fn finalize_neg_rowish_type(&mut self, ty: &CompactType) -> NegId {
        let rows = ty
            .rows
            .iter()
            .map(|row| self.finalize_neg_row(row))
            .collect();
        self.intersection_neg(rows)
    }

    fn finalize_pos_row(&mut self, row: &CompactRow) -> PosId {
        let mut items = Vec::new();
        self.extend_pos_row_items(row, &mut items);
        self.alloc_pos(Pos::Row(items))
    }

    fn finalize_neg_row(&mut self, row: &CompactRow) -> NegId {
        let items = row
            .items
            .iter()
            .map(|item| self.finalize_neg_type(item))
            .collect();
        let tail = self.finalize_neg_row_tail(&row.tail);
        self.alloc_neg(Neg::Row(items, tail))
    }

    fn extend_pos_row_items(&mut self, row: &CompactRow, out: &mut Vec<PosId>) {
        for item in &row.items {
            out.push(self.finalize_pos_type(item));
        }
        if !is_empty_compact_type(&row.tail) {
            out.push(self.finalize_pos_type(&row.tail));
        }
    }

    fn finalize_neg_row_tail(&mut self, ty: &CompactType) -> NegId {
        if is_empty_compact_type(ty) {
            return self.alloc_neg(Neg::Top);
        }
        self.finalize_neg_type(ty)
    }

    fn is_positive_rowish(&self, ty: &CompactType) -> bool {
        !ty.rows.is_empty()
            && !ty.never
            && ty.builtins.is_empty()
            && ty.cons.is_empty()
            && ty.funs.is_empty()
            && ty.records.is_empty()
            && ty.record_spreads.is_empty()
            && ty.poly_variants.is_empty()
            && ty.tuples.is_empty()
    }

    fn is_negative_rowish(&self, ty: &CompactType) -> bool {
        !ty.rows.is_empty()
            && ty.vars.is_empty()
            && ty.builtins.is_empty()
            && ty.cons.is_empty()
            && ty.funs.is_empty()
            && ty.records.is_empty()
            && ty.record_spreads.is_empty()
            && ty.poly_variants.is_empty()
            && ty.tuples.is_empty()
    }

    fn union_pos(&mut self, input: Vec<PosId>) -> PosId {
        let mut parts = Vec::new();
        for part in input {
            if matches!(self.types.pos(part), Pos::Bot) || parts.contains(&part) {
                continue;
            }
            parts.push(part);
        }
        let Some(first) = parts.first().copied() else {
            return self.alloc_pos(Pos::Bot);
        };
        parts
            .into_iter()
            .skip(1)
            .fold(first, |acc, part| self.alloc_pos(Pos::Union(acc, part)))
    }

    fn intersection_neg(&mut self, input: Vec<NegId>) -> NegId {
        if input
            .iter()
            .any(|part| matches!(self.types.neg(*part), Neg::Bot))
        {
            return self.alloc_neg(Neg::Bot);
        }
        let mut parts = Vec::new();
        for part in input {
            if matches!(self.types.neg(part), Neg::Top) || parts.contains(&part) {
                continue;
            }
            parts.push(part);
        }
        let Some(first) = parts.first().copied() else {
            return self.alloc_neg(Neg::Top);
        };
        parts.into_iter().skip(1).fold(first, |acc, part| {
            self.alloc_neg(Neg::Intersection(acc, part))
        })
    }

    fn alloc_pos(&mut self, pos: Pos) -> PosId {
        self.types.alloc_pos(pos)
    }

    fn alloc_neg(&mut self, neg: Neg) -> NegId {
        self.types.alloc_neg(neg)
    }

    fn alloc_neu(&mut self, neu: Neu) -> NeuId {
        self.types.alloc_neu(neu)
    }
}

fn builtin_path(builtin: BuiltinType) -> Vec<String> {
    vec![builtin.surface_name().into()]
}

fn merge_unique_owned<T: PartialEq>(mut lhs: Vec<T>, rhs: Vec<T>) -> Vec<T> {
    for item in rhs {
        if !lhs.contains(&item) {
            lhs.push(item);
        }
    }
    lhs
}

fn merge_cons(positive: bool, lhs: Vec<CompactCon>, rhs: Vec<CompactCon>) -> Vec<CompactCon> {
    let mut out = lhs;
    for other in rhs {
        if let Some(existing) = out.iter_mut().find(|con| {
            con.path == other.path
                && con.args.len() == other.args.len()
                && compact_bounds_slices_mergeable(&con.args, &other.args)
        }) {
            existing.args = mem::take(&mut existing.args)
                .into_iter()
                .zip(other.args)
                .map(|(lhs, rhs)| merge_compact_bounds(positive, lhs, rhs))
                .collect();
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

fn compact_bounds_slices_mergeable(lhs: &[CompactBounds], rhs: &[CompactBounds]) -> bool {
    lhs.iter()
        .zip(rhs)
        .all(|(lhs, rhs)| compact_bounds_mergeable(lhs, rhs))
}

fn compact_bounds_mergeable(lhs: &CompactBounds, rhs: &CompactBounds) -> bool {
    match (lhs, rhs) {
        (
            CompactBounds::Interval { self_var, .. },
            CompactBounds::Interval {
                self_var: rhs_self, ..
            },
        ) => self_var == rhs_self,
        (
            CompactBounds::Con { path, args },
            CompactBounds::Con {
                path: rhs_path,
                args: rhs_args,
            },
        ) => {
            path == rhs_path
                && args.len() == rhs_args.len()
                && compact_bounds_slices_mergeable(args, rhs_args)
        }
        (CompactBounds::Tuple { items }, CompactBounds::Tuple { items: rhs_items }) => {
            items.len() == rhs_items.len() && compact_bounds_slices_mergeable(items, rhs_items)
        }
        (CompactBounds::Fun { .. }, CompactBounds::Fun { .. }) => true,
        (CompactBounds::Record { fields }, CompactBounds::Record { fields: rhs_fields }) => {
            fields.len() == rhs_fields.len()
                && fields.iter().zip(rhs_fields).all(|(field, rhs_field)| {
                    field.name == rhs_field.name
                        && field.optional == rhs_field.optional
                        && compact_bounds_mergeable(&field.value, &rhs_field.value)
                })
        }
        (CompactBounds::PolyVariant { items }, CompactBounds::PolyVariant { items: rhs_items }) => {
            items.len() == rhs_items.len()
        }
        _ => false,
    }
}

fn merge_compact_bounds(positive: bool, lhs: CompactBounds, rhs: CompactBounds) -> CompactBounds {
    match (lhs, rhs) {
        (
            CompactBounds::Interval {
                self_var,
                lower,
                upper,
            },
            CompactBounds::Interval {
                self_var: rhs_self,
                lower: rhs_lower,
                upper: rhs_upper,
            },
        ) if self_var == rhs_self => CompactBounds::Interval {
            self_var,
            lower: merge_compact_types(positive, lower, rhs_lower),
            upper: merge_compact_types(!positive, upper, rhs_upper),
        },
        (
            CompactBounds::Con { path, args },
            CompactBounds::Con {
                path: rhs_path,
                args: rhs_args,
            },
        ) if path == rhs_path && args.len() == rhs_args.len() => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .zip(rhs_args)
                .map(|(lhs, rhs)| merge_compact_bounds(positive, lhs, rhs))
                .collect(),
        },
        (CompactBounds::Tuple { items }, CompactBounds::Tuple { items: rhs_items })
            if items.len() == rhs_items.len() =>
        {
            CompactBounds::Tuple {
                items: items
                    .into_iter()
                    .zip(rhs_items)
                    .map(|(lhs, rhs)| merge_compact_bounds(positive, lhs, rhs))
                    .collect(),
            }
        }
        (
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            },
            CompactBounds::Fun {
                arg: rhs_arg,
                arg_eff: rhs_arg_eff,
                ret_eff: rhs_ret_eff,
                ret: rhs_ret,
            },
        ) => CompactBounds::Fun {
            arg: Box::new(merge_compact_bounds(!positive, *arg, *rhs_arg)),
            arg_eff: Box::new(merge_compact_bounds(!positive, *arg_eff, *rhs_arg_eff)),
            ret_eff: Box::new(merge_compact_bounds(positive, *ret_eff, *rhs_ret_eff)),
            ret: Box::new(merge_compact_bounds(positive, *ret, *rhs_ret)),
        },
        (CompactBounds::Record { fields }, CompactBounds::Record { fields: rhs_fields }) => {
            CompactBounds::Record {
                fields: fields
                    .into_iter()
                    .zip(rhs_fields)
                    .map(|(field, rhs_field)| RecordField {
                        name: field.name,
                        value: merge_compact_bounds(positive, field.value, rhs_field.value),
                        optional: field.optional && rhs_field.optional,
                    })
                    .collect(),
            }
        }
        (CompactBounds::PolyVariant { items }, CompactBounds::PolyVariant { items: rhs_items })
            if items == rhs_items =>
        {
            CompactBounds::PolyVariant { items }
        }
        (lhs, rhs) if lhs == rhs => lhs,
        (lhs, _) => lhs,
    }
}

fn merge_funs(positive: bool, lhs: Vec<CompactFun>, rhs: Vec<CompactFun>) -> Vec<CompactFun> {
    let mut iter = lhs.into_iter().chain(rhs);
    let Some(mut acc) = iter.next() else {
        return Vec::new();
    };
    for other in iter {
        acc = CompactFun {
            arg: merge_compact_types(!positive, acc.arg, other.arg),
            arg_eff: merge_compact_types(!positive, acc.arg_eff, other.arg_eff),
            ret_eff: merge_compact_types(positive, acc.ret_eff, other.ret_eff),
            ret: merge_compact_types(positive, acc.ret, other.ret),
        };
    }
    vec![acc]
}

fn merge_records(
    positive: bool,
    lhs: Vec<CompactRecord>,
    rhs: Vec<CompactRecord>,
) -> Vec<CompactRecord> {
    let mut iter = lhs.into_iter().chain(rhs);
    let Some(mut acc) = iter.next() else {
        return Vec::new();
    };
    for other in iter {
        let mut rhs_fields = other
            .fields
            .into_iter()
            .map(|field| (field.name.clone(), field))
            .collect::<FxHashMap<_, _>>();
        let mut fields = Vec::new();
        for lhs_field in acc.fields {
            match rhs_fields.remove(&lhs_field.name) {
                Some(rhs_field) => fields.push(RecordField {
                    name: lhs_field.name,
                    value: merge_compact_types(positive, lhs_field.value, rhs_field.value),
                    optional: lhs_field.optional && rhs_field.optional,
                }),
                None if !positive => fields.push(lhs_field),
                None => {}
            }
        }
        if !positive {
            for rhs_field in rhs_fields.into_values() {
                if !fields.iter().any(|field| field.name == rhs_field.name) {
                    fields.push(rhs_field);
                }
            }
        }
        acc = CompactRecord { fields };
    }
    vec![acc]
}

fn merge_variants(
    positive: bool,
    lhs: Vec<CompactPolyVariant>,
    rhs: Vec<CompactPolyVariant>,
) -> Vec<CompactPolyVariant> {
    let mut items = Vec::<(String, Vec<CompactType>)>::new();
    for variant in lhs.into_iter().chain(rhs) {
        for (name, payloads) in variant.items {
            if let Some((_, existing_payloads)) =
                items.iter_mut().find(|(existing_name, existing_payloads)| {
                    *existing_name == name && existing_payloads.len() == payloads.len()
                })
            {
                *existing_payloads = mem::take(existing_payloads)
                    .into_iter()
                    .zip(payloads)
                    .map(|(lhs, rhs)| merge_compact_types(positive, lhs, rhs))
                    .collect();
            } else {
                items.push((name, payloads));
            }
        }
    }
    if items.is_empty() {
        Vec::new()
    } else {
        vec![CompactPolyVariant { items }]
    }
}

fn merge_tuples(
    positive: bool,
    lhs: Vec<CompactTuple>,
    rhs: Vec<CompactTuple>,
) -> Vec<CompactTuple> {
    let mut out = lhs;
    for other in rhs {
        if let Some(existing) = out
            .iter_mut()
            .find(|tuple| tuple.items.len() == other.items.len())
        {
            existing.items = mem::take(&mut existing.items)
                .into_iter()
                .zip(other.items)
                .map(|(lhs, rhs)| merge_compact_types(positive, lhs, rhs))
                .collect();
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

fn merge_rows(positive: bool, lhs: Vec<CompactRow>, rhs: Vec<CompactRow>) -> Vec<CompactRow> {
    let mut out = lhs;
    for other in rhs {
        if let Some(existing) = out.iter_mut().find(|row| row.tail == other.tail) {
            existing.items = merge_unique_owned(mem::take(&mut existing.items), other.items);
        } else if let Some(existing) = out.iter_mut().find(|row| row.items == other.items) {
            existing.tail = Box::new(merge_compact_types(
                positive,
                (*existing.tail).clone(),
                (*other.tail).clone(),
            ));
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

struct CompactCollector<'a> {
    machine: &'a ConstraintMachine,
    in_progress: FxHashSet<(TypeVar, Polarity)>,
    recursive: FxHashSet<(TypeVar, Polarity)>,
    rec_vars: FxHashMap<TypeVar, CompactBounds>,
}

impl<'a> CompactCollector<'a> {
    fn new(machine: &'a ConstraintMachine) -> Self {
        Self {
            machine,
            in_progress: FxHashSet::default(),
            recursive: FxHashSet::default(),
            rec_vars: FxHashMap::default(),
        }
    }

    fn compact_root(mut self, root: TypeVar) -> CompactRoot {
        let root_ty = self.compact_var_side(
            root,
            Polarity::Positive,
            ConstraintWeight::empty(),
            VarExpansion::Expand,
        );
        let mut rec_vars = self
            .rec_vars
            .into_iter()
            .map(|(var, bounds)| CompactRecursiveVar { var, bounds })
            .collect::<Vec<_>>();
        rec_vars.sort_by_key(|rec| rec.var.0);
        CompactRoot {
            root: root_ty,
            rec_vars,
        }
    }

    fn compact_reachable_role_constraints(
        mut self,
        seed: &CompactRoot,
        constraints: &[RoleConstraint],
    ) -> Vec<CompactRoleConstraint> {
        let mut reachable = free_vars_in_root(seed);
        let mut selected = vec![false; constraints.len()];
        let mut out = Vec::new();

        loop {
            let mut changed = false;
            for (index, constraint) in constraints.iter().enumerate() {
                if selected[index] {
                    continue;
                }
                let raw_vars = constraint.raw_vars(self.machine.types());
                if !raw_vars.is_empty() && raw_vars.is_disjoint(&reachable) {
                    continue;
                }

                selected[index] = true;
                let compact = self.compact_role_constraint(constraint);
                for var in free_vars_in_role_constraint(&compact) {
                    reachable.insert(var);
                }
                out.push(compact);
                changed = true;
            }
            if !changed {
                return out;
            }
        }
    }

    fn compact_role_constraint(&mut self, constraint: &RoleConstraint) -> CompactRoleConstraint {
        CompactRoleConstraint {
            role: constraint.role.clone(),
            inputs: constraint
                .inputs
                .iter()
                .map(|arg| self.compact_role_arg(arg))
                .collect(),
            associated: constraint
                .associated
                .iter()
                .map(|associated| self.compact_role_associated(associated))
                .collect(),
        }
    }

    fn compact_role_associated(
        &mut self,
        associated: &RoleAssociatedConstraint,
    ) -> CompactRoleAssociatedType {
        CompactRoleAssociatedType {
            name: associated.name.clone(),
            value: self.compact_role_arg(&associated.value),
        }
    }

    fn compact_role_arg(&mut self, arg: &RoleConstraintArg) -> CompactRoleArg {
        CompactRoleArg {
            lower: self.compact_pos_id(arg.lower, ConstraintWeight::empty()),
            upper: self.compact_neg_id(arg.upper, ConstraintWeight::empty()),
        }
    }

    fn compact_var_side(
        &mut self,
        var: TypeVar,
        polarity: Polarity,
        weight: ConstraintWeight,
        expansion: VarExpansion,
    ) -> CompactType {
        if matches!(expansion, VarExpansion::DoNotExpand) {
            return CompactType::from_var(self.compact_var_occurrence(var, polarity, weight));
        }

        let key = (var, polarity);
        if self.in_progress.contains(&key) {
            self.recursive.insert(key);
            return CompactType::from_var(self.compact_var_occurrence(var, polarity, weight));
        }

        self.in_progress.insert(key);
        let bounds = self.compact_var_bounds(var, polarity);
        let with_self = merge_compact_types(
            polarity.is_positive(),
            CompactType::from_var(self.compact_var_occurrence(var, polarity, weight)),
            bounds,
        );
        self.in_progress.remove(&key);

        if self.recursive.remove(&key) {
            self.record_recursive_side(var, polarity, with_self.clone());
            return CompactType::from_var(self.compact_var_occurrence(
                var,
                polarity,
                ConstraintWeight::empty(),
            ));
        }

        with_self
    }

    fn compact_var_occurrence(
        &self,
        var: TypeVar,
        polarity: Polarity,
        weight: ConstraintWeight,
    ) -> CompactVar {
        if polarity.is_positive() {
            CompactVar::covariant(var, weight)
        } else {
            CompactVar::contravariant(var)
        }
    }

    fn compact_var_bounds(&mut self, var: TypeVar, polarity: Polarity) -> CompactType {
        let Some(bounds) = self.machine.bounds().of(var).cloned() else {
            return CompactType::default();
        };
        match polarity {
            Polarity::Positive => self.compact_lower_bounds(&bounds),
            Polarity::Negative => self.compact_upper_bounds(&bounds),
        }
    }

    fn compact_lower_bounds(&mut self, bounds: &VarBounds) -> CompactType {
        bounds
            .lowers()
            .iter()
            .fold(CompactType::default(), |acc, bound| {
                merge_compact_types(
                    true,
                    acc,
                    self.compact_pos_bound_id(bound.pos, bound.weights.left.clone()),
                )
            })
    }

    fn compact_upper_bounds(&mut self, bounds: &VarBounds) -> CompactType {
        bounds
            .uppers()
            .iter()
            .fold(CompactType::default(), |acc, bound| {
                merge_compact_types(
                    false,
                    acc,
                    self.compact_neg_bound_id(bound.neg, bound.weights.right.clone()),
                )
            })
    }

    fn compact_pos_bound_id(&mut self, id: PosId, weight: ConstraintWeight) -> CompactType {
        match self.machine.types().pos(id).clone() {
            Pos::Var(var) => CompactType::from_var(CompactVar::covariant(var, weight)),
            Pos::Union(lhs, rhs) => {
                let lhs = self.compact_pos_bound_id(lhs, weight.clone());
                let rhs = self.compact_pos_bound_id(rhs, weight);
                merge_compact_types(true, lhs, rhs)
            }
            _ => self.compact_pos_id(id, weight),
        }
    }

    fn compact_neg_bound_id(&mut self, id: NegId, weight: ConstraintWeight) -> CompactType {
        match self.machine.types().neg(id).clone() {
            Neg::Var(var) => CompactType::from_var(CompactVar::contravariant(var)),
            Neg::Intersection(lhs, rhs) => {
                let lhs = self.compact_neg_bound_id(lhs, weight.clone());
                let rhs = self.compact_neg_bound_id(rhs, weight);
                merge_compact_types(false, lhs, rhs)
            }
            _ => self.compact_neg_id(id, weight),
        }
    }

    fn compact_pos_id(&mut self, id: PosId, weight: ConstraintWeight) -> CompactType {
        match self.machine.types().pos(id).clone() {
            Pos::Bot => CompactType::default(),
            Pos::Var(var) => {
                self.compact_var_side(var, Polarity::Positive, weight, VarExpansion::Expand)
            }
            Pos::Con(path, args) => self.compact_con(path, args, weight),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactType::from_fun(CompactFun {
                arg: self.compact_neg_id(arg, ConstraintWeight::empty()),
                arg_eff: self.compact_neg_id(arg_eff, ConstraintWeight::empty()),
                ret_eff: self.compact_pos_id(ret_eff, weight.clone()),
                ret: self.compact_pos_id(ret, weight),
            }),
            Pos::Record(fields) => CompactType::from_record(CompactRecord {
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.compact_pos_id(field.value, weight.clone()),
                        optional: field.optional,
                    })
                    .collect(),
            }),
            Pos::RecordTailSpread { fields, tail } => {
                CompactType::from_record_spread(CompactRecordSpread {
                    fields: fields
                        .into_iter()
                        .map(|field| RecordField {
                            name: field.name,
                            value: self.compact_pos_id(field.value, weight.clone()),
                            optional: field.optional,
                        })
                        .collect(),
                    tail: Box::new(self.compact_pos_id(tail, weight)),
                    tail_wins: true,
                })
            }
            Pos::RecordHeadSpread { tail, fields } => {
                CompactType::from_record_spread(CompactRecordSpread {
                    fields: fields
                        .into_iter()
                        .map(|field| RecordField {
                            name: field.name,
                            value: self.compact_pos_id(field.value, weight.clone()),
                            optional: field.optional,
                        })
                        .collect(),
                    tail: Box::new(self.compact_pos_id(tail, weight)),
                    tail_wins: false,
                })
            }
            Pos::PolyVariant(items) => CompactType::from_poly_variant(CompactPolyVariant {
                items: items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.compact_pos_id(payload, weight.clone()))
                                .collect(),
                        )
                    })
                    .collect(),
            }),
            Pos::Tuple(items) => CompactType::from_tuple(CompactTuple {
                items: items
                    .into_iter()
                    .map(|item| self.compact_pos_id(item, weight.clone()))
                    .collect(),
            }),
            Pos::Row(items) => self.compact_pos_row(items, weight),
            Pos::NonSubtract(pos, _) => self.compact_pos_id(pos, weight),
            Pos::Union(lhs, rhs) => {
                let lhs = self.compact_pos_id(lhs, weight.clone());
                let rhs = self.compact_pos_id(rhs, weight);
                merge_compact_types(true, lhs, rhs)
            }
        }
    }

    fn compact_neg_id(&mut self, id: NegId, weight: ConstraintWeight) -> CompactType {
        match self.machine.types().neg(id).clone() {
            Neg::Top => CompactType::default(),
            Neg::Bot => CompactType::never(),
            Neg::Var(var) => self.compact_var_side(
                var,
                Polarity::Negative,
                ConstraintWeight::empty(),
                VarExpansion::Expand,
            ),
            Neg::Con(path, args) => self.compact_con(path, args, ConstraintWeight::empty()),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactType::from_fun(CompactFun {
                arg: self.compact_pos_id(arg, weight.clone()),
                arg_eff: self.compact_pos_id(arg_eff, weight.clone()),
                ret_eff: self.compact_neg_id(ret_eff, ConstraintWeight::empty()),
                ret: self.compact_neg_id(ret, ConstraintWeight::empty()),
            }),
            Neg::Record(fields) => CompactType::from_record(CompactRecord {
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.compact_neg_id(field.value, ConstraintWeight::empty()),
                        optional: field.optional,
                    })
                    .collect(),
            }),
            Neg::PolyVariant(items) => CompactType::from_poly_variant(CompactPolyVariant {
                items: items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| {
                                    self.compact_neg_id(payload, ConstraintWeight::empty())
                                })
                                .collect(),
                        )
                    })
                    .collect(),
            }),
            Neg::Tuple(items) => CompactType::from_tuple(CompactTuple {
                items: items
                    .into_iter()
                    .map(|item| self.compact_neg_id(item, ConstraintWeight::empty()))
                    .collect(),
            }),
            Neg::Row(items, tail) => self.compact_neg_row(items, tail, weight),
            Neg::Intersection(lhs, rhs) => {
                let lhs = self.compact_neg_id(lhs, weight.clone());
                let rhs = self.compact_neg_id(rhs, weight);
                merge_compact_types(false, lhs, rhs)
            }
        }
    }

    fn compact_con(
        &mut self,
        path: Vec<String>,
        args: Vec<NeuId>,
        weight: ConstraintWeight,
    ) -> CompactType {
        if args.is_empty()
            && path.len() == 1
            && let Some(builtin) = BuiltinType::from_surface_name(&path[0])
        {
            return CompactType::from_builtin(builtin);
        }
        CompactType::from_con(CompactCon {
            path,
            args: args
                .into_iter()
                .map(|arg| self.compact_neu_id(arg, weight.clone()))
                .collect(),
        })
    }

    fn compact_neu_id(&mut self, id: NeuId, weight: ConstraintWeight) -> CompactBounds {
        match self.machine.types().neu(id).clone() {
            Neu::Bounds(lower, self_var, upper) => CompactBounds::Interval {
                self_var,
                lower: self.compact_pos_id(lower, weight),
                upper: self.compact_neg_id(upper, ConstraintWeight::empty()),
            },
            Neu::Con(path, args) => CompactBounds::Con {
                path,
                args: args
                    .into_iter()
                    .map(|arg| self.compact_neu_id(arg, weight.clone()))
                    .collect(),
            },
            Neu::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactBounds::Fun {
                arg: Box::new(self.compact_neu_id(arg, ConstraintWeight::empty())),
                arg_eff: Box::new(self.compact_neu_id(arg_eff, ConstraintWeight::empty())),
                ret_eff: Box::new(self.compact_neu_id(ret_eff, weight.clone())),
                ret: Box::new(self.compact_neu_id(ret, weight)),
            },
            Neu::Record(fields) => CompactBounds::Record {
                fields: fields
                    .into_iter()
                    .map(|field| RecordField {
                        name: field.name,
                        value: self.compact_neu_id(field.value, weight.clone()),
                        optional: field.optional,
                    })
                    .collect(),
            },
            Neu::PolyVariant(items) => CompactBounds::PolyVariant {
                items: items
                    .into_iter()
                    .map(|(name, payloads)| {
                        (
                            name,
                            payloads
                                .into_iter()
                                .map(|payload| self.compact_neu_id(payload, weight.clone()))
                                .collect(),
                        )
                    })
                    .collect(),
            },
            Neu::Tuple(items) => CompactBounds::Tuple {
                items: items
                    .into_iter()
                    .map(|item| self.compact_neu_id(item, weight.clone()))
                    .collect(),
            },
        }
    }

    fn compact_pos_row(&mut self, items: Vec<PosId>, weight: ConstraintWeight) -> CompactType {
        let mut vars_and_nested = CompactType::default();
        let mut concrete_items = Vec::new();
        for item in items {
            match self.machine.types().pos(item).clone() {
                Pos::Var(var) => {
                    vars_and_nested = merge_compact_types(
                        true,
                        vars_and_nested,
                        self.compact_var_side(
                            var,
                            Polarity::Positive,
                            weight.clone(),
                            VarExpansion::Expand,
                        ),
                    );
                }
                Pos::Row(nested) => {
                    vars_and_nested = merge_compact_types(
                        true,
                        vars_and_nested,
                        self.compact_pos_row(nested, weight.clone()),
                    );
                }
                _ => concrete_items.push(self.compact_pos_id(item, weight.clone())),
            }
        }
        if concrete_items.is_empty() {
            vars_and_nested
        } else {
            merge_compact_types(
                true,
                vars_and_nested,
                CompactType::from_row(CompactRow {
                    items: concrete_items,
                    tail: Box::new(CompactType::default()),
                }),
            )
        }
    }

    fn compact_neg_row(
        &mut self,
        items: Vec<NegId>,
        tail: NegId,
        weight: ConstraintWeight,
    ) -> CompactType {
        CompactType::from_row(CompactRow {
            items: items
                .into_iter()
                .map(|item| self.compact_neg_id(item, ConstraintWeight::empty()))
                .collect(),
            tail: Box::new(self.compact_neg_id(tail, weight)),
        })
    }

    fn record_recursive_side(&mut self, var: TypeVar, polarity: Polarity, side: CompactType) {
        let entry = self
            .rec_vars
            .entry(var)
            .or_insert_with(|| CompactBounds::Interval {
                self_var: var,
                lower: CompactType::default(),
                upper: CompactType::default(),
            });
        let CompactBounds::Interval { lower, upper, .. } = entry else {
            return;
        };
        match polarity {
            Polarity::Positive => *lower = side,
            Polarity::Negative => *upper = side,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VarExpansion {
    Expand,
    DoNotExpand,
}

#[cfg(test)]
mod tests {
    use poly::types::{Neg, Pos, SubtractId};

    use super::*;
    use crate::constraints::{ConstraintMachine, ConstraintWeights, TypeLevel};
    use crate::roles::{RoleAssociatedConstraint, RoleConstraint, RoleConstraintArg};

    #[test]
    fn covariant_vars_keep_weight() {
        let weight = ConstraintWeight::from_ids([SubtractId(1), SubtractId(1), SubtractId(0)]);
        let var = CompactVar::covariant(TypeVar(7), weight);

        assert_eq!(var.var, TypeVar(7));
        assert!(var.weight.contains(SubtractId(0)));
        assert!(var.weight.contains(SubtractId(1)));
    }

    #[test]
    fn contravariant_vars_drop_weight() {
        let var = CompactVar::contravariant(TypeVar(3));

        assert_eq!(var.var, TypeVar(3));
        assert!(var.weight.is_empty());
    }

    #[test]
    fn interval_always_has_center_var() {
        let bounds = CompactBounds::Interval {
            self_var: TypeVar(2),
            lower: CompactType::from_var(CompactVar::plain(TypeVar(2))),
            upper: CompactType::default(),
        };

        let CompactBounds::Interval { self_var, .. } = bounds else {
            panic!("expected interval");
        };
        assert_eq!(self_var, TypeVar(2));
    }

    #[test]
    fn collect_pushes_weight_into_covariant_type_argument_vars() {
        let mut machine = ConstraintMachine::new();
        let root = TypeVar(0);
        let payload = TypeVar(1);
        let payload_pos = machine.alloc_pos(Pos::Var(payload));
        let payload_neg = machine.alloc_neg(Neg::Var(payload));
        let payload_neu = machine.alloc_neu(Neu::Bounds(payload_pos, payload, payload_neg));
        let list = machine.alloc_pos(Pos::Con(vec!["list".into()], vec![payload_neu]));
        let root_upper = machine.alloc_neg(Neg::Var(root));
        machine.weighted_subtype(
            list,
            ConstraintWeights::empty().with_left(SubtractId(4)),
            root_upper,
        );

        let compact = compact_type_var(&machine, root);
        let list = compact
            .root
            .cons
            .iter()
            .find(|con| compact_path_is(con.path.as_slice(), "list"))
            .expect("list lower bound should be collected");
        let CompactBounds::Interval { lower, upper, .. } = &list.args[0] else {
            panic!("list payload should be an interval");
        };

        assert!(
            lower
                .vars
                .iter()
                .any(|var| var.var == payload && var.weight.contains(SubtractId(4)))
        );
        assert!(
            upper
                .vars
                .iter()
                .all(|var| var.var != payload || var.weight.is_empty())
        );
    }

    #[test]
    fn collect_stops_bare_variable_bounds_but_expands_structured_tails() {
        let mut machine = ConstraintMachine::new();
        let epsilon = TypeVar(1);
        let zeta = TypeVar(2);
        let gamma = TypeVar(3);
        let eta = TypeVar(4);

        let io = machine.alloc_neg(Neg::Con(vec!["io".into()], Vec::new()));
        let eta_tail = machine.alloc_neg(Neg::Var(eta));
        let epsilon_row = machine.alloc_neg(Neg::Row(vec![io], eta_tail));
        let epsilon_pos = machine.alloc_pos(Pos::Var(epsilon));
        machine.subtype(epsilon_pos, epsilon_row);

        let flip = machine.alloc_neg(Neg::Con(vec!["flip".into()], Vec::new()));
        let gamma_tail = machine.alloc_neg(Neg::Var(gamma));
        let zeta_row = machine.alloc_neg(Neg::Row(vec![flip], gamma_tail));
        let zeta_pos = machine.alloc_pos(Pos::Var(zeta));
        machine.subtype(zeta_pos, zeta_row);

        let epsilon_neg = machine.alloc_neg(Neg::Var(epsilon));
        let undet = machine.alloc_neg(Neg::Con(vec!["undet".into()], Vec::new()));
        let zeta_tail = machine.alloc_neg(Neg::Var(zeta));
        let structured_row = machine.alloc_neg(Neg::Row(vec![undet], zeta_tail));

        let mut collector = CompactCollector::new(&machine);
        let bare = collector.compact_neg_bound_id(epsilon_neg, ConstraintWeight::empty());
        let structured = collector.compact_neg_id(structured_row, ConstraintWeight::empty());

        assert!(bare.vars.iter().any(|var| var.var == epsilon));
        assert!(!compact_row_contains_path(&bare, "io"));
        assert!(compact_row_contains_path(&structured, "undet"));
        assert!(compact_row_contains_path(&structured, "flip"));
    }

    #[test]
    fn positive_row_variables_are_collected_as_flat_vars() {
        let mut machine = ConstraintMachine::new();
        let root = TypeVar(0);
        let alpha = TypeVar(1);
        let gamma = TypeVar(2);
        let alpha_item = machine.alloc_pos(Pos::Var(alpha));
        let gamma_item = machine.alloc_pos(Pos::Var(gamma));
        let io_item = machine.alloc_pos(Pos::Con(vec!["io".into()], Vec::new()));
        let row = machine.alloc_pos(Pos::Row(vec![alpha_item, gamma_item, io_item]));
        let root_upper = machine.alloc_neg(Neg::Var(root));
        machine.subtype(row, root_upper);

        let compact = compact_type_var(&machine, root);

        assert!(compact.root.vars.iter().any(|var| var.var == alpha));
        assert!(compact.root.vars.iter().any(|var| var.var == gamma));
        assert!(compact_row_contains_path(&compact.root, "io"));
    }

    #[test]
    fn reachable_role_collect_pulls_roles_from_main_type_frontier() {
        let mut machine = ConstraintMachine::new();
        let root_var = TypeVar(0);
        let output_var = TypeVar(1);
        let next_var = TypeVar(2);
        let unrelated_var = TypeVar(3);
        let seed = CompactRoot {
            root: CompactType::from_var(CompactVar::plain(root_var)),
            rec_vars: Vec::new(),
        };
        let constraints = vec![
            RoleConstraint {
                role: vec!["First".into()],
                inputs: vec![role_arg(&mut machine, root_var)],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_arg(&mut machine, output_var),
                }],
            },
            RoleConstraint {
                role: vec!["Second".into()],
                inputs: vec![role_arg(&mut machine, output_var)],
                associated: vec![RoleAssociatedConstraint {
                    name: "out".into(),
                    value: role_arg(&mut machine, next_var),
                }],
            },
            RoleConstraint {
                role: vec!["Unrelated".into()],
                inputs: vec![role_arg(&mut machine, unrelated_var)],
                associated: Vec::new(),
            },
        ];

        let roles = compact_reachable_role_constraints(&machine, &seed, &constraints);

        assert_eq!(roles.len(), 2);
        assert_eq!(roles[0].role, vec!["First".to_string()]);
        assert_eq!(roles[1].role, vec!["Second".to_string()]);
        assert!(
            roles[0].associated[0]
                .value
                .lower
                .vars
                .iter()
                .any(|var| var.var == output_var)
        );
    }

    #[test]
    fn polar_elimination_removes_one_sided_vars() {
        let machine = ConstraintMachine::new();
        let mut root = CompactRoot {
            root: CompactType::from_fun(CompactFun {
                arg: CompactType::from_var(CompactVar::plain(TypeVar(1))),
                arg_eff: CompactType::default(),
                ret_eff: CompactType::default(),
                ret: CompactType::from_var(CompactVar::plain(TypeVar(2))),
            }),
            rec_vars: Vec::new(),
        };

        let substitutions = eliminate_polar_variables(&machine, TypeLevel::root(), &mut root);

        let fun = &root.root.funs[0];
        assert!(fun.arg.vars.is_empty());
        assert!(fun.ret.vars.is_empty());
        assert_eq!(
            substitutions,
            vec![
                CompactVarSubstitution {
                    source: TypeVar(1),
                    target: None
                },
                CompactVarSubstitution {
                    source: TypeVar(2),
                    target: None
                }
            ]
        );
    }

    #[test]
    fn polar_elimination_keeps_low_level_one_sided_vars() {
        let mut machine = ConstraintMachine::new();
        let outer = TypeVar(1);
        let inner = TypeVar(2);
        machine.register_type_var(outer, TypeLevel::root());
        machine.register_type_var(inner, TypeLevel::root().child());
        let mut root = CompactRoot {
            root: CompactType {
                vars: vec![CompactVar::plain(outer), CompactVar::plain(inner)],
                ..CompactType::default()
            },
            rec_vars: Vec::new(),
        };

        let substitutions =
            eliminate_polar_variables(&machine, TypeLevel::root().child(), &mut root);

        assert_eq!(root.root.vars, vec![CompactVar::plain(outer)]);
        assert_eq!(
            substitutions,
            vec![CompactVarSubstitution {
                source: inner,
                target: None
            }]
        );
    }

    #[test]
    fn polar_elimination_keeps_interval_center_as_bipolar() {
        let machine = ConstraintMachine::new();
        let center = TypeVar(1);
        let one_sided = TypeVar(2);
        let mut root = CompactRoot {
            root: CompactType::default(),
            rec_vars: vec![CompactRecursiveVar {
                var: center,
                bounds: CompactBounds::Interval {
                    self_var: center,
                    lower: CompactType::from_var(CompactVar::plain(one_sided)),
                    upper: CompactType::default(),
                },
            }],
        };

        let substitutions = eliminate_polar_variables(&machine, TypeLevel::root(), &mut root);

        assert_eq!(root.rec_vars[0].var, center);
        assert!(matches!(
            &root.rec_vars[0].bounds,
            CompactBounds::Interval {
                self_var,
                lower,
                ..
            } if *self_var == center && lower.vars.is_empty()
        ));
        assert_eq!(
            substitutions,
            vec![CompactVarSubstitution {
                source: one_sided,
                target: None
            }]
        );
    }

    #[test]
    fn co_occurrence_unifies_indistinguishable_vars() {
        let machine = ConstraintMachine::new();
        let mut root = CompactRoot {
            root: CompactType {
                vars: vec![
                    CompactVar::plain(TypeVar(10)),
                    CompactVar::plain(TypeVar(11)),
                ],
                ..CompactType::default()
            },
            rec_vars: Vec::new(),
        };

        let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

        assert_eq!(root.root.vars.len(), 1);
        assert_eq!(root.root.vars[0].var, TypeVar(10));
        assert_eq!(
            substitutions,
            vec![CompactVarSubstitution {
                source: TypeVar(11),
                target: Some(TypeVar(10))
            }]
        );
    }

    #[test]
    fn co_occurrence_links_interval_center_with_lower_and_upper() {
        let machine = ConstraintMachine::new();
        let center = TypeVar(1);
        let lower_var = TypeVar(2);
        let upper_var = TypeVar(3);
        let mut root = CompactRoot {
            root: CompactType::default(),
            rec_vars: vec![CompactRecursiveVar {
                var: center,
                bounds: CompactBounds::Interval {
                    self_var: center,
                    lower: CompactType::from_var(CompactVar::plain(lower_var)),
                    upper: CompactType::from_var(CompactVar::plain(upper_var)),
                },
            }],
        };

        let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

        assert_eq!(
            substitutions,
            vec![
                CompactVarSubstitution {
                    source: lower_var,
                    target: Some(center)
                },
                CompactVarSubstitution {
                    source: upper_var,
                    target: Some(center)
                }
            ]
        );
        assert!(matches!(
            &root.rec_vars[0].bounds,
            CompactBounds::Interval {
                self_var,
                lower,
                upper,
            } if *self_var == center
                && lower.vars == vec![CompactVar::plain(center)]
                && upper.vars == vec![CompactVar::plain(center)]
        ));
    }

    #[test]
    fn co_occurrence_ignores_secondary_marker_for_representative() {
        let machine = ConstraintMachine::new();
        let mut root = CompactRoot {
            root: CompactType {
                vars: vec![
                    CompactVar::plain(TypeVar(10)).secondary(),
                    CompactVar::plain(TypeVar(11)),
                ],
                ..CompactType::default()
            },
            rec_vars: Vec::new(),
        };

        let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

        assert_eq!(root.root.vars.len(), 1);
        assert_eq!(root.root.vars[0].var, TypeVar(10));
        assert_eq!(root.root.vars[0].origin, CompactVarOrigin::Secondary);
        assert_eq!(
            substitutions,
            vec![CompactVarSubstitution {
                source: TypeVar(11),
                target: Some(TypeVar(10))
            }]
        );
    }

    #[test]
    fn co_occurrence_ignores_weight_and_unions_ids_after_substitution() {
        let machine = ConstraintMachine::new();
        let first = SubtractId(1);
        let second = SubtractId(2);
        let mut root = CompactRoot {
            root: CompactType {
                vars: vec![
                    CompactVar::covariant(TypeVar(10), ConstraintWeight::from_ids([first])),
                    CompactVar::covariant(TypeVar(11), ConstraintWeight::from_ids([second])),
                ],
                ..CompactType::default()
            },
            rec_vars: Vec::new(),
        };

        let substitutions = coalesce_by_co_occurrence(&machine, TypeLevel::root(), &mut root);

        assert_eq!(root.root.vars.len(), 1);
        assert_eq!(root.root.vars[0].var, TypeVar(10));
        assert!(root.root.vars[0].weight.contains(first));
        assert!(root.root.vars[0].weight.contains(second));
        assert_eq!(
            substitutions,
            vec![CompactVarSubstitution {
                source: TypeVar(11),
                target: Some(TypeVar(10))
            }]
        );
    }

    #[test]
    fn co_occurrence_does_not_merge_low_level_vars_together() {
        let mut machine = ConstraintMachine::new();
        let first_outer = TypeVar(1);
        let second_outer = TypeVar(2);
        machine.register_type_var(first_outer, TypeLevel::root());
        machine.register_type_var(second_outer, TypeLevel::root());
        let mut root = CompactRoot {
            root: CompactType {
                vars: vec![
                    CompactVar::plain(first_outer),
                    CompactVar::plain(second_outer),
                ],
                ..CompactType::default()
            },
            rec_vars: Vec::new(),
        };

        let substitutions =
            coalesce_by_co_occurrence(&machine, TypeLevel::root().child(), &mut root);

        assert_eq!(
            root.root.vars,
            vec![
                CompactVar::plain(first_outer),
                CompactVar::plain(second_outer)
            ]
        );
        assert!(substitutions.is_empty());
    }

    #[test]
    fn co_occurrence_rewrites_high_level_var_to_low_level_representative() {
        let mut machine = ConstraintMachine::new();
        let outer = TypeVar(1);
        let inner = TypeVar(2);
        machine.register_type_var(outer, TypeLevel::root());
        machine.register_type_var(inner, TypeLevel::root().child());
        let mut root = CompactRoot {
            root: CompactType {
                vars: vec![CompactVar::plain(outer), CompactVar::plain(inner)],
                ..CompactType::default()
            },
            rec_vars: Vec::new(),
        };

        let substitutions =
            coalesce_by_co_occurrence(&machine, TypeLevel::root().child(), &mut root);

        assert_eq!(root.root.vars, vec![CompactVar::plain(outer)]);
        assert_eq!(
            substitutions,
            vec![CompactVarSubstitution {
                source: inner,
                target: Some(outer)
            }]
        );
    }

    #[test]
    fn sandwich_lifts_list_and_reuses_common_interval_var() {
        let machine = ConstraintMachine::new();
        let center = TypeVar(1);
        let payload = TypeVar(2);
        let mut root = CompactRoot {
            root: CompactType::from_con(CompactCon {
                path: vec!["box".into()],
                args: vec![CompactBounds::Interval {
                    self_var: center,
                    lower: list_with_payload_bound(
                        center,
                        CompactBounds::Interval {
                            self_var: TypeVar(20),
                            lower: CompactType::from_var(CompactVar::plain(payload)),
                            upper: CompactType::default(),
                        },
                    ),
                    upper: list_with_payload_bound(
                        center,
                        CompactBounds::Interval {
                            self_var: TypeVar(21),
                            lower: CompactType::default(),
                            upper: CompactType::from_var(CompactVar::plain(payload)),
                        },
                    ),
                }],
            }),
            rec_vars: Vec::new(),
        };

        let sandwiches = sandwich_compact_root(&machine, TypeLevel::root(), &mut root);

        let CompactBounds::Con { path, args } = &root.root.cons[0].args[0] else {
            panic!("box payload should be lifted to list");
        };
        assert!(compact_path_is(path, "list"));
        let CompactBounds::Interval { self_var, .. } = &args[0] else {
            panic!("list payload should remain interval");
        };
        assert_eq!(*self_var, payload);
        assert_eq!(
            sandwiches,
            vec![CompactSandwich {
                var: center,
                kind: CompactSandwichKind::Con {
                    path: vec!["list".into()],
                    arity: 1
                }
            }]
        );
    }

    #[test]
    fn sandwich_lifts_list_and_freshens_interval_var_without_common_var() {
        let machine = ConstraintMachine::new();
        let center = TypeVar(1);
        let lower_payload = TypeVar(2);
        let upper_payload = TypeVar(3);
        let mut root = CompactRoot {
            root: CompactType::from_con(CompactCon {
                path: vec!["box".into()],
                args: vec![CompactBounds::Interval {
                    self_var: center,
                    lower: list_with_payload_bound(
                        center,
                        CompactBounds::Interval {
                            self_var: TypeVar(4),
                            lower: CompactType::from_var(CompactVar::plain(lower_payload)),
                            upper: CompactType::default(),
                        },
                    ),
                    upper: list_with_payload_bound(
                        center,
                        CompactBounds::Interval {
                            self_var: TypeVar(5),
                            lower: CompactType::default(),
                            upper: CompactType::from_var(CompactVar::plain(upper_payload)),
                        },
                    ),
                }],
            }),
            rec_vars: Vec::new(),
        };

        let sandwiches = sandwich_compact_root(&machine, TypeLevel::root(), &mut root);

        let CompactBounds::Con { args, .. } = &root.root.cons[0].args[0] else {
            panic!("box payload should be lifted to list");
        };
        let CompactBounds::Interval { self_var, .. } = &args[0] else {
            panic!("list payload should remain interval");
        };
        assert_eq!(*self_var, TypeVar(6));
        assert_eq!(
            sandwiches,
            vec![CompactSandwich {
                var: center,
                kind: CompactSandwichKind::Con {
                    path: vec!["list".into()],
                    arity: 1
                }
            }]
        );
    }

    #[test]
    fn sandwich_does_not_lift_low_level_vars() {
        let mut machine = ConstraintMachine::new();
        let center = TypeVar(1);
        let payload = TypeVar(2);
        machine.register_type_var(center, TypeLevel::root());
        machine.register_type_var(payload, TypeLevel::root().child());
        let mut root = CompactRoot {
            root: CompactType::from_con(CompactCon {
                path: vec!["box".into()],
                args: vec![CompactBounds::Interval {
                    self_var: center,
                    lower: list_with_payload_bound(
                        center,
                        CompactBounds::Interval {
                            self_var: TypeVar(20),
                            lower: CompactType::from_var(CompactVar::plain(payload)),
                            upper: CompactType::default(),
                        },
                    ),
                    upper: list_with_payload_bound(
                        center,
                        CompactBounds::Interval {
                            self_var: TypeVar(21),
                            lower: CompactType::default(),
                            upper: CompactType::from_var(CompactVar::plain(payload)),
                        },
                    ),
                }],
            }),
            rec_vars: Vec::new(),
        };

        let sandwiches = sandwich_compact_root(&machine, TypeLevel::root().child(), &mut root);

        assert!(sandwiches.is_empty());
        assert!(matches!(
            &root.root.cons[0].args[0],
            CompactBounds::Interval { .. }
        ));
    }

    #[test]
    fn sandwich_does_not_lift_low_level_interval_through_high_level_common_var() {
        let mut machine = ConstraintMachine::new();
        let outer = TypeVar(1);
        let inner = TypeVar(2);
        let payload = TypeVar(3);
        machine.register_type_var(outer, TypeLevel::root());
        machine.register_type_var(inner, TypeLevel::root().child());
        machine.register_type_var(payload, TypeLevel::root().child());
        let mut root = CompactRoot {
            root: CompactType::from_con(CompactCon {
                path: vec!["box".into()],
                args: vec![CompactBounds::Interval {
                    self_var: outer,
                    lower: list_with_payload_bound(
                        inner,
                        CompactBounds::Interval {
                            self_var: TypeVar(20),
                            lower: CompactType::from_var(CompactVar::plain(payload)),
                            upper: CompactType::default(),
                        },
                    ),
                    upper: list_with_payload_bound(
                        inner,
                        CompactBounds::Interval {
                            self_var: TypeVar(21),
                            lower: CompactType::default(),
                            upper: CompactType::from_var(CompactVar::plain(payload)),
                        },
                    ),
                }],
            }),
            rec_vars: Vec::new(),
        };

        let sandwiches = sandwich_compact_root(&machine, TypeLevel::root().child(), &mut root);

        assert!(sandwiches.is_empty());
        assert!(matches!(
            &root.root.cons[0].args[0],
            CompactBounds::Interval { self_var, .. } if *self_var == outer
        ));
    }

    #[test]
    fn finalize_returns_pos_union_for_multiple_positive_parts() {
        let mut types = TypeArena::new();
        let ty = merge_compact_types(
            true,
            CompactType::from_var(CompactVar::plain(TypeVar(1))),
            CompactType::from_builtin(BuiltinType::Int),
        );

        let finalized = finalize_compact_type(&mut types, &ty);

        assert!(pos_contains_var(&types, finalized, TypeVar(1)));
        assert!(pos_contains_path(&types, finalized, "int"));
    }

    #[test]
    fn finalize_preserves_function_polarity() {
        let mut types = TypeArena::new();
        let ty = CompactType::from_fun(CompactFun {
            arg: CompactType::from_var(CompactVar::plain(TypeVar(1))),
            arg_eff: CompactType::never(),
            ret_eff: CompactType::from_var(CompactVar::plain(TypeVar(2))),
            ret: CompactType::from_var(CompactVar::plain(TypeVar(3))),
        });

        let finalized = finalize_compact_type(&mut types, &ty);

        let Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } = types.pos(finalized)
        else {
            panic!("expected finalized function");
        };
        assert!(matches!(types.neg(*arg), Neg::Var(var) if *var == TypeVar(1)));
        assert!(matches!(types.neg(*arg_eff), Neg::Bot));
        assert!(matches!(types.pos(*ret_eff), Pos::Var(var) if *var == TypeVar(2)));
        assert!(matches!(types.pos(*ret), Pos::Var(var) if *var == TypeVar(3)));
    }

    #[test]
    fn finalize_interval_bounds_to_neutral_bounds() {
        let mut types = TypeArena::new();
        let bounds = CompactBounds::Interval {
            self_var: TypeVar(7),
            lower: CompactType::from_builtin(BuiltinType::Unit),
            upper: CompactType::from_var(CompactVar::plain(TypeVar(8))),
        };

        let finalized = finalize_compact_bounds(&mut types, &bounds);

        let Neu::Bounds(lower, self_var, upper) = types.neu(finalized) else {
            panic!("expected neutral bounds");
        };
        assert_eq!(*self_var, TypeVar(7));
        assert!(pos_contains_path(&types, *lower, "unit"));
        assert!(matches!(types.neg(*upper), Neg::Var(var) if *var == TypeVar(8)));
    }

    #[test]
    fn finalize_lifted_compact_bounds_to_neutral_constructor() {
        let mut types = TypeArena::new();
        let bounds = CompactBounds::Con {
            path: vec!["list".into()],
            args: vec![CompactBounds::Interval {
                self_var: TypeVar(1),
                lower: CompactType::from_var(CompactVar::plain(TypeVar(1))),
                upper: CompactType::from_var(CompactVar::plain(TypeVar(1))),
            }],
        };

        let finalized = finalize_compact_bounds(&mut types, &bounds);

        let Neu::Con(path, args) = types.neu(finalized) else {
            panic!("expected neutral constructor");
        };
        assert!(compact_path_is(path, "list"));
        let Neu::Bounds(_, self_var, _) = types.neu(args[0]) else {
            panic!("expected list payload bounds");
        };
        assert_eq!(*self_var, TypeVar(1));
    }

    #[test]
    fn finalize_positive_row_flattens_tail_vars_into_row_items() {
        let mut types = TypeArena::new();
        let ty = CompactType {
            vars: vec![CompactVar::plain(TypeVar(1))],
            rows: vec![CompactRow {
                items: vec![CompactType::from_con(CompactCon {
                    path: vec!["io".into()],
                    args: Vec::new(),
                })],
                tail: Box::new(CompactType::default()),
            }],
            ..CompactType::default()
        };

        let finalized = finalize_compact_type(&mut types, &ty);

        let Pos::Row(items) = types.pos(finalized) else {
            panic!("expected positive row");
        };
        assert!(
            items
                .iter()
                .any(|item| { matches!(types.pos(*item), Pos::Var(var) if *var == TypeVar(1)) })
        );
        assert!(
            items
                .iter()
                .any(|item| pos_contains_path(&types, *item, "io"))
        );
    }

    #[test]
    fn finalize_root_preserves_recursive_side_table() {
        let mut types = TypeArena::new();
        let root = CompactRoot {
            root: CompactType::from_var(CompactVar::plain(TypeVar(1))),
            rec_vars: vec![CompactRecursiveVar {
                var: TypeVar(1),
                bounds: CompactBounds::Interval {
                    self_var: TypeVar(1),
                    lower: CompactType::from_con(CompactCon {
                        path: vec!["list".into()],
                        args: Vec::new(),
                    }),
                    upper: CompactType::default(),
                },
            }],
        };

        let finalized = finalize_compact_root(&mut types, &root);

        assert!(matches!(types.pos(finalized.root), Pos::Var(var) if *var == TypeVar(1)));
        assert_eq!(finalized.rec_vars.len(), 1);
        assert_eq!(finalized.rec_vars[0].var, TypeVar(1));
        let Neu::Bounds(lower, self_var, _) = types.neu(finalized.rec_vars[0].bounds) else {
            panic!("expected recursive bounds");
        };
        assert_eq!(*self_var, TypeVar(1));
        assert!(pos_contains_path(&types, *lower, "list"));
    }

    fn compact_row_contains_path(compact: &CompactType, path: &str) -> bool {
        compact.rows.iter().any(|row| {
            row.items
                .iter()
                .any(|item| compact_type_contains_path(item, path))
                || compact_type_contains_path(&row.tail, path)
        }) || compact_type_contains_path_without_rows(compact, path)
    }

    fn compact_type_contains_path(compact: &CompactType, path: &str) -> bool {
        compact_type_contains_path_without_rows(compact, path)
            || compact.rows.iter().any(|row| {
                row.items
                    .iter()
                    .any(|item| compact_type_contains_path(item, path))
                    || compact_type_contains_path(&row.tail, path)
            })
    }

    fn compact_type_contains_path_without_rows(compact: &CompactType, path: &str) -> bool {
        compact
            .cons
            .iter()
            .any(|con| compact_path_is(con.path.as_slice(), path))
            || compact
                .builtins
                .iter()
                .any(|builtin| builtin.surface_name() == path)
    }

    fn compact_path_is(actual: &[String], expected: &str) -> bool {
        actual.len() == 1 && actual[0] == expected
    }

    fn pos_contains_var(types: &TypeArena, id: PosId, expected: TypeVar) -> bool {
        match types.pos(id) {
            Pos::Var(var) => *var == expected,
            Pos::Row(items) => items
                .iter()
                .any(|item| pos_contains_var(types, *item, expected)),
            Pos::Union(left, right) => {
                pos_contains_var(types, *left, expected)
                    || pos_contains_var(types, *right, expected)
            }
            _ => false,
        }
    }

    fn pos_contains_path(types: &TypeArena, id: PosId, expected: &str) -> bool {
        match types.pos(id) {
            Pos::Con(path, _) => compact_path_is(path, expected),
            Pos::Row(items) => items
                .iter()
                .any(|item| pos_contains_path(types, *item, expected)),
            Pos::Union(left, right) => {
                pos_contains_path(types, *left, expected)
                    || pos_contains_path(types, *right, expected)
            }
            _ => false,
        }
    }

    fn list_with_payload_bound(center: TypeVar, payload: CompactBounds) -> CompactType {
        merge_compact_types(
            true,
            CompactType::from_var(CompactVar::plain(center)),
            CompactType::from_con(CompactCon {
                path: vec!["list".into()],
                args: vec![payload],
            }),
        )
    }

    fn role_arg(machine: &mut ConstraintMachine, var: TypeVar) -> RoleConstraintArg {
        RoleConstraintArg {
            lower: machine.alloc_pos(Pos::Var(var)),
            upper: machine.alloc_neg(Neg::Var(var)),
        }
    }
}
