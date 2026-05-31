use std::collections::{HashMap, HashSet};

use rustc_hash::{FxHashMap, FxHashSet};
use std::mem;

use std::time::Duration;

use crate::profile::ProfileClock as Instant;

use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

use crate::ids::{NegId, PosId, TypeVar};
use crate::scheme::OwnedSchemeInstance;
use crate::symbols::{Name, Path};
use crate::types::RecordField;
use crate::types::{Neg, Pos};

use crate::solve::{Infer, IntoNegId, IntoPosId};

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompactBounds {
    pub self_var: Option<TypeVar>,
    pub lower: CompactType,
    pub upper: CompactType,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompactTypeScheme {
    pub cty: CompactBounds,
    pub rec_vars: std::collections::HashMap<TypeVar, CompactBounds>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct CompactType {
    pub vars: std::collections::HashSet<TypeVar>,
    pub prims: std::collections::HashSet<Path>,
    pub cons: Vec<CompactCon>,
    pub funs: Vec<CompactFun>,
    pub records: Vec<CompactRecord>,
    pub record_spreads: Vec<CompactRecordSpread>,
    pub variants: Vec<CompactVariant>,
    pub tuples: Vec<Vec<CompactType>>,
    pub rows: Vec<CompactRow>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CompactProfile {
    pub compact_var_side: Duration,
    pub compact_pos_ref: Duration,
    pub compact_neg_ref: Duration,
    pub compact_reachable_rec_vars: Duration,
}

impl CompactProfile {
    pub fn merge(&mut self, other: &Self) {
        self.compact_var_side += other.compact_var_side;
        self.compact_pos_ref += other.compact_pos_ref;
        self.compact_neg_ref += other.compact_neg_ref;
        self.compact_reachable_rec_vars += other.compact_reachable_rec_vars;
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactCon {
    pub path: Path,
    pub args: Vec<CompactBounds>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactFun {
    pub arg: CompactType,
    pub arg_eff: CompactType,
    pub ret_eff: CompactType,
    pub ret: CompactType,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactRecord {
    pub fields: Vec<RecordField<CompactType>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactRecordSpread {
    pub fields: Vec<RecordField<CompactType>>,
    pub tail: Box<CompactType>,
    pub tail_wins: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactVariant {
    pub items: Vec<(Name, Vec<CompactType>)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactRow {
    pub items: Vec<CompactType>,
    pub tail: Box<CompactType>,
}

pub fn compact_type_var(infer: &Infer, tv: TypeVar) -> CompactTypeScheme {
    compact_type_var_profiled(infer, tv).0
}

pub fn compact_type_var_profiled(
    infer: &Infer,
    tv: TypeVar,
) -> (CompactTypeScheme, CompactProfile) {
    let mut ctx = CompactContext::new(infer);
    let scheme = ctx.compact_scheme(tv);
    (scheme, ctx.profile)
}

pub fn compact_type_vars_in_order(infer: &Infer, roots: &[TypeVar]) -> Vec<CompactTypeScheme> {
    compact_type_vars_in_order_profiled(infer, roots).0
}

pub fn compact_type_vars_in_order_profiled(
    infer: &Infer,
    roots: &[TypeVar],
) -> (Vec<CompactTypeScheme>, CompactProfile) {
    let mut ctx = CompactContext::new(infer);
    let schemes = roots
        .iter()
        .copied()
        .map(|tv| ctx.compact_scheme(tv))
        .collect();
    (schemes, ctx.profile)
}

pub(crate) fn compact_pos_expr<P: IntoPosId>(infer: &Infer, pos: P) -> CompactType {
    CompactContext::new(infer).compact_pos_id(pos.into_pos_id(infer), &ParentStack::new())
}

pub(crate) fn compact_neg_expr<N: IntoNegId>(infer: &Infer, neg: N) -> CompactType {
    CompactContext::new(infer).compact_neg_id(neg.into_neg_id(infer), &ParentStack::new())
}

pub(crate) fn merge_compact_bounds(
    positive: bool,
    lhs: CompactBounds,
    rhs: CompactBounds,
) -> CompactBounds {
    CompactBounds {
        self_var: lhs.self_var.or(rhs.self_var),
        lower: merge_compact_types(positive, lhs.lower, rhs.lower),
        upper: merge_compact_types(!positive, lhs.upper, rhs.upper),
    }
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

    let CompactType {
        vars: rhs_vars,
        prims: rhs_prims,
        cons: rhs_cons,
        funs: rhs_funs,
        records: rhs_records,
        record_spreads: rhs_record_spreads,
        variants: rhs_variants,
        tuples: rhs_tuples,
        rows: rhs_rows,
    } = rhs;
    let mut lhs = lhs;
    lhs.vars.extend(rhs_vars);
    lhs.prims.extend(rhs_prims);
    lhs.cons = merge_cons(positive, lhs.cons, rhs_cons);
    lhs.funs = merge_funs(positive, lhs.funs, rhs_funs);
    lhs.records = merge_records(positive, lhs.records, rhs_records);
    lhs.record_spreads = merge_unique_owned(lhs.record_spreads, rhs_record_spreads);
    lhs.variants = merge_variants(positive, lhs.variants, rhs_variants);
    lhs.tuples = merge_tuples(positive, lhs.tuples, rhs_tuples);
    lhs.rows = merge_rows(positive, lhs.rows, rhs_rows);
    lhs
}

pub(crate) fn coalesce_function_effect_residual(
    arg_eff: &mut CompactType,
    ret_eff: &mut CompactType,
) {
    if arg_eff.rows.is_empty() || arg_eff.vars.is_empty() || ret_eff.vars.is_empty() {
        return;
    }
    let keep_surface_residual = ret_eff.vars.len() > 1;
    let mut tail_vars = HashSet::new();
    collect_effect_row_tail_vars_with_items(arg_eff, &ret_eff.vars, &mut tail_vars);
    if tail_vars.is_empty() {
        promote_adjacent_effect_residual_vars(arg_eff, &ret_eff.vars);
        return;
    }
    let mut subst = arg_eff
        .vars
        .iter()
        .copied()
        .filter(|tv| ret_eff.vars.contains(tv))
        .filter_map(|surface| {
            tail_vars
                .iter()
                .copied()
                .find(|tail| *tail != surface)
                .map(|tail| (surface, tail))
        })
        .collect::<Vec<_>>();
    subst.sort_by_key(|(from, _)| from.0);
    subst.dedup_by_key(|(from, _)| *from);
    if subst.is_empty() {
        if !keep_surface_residual {
            for tail in tail_vars {
                arg_eff.vars.remove(&tail);
            }
        }
        return;
    }
    *arg_eff = subst_compact_type(arg_eff, &subst);
    *ret_eff = subst_compact_type(ret_eff, &subst);
    if !keep_surface_residual {
        for &(_, tail) in &subst {
            arg_eff.vars.remove(&tail);
        }
        for tail in tail_vars {
            arg_eff.vars.remove(&tail);
        }
    }
}

fn promote_adjacent_effect_residual_vars(
    ty: &mut CompactType,
    ret_vars: &HashSet<TypeVar>,
) -> HashSet<TypeVar> {
    let residual_vars = ty
        .vars
        .intersection(ret_vars)
        .copied()
        .collect::<HashSet<_>>();
    if residual_vars.is_empty() {
        return HashSet::new();
    }

    let mut promoted = HashSet::new();
    for row in &mut ty.rows {
        promote_adjacent_effect_residual_vars_in_row(row, &residual_vars, &mut promoted);
    }
    promoted
}

fn promote_adjacent_effect_residual_vars_in_row(
    row: &mut CompactRow,
    residual_vars: &HashSet<TypeVar>,
    promoted: &mut HashSet<TypeVar>,
) {
    if !row.items.is_empty() && is_empty_compact_type(&row.tail) {
        row.tail.vars.extend(residual_vars.iter().copied());
        promoted.extend(residual_vars.iter().copied());
        return;
    }

    for nested in &mut row.tail.rows {
        promote_adjacent_effect_residual_vars_in_row(nested, residual_vars, promoted);
    }
}

pub(crate) fn coalesce_function_effect_residuals_in_scheme(scheme: &mut CompactTypeScheme) {
    coalesce_function_effect_residuals_in_bounds(&mut scheme.cty);
    for bounds in scheme.rec_vars.values_mut() {
        coalesce_function_effect_residuals_in_bounds(bounds);
    }
}

pub(crate) fn coalesce_multi_function_effect_residuals_in_scheme(scheme: &mut CompactTypeScheme) {
    coalesce_multi_function_effect_residuals_in_bounds(&mut scheme.cty);
    for bounds in scheme.rec_vars.values_mut() {
        coalesce_multi_function_effect_residuals_in_bounds(bounds);
    }
}

pub(crate) fn coalesce_nested_tail_function_effect_residuals_in_scheme(
    scheme: &mut CompactTypeScheme,
) -> HashSet<TypeVar> {
    let mut exposed = HashSet::new();
    coalesce_nested_tail_function_effect_residuals_in_bounds(&mut scheme.cty, &mut exposed);
    for bounds in scheme.rec_vars.values_mut() {
        coalesce_nested_tail_function_effect_residuals_in_bounds(bounds, &mut exposed);
    }
    exposed
}

fn coalesce_function_effect_residuals_in_bounds(bounds: &mut CompactBounds) {
    coalesce_function_effect_residuals_in_type(&mut bounds.lower);
    coalesce_function_effect_residuals_in_type(&mut bounds.upper);
}

fn coalesce_function_effect_residuals_in_type(ty: &mut CompactType) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            coalesce_function_effect_residuals_in_bounds(arg);
        }
    }
    for fun in &mut ty.funs {
        coalesce_function_effect_residuals_in_type(&mut fun.arg);
        coalesce_function_effect_residuals_in_type(&mut fun.arg_eff);
        coalesce_function_effect_residuals_in_type(&mut fun.ret_eff);
        coalesce_function_effect_residuals_in_type(&mut fun.ret);
        coalesce_function_effect_residual(&mut fun.arg_eff, &mut fun.ret_eff);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            coalesce_function_effect_residuals_in_type(&mut field.value);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            coalesce_function_effect_residuals_in_type(&mut field.value);
        }
        coalesce_function_effect_residuals_in_type(&mut spread.tail);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                coalesce_function_effect_residuals_in_type(payload);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            coalesce_function_effect_residuals_in_type(item);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            coalesce_function_effect_residuals_in_type(item);
        }
        coalesce_function_effect_residuals_in_type(&mut row.tail);
    }
}

fn coalesce_multi_function_effect_residuals_in_bounds(bounds: &mut CompactBounds) {
    coalesce_multi_function_effect_residuals_in_type(&mut bounds.lower);
    coalesce_multi_function_effect_residuals_in_type(&mut bounds.upper);
}

fn coalesce_multi_function_effect_residuals_in_type(ty: &mut CompactType) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            coalesce_multi_function_effect_residuals_in_bounds(arg);
        }
    }
    for fun in &mut ty.funs {
        coalesce_multi_function_effect_residuals_in_type(&mut fun.arg);
        coalesce_multi_function_effect_residuals_in_type(&mut fun.arg_eff);
        coalesce_multi_function_effect_residuals_in_type(&mut fun.ret_eff);
        coalesce_multi_function_effect_residuals_in_type(&mut fun.ret);
        if fun.ret_eff.vars.len() > 1 {
            coalesce_function_effect_residual(&mut fun.arg_eff, &mut fun.ret_eff);
        }
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            coalesce_multi_function_effect_residuals_in_type(&mut field.value);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            coalesce_multi_function_effect_residuals_in_type(&mut field.value);
        }
        coalesce_multi_function_effect_residuals_in_type(&mut spread.tail);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                coalesce_multi_function_effect_residuals_in_type(payload);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            coalesce_multi_function_effect_residuals_in_type(item);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            coalesce_multi_function_effect_residuals_in_type(item);
        }
        coalesce_multi_function_effect_residuals_in_type(&mut row.tail);
    }
}

fn coalesce_nested_tail_function_effect_residuals_in_bounds(
    bounds: &mut CompactBounds,
    exposed: &mut HashSet<TypeVar>,
) {
    coalesce_nested_tail_function_effect_residuals_in_type(&mut bounds.lower, exposed);
    coalesce_nested_tail_function_effect_residuals_in_type(&mut bounds.upper, exposed);
}

fn coalesce_nested_tail_function_effect_residuals_in_type(
    ty: &mut CompactType,
    exposed: &mut HashSet<TypeVar>,
) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            coalesce_nested_tail_function_effect_residuals_in_bounds(arg, exposed);
        }
    }
    for fun in &mut ty.funs {
        coalesce_nested_tail_function_effect_residuals_in_type(&mut fun.arg, exposed);
        coalesce_nested_tail_function_effect_residuals_in_type(&mut fun.arg_eff, exposed);
        coalesce_nested_tail_function_effect_residuals_in_type(&mut fun.ret_eff, exposed);
        coalesce_nested_tail_function_effect_residuals_in_type(&mut fun.ret, exposed);
        if fun.ret_eff.vars.len() > 1 && has_nested_effect_row_tail(&fun.arg_eff) {
            let ret_vars = fun.ret_eff.vars.clone();
            let mut tail_vars = HashSet::new();
            collect_effect_row_tail_vars_with_items(&fun.arg_eff, &ret_vars, &mut tail_vars);
            coalesce_function_effect_residual(&mut fun.arg_eff, &mut fun.ret_eff);
            if let Some(representative) = tail_vars
                .into_iter()
                .filter(|tv| fun.ret_eff.vars.contains(tv))
                .min_by_key(|tv| tv.0)
            {
                exposed.insert(representative);
            }
        }
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            coalesce_nested_tail_function_effect_residuals_in_type(&mut field.value, exposed);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            coalesce_nested_tail_function_effect_residuals_in_type(&mut field.value, exposed);
        }
        coalesce_nested_tail_function_effect_residuals_in_type(&mut spread.tail, exposed);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                coalesce_nested_tail_function_effect_residuals_in_type(payload, exposed);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            coalesce_nested_tail_function_effect_residuals_in_type(item, exposed);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            coalesce_nested_tail_function_effect_residuals_in_type(item, exposed);
        }
        coalesce_nested_tail_function_effect_residuals_in_type(&mut row.tail, exposed);
    }
}

fn has_nested_effect_row_tail(ty: &CompactType) -> bool {
    ty.rows.iter().any(|row| {
        (!row.items.is_empty() && !row.tail.rows.is_empty())
            || has_nested_effect_row_tail(&row.tail)
    })
}

fn collect_effect_row_tail_vars_with_items(
    ty: &CompactType,
    ret_vars: &HashSet<TypeVar>,
    out: &mut HashSet<TypeVar>,
) {
    for row in &ty.rows {
        if !row.items.is_empty() {
            out.extend(
                row.tail
                    .vars
                    .iter()
                    .copied()
                    .filter(|tv| ret_vars.contains(tv)),
            );
        }
        collect_effect_row_tail_vars_with_items(&row.tail, ret_vars, out);
    }
}

struct CompactContext<'a> {
    infer: &'a Infer,
    lower_bounds: std::cell::Ref<'a, FxHashMap<TypeVar, SmallVec<[PosId; 2]>>>,
    upper_bounds: std::cell::Ref<'a, FxHashMap<TypeVar, SmallVec<[NegId; 2]>>>,
    compact_lower_instances:
        std::cell::Ref<'a, FxHashMap<TypeVar, SmallVec<[OwnedSchemeInstance; 2]>>>,
    in_progress: FxHashSet<(TypeVar, bool)>,
    recursive: FxHashSet<(TypeVar, bool)>,
    rec_vars: FxHashMap<TypeVar, CompactBounds>,
    cache: FxHashMap<(TypeVar, bool), CompactType>,
    profile: CompactProfile,
}

type ParentStack = SmallVec<[TypeVar; 8]>;

impl<'a> CompactContext<'a> {
    fn new(infer: &'a Infer) -> Self {
        Self {
            infer,
            lower_bounds: infer.lower.borrow(),
            upper_bounds: infer.upper.borrow(),
            compact_lower_instances: infer.compact_lower_instances.borrow(),
            in_progress: FxHashSet::default(),
            recursive: FxHashSet::default(),
            rec_vars: FxHashMap::default(),
            cache: FxHashMap::default(),
            profile: CompactProfile::default(),
        }
    }

    fn compact_var(&mut self, tv: TypeVar) -> CompactBounds {
        CompactBounds {
            self_var: Some(tv),
            lower: self.compact_var_side(tv, true, &ParentStack::new()),
            upper: self.compact_var_side(tv, false, &ParentStack::new()),
        }
    }

    fn compact_scheme(&mut self, tv: TypeVar) -> CompactTypeScheme {
        let cty = self.compact_var(tv);
        let reachable_start = Instant::now();
        let rec_vars = self.reachable_rec_vars(&cty);
        self.profile.compact_reachable_rec_vars += reachable_start.elapsed();
        CompactTypeScheme { rec_vars, cty }
    }

    fn reachable_rec_vars(
        &self,
        cty: &CompactBounds,
    ) -> std::collections::HashMap<TypeVar, CompactBounds> {
        let mut out = std::collections::HashMap::new();
        let mut stack = Vec::new();
        let mut seen = FxHashSet::default();

        if let Some(tv) = cty.self_var {
            stack.push(tv);
        }
        self.collect_referenced_rec_vars_in_bounds(cty, &mut stack);

        while let Some(tv) = stack.pop() {
            if !seen.insert(tv) {
                continue;
            }
            let Some(bounds) = self.rec_vars.get(&tv) else {
                continue;
            };
            self.collect_referenced_rec_vars_in_bounds(bounds, &mut stack);
            out.insert(tv, bounds.clone());
        }

        out
    }

    fn collect_referenced_rec_vars_in_bounds(
        &self,
        bounds: &CompactBounds,
        stack: &mut Vec<TypeVar>,
    ) {
        if let Some(tv) = bounds.self_var {
            if self.rec_vars.contains_key(&tv) {
                stack.push(tv);
            }
        }
        self.collect_referenced_rec_vars_in_type(&bounds.lower, stack);
        self.collect_referenced_rec_vars_in_type(&bounds.upper, stack);
    }

    fn collect_referenced_rec_vars_in_type(&self, ty: &CompactType, stack: &mut Vec<TypeVar>) {
        stack.extend(
            ty.vars
                .iter()
                .copied()
                .filter(|tv| self.rec_vars.contains_key(tv)),
        );
        for con in &ty.cons {
            for arg in &con.args {
                self.collect_referenced_rec_vars_in_bounds(arg, stack);
            }
        }
        for fun in &ty.funs {
            self.collect_referenced_rec_vars_in_type(&fun.arg, stack);
            self.collect_referenced_rec_vars_in_type(&fun.arg_eff, stack);
            self.collect_referenced_rec_vars_in_type(&fun.ret_eff, stack);
            self.collect_referenced_rec_vars_in_type(&fun.ret, stack);
        }
        for record in &ty.records {
            for field in &record.fields {
                self.collect_referenced_rec_vars_in_type(&field.value, stack);
            }
        }
        for spread in &ty.record_spreads {
            for field in &spread.fields {
                self.collect_referenced_rec_vars_in_type(&field.value, stack);
            }
            self.collect_referenced_rec_vars_in_type(&spread.tail, stack);
        }
        for variant in &ty.variants {
            for (_, payloads) in &variant.items {
                for payload in payloads {
                    self.collect_referenced_rec_vars_in_type(payload, stack);
                }
            }
        }
        for tuple in &ty.tuples {
            for item in tuple {
                self.collect_referenced_rec_vars_in_type(item, stack);
            }
        }
        for row in &ty.rows {
            for item in &row.items {
                self.collect_referenced_rec_vars_in_type(item, stack);
            }
            self.collect_referenced_rec_vars_in_type(&row.tail, stack);
        }
    }

    fn compact_var_side(
        &mut self,
        tv: TypeVar,
        positive: bool,
        parents: &ParentStack,
    ) -> CompactType {
        let start = Instant::now();
        let key = (tv, positive);
        if let Some(cached) = self.cache.get(&key) {
            let out = cached.clone();
            self.profile.compact_var_side += start.elapsed();
            return out;
        }
        if self.in_progress.contains(&key) {
            if parents.contains(&tv) {
                self.profile.compact_var_side += start.elapsed();
                return CompactType::default();
            }
            self.recursive.insert(key);
            self.profile.compact_var_side += start.elapsed();
            return CompactType::from_var(tv);
        }

        self.in_progress.insert(key);
        let mut next_parents = parents.clone();
        next_parents.push(tv);
        let bounds = self.compact_var_bounds(tv, positive, &next_parents);
        let mut bound = if positive {
            merge_compact_types(true, CompactType::from_var(tv), bounds)
        } else {
            merge_compact_types(false, CompactType::from_var(tv), bounds)
        };
        if let Some(alias_tv) = single_alias_var(&bound) {
            if alias_tv != tv && !next_parents.contains(&alias_tv) {
                bound = self.compact_var_side(alias_tv, positive, &next_parents);
            }
        }
        self.in_progress.remove(&key);

        if self.recursive.remove(&key) {
            let entry = self.rec_vars.entry(tv).or_insert_with(|| CompactBounds {
                self_var: Some(tv),
                lower: CompactType::default(),
                upper: CompactType::default(),
            });
            if positive {
                entry.lower = bound.clone();
            } else {
                entry.upper = bound.clone();
            }
            bound = CompactType::from_var(tv);
        }

        self.cache.insert(key, bound.clone());
        self.profile.compact_var_side += start.elapsed();
        bound
    }

    fn compact_var_bounds(
        &mut self,
        tv: TypeVar,
        positive: bool,
        parents: &ParentStack,
    ) -> CompactType {
        if positive {
            let regular = match self
                .lower_bounds
                .get(&tv)
                .map(|bounds| bounds.iter().copied().collect::<SmallVec<[PosId; 4]>>())
            {
                Some(bounds) => self.compact_pos_bounds_ref(bounds.as_slice(), parents),
                None => CompactType::default(),
            };
            let instantiated = match self.compact_lower_instances.get(&tv).map(|instances| {
                instances
                    .iter()
                    .cloned()
                    .collect::<SmallVec<[OwnedSchemeInstance; 2]>>()
            }) {
                Some(instances) => self.compact_instance_bounds_ref(instances.as_slice(), parents),
                None => CompactType::default(),
            };
            merge_compact_types(true, regular, instantiated)
        } else {
            match self
                .upper_bounds
                .get(&tv)
                .map(|bounds| bounds.iter().copied().collect::<SmallVec<[NegId; 4]>>())
            {
                Some(bounds) => self.compact_neg_bounds_ref(bounds.as_slice(), parents),
                None => CompactType::default(),
            }
        }
    }

    fn compact_pos_bounds_ref(&mut self, bounds: &[PosId], parents: &ParentStack) -> CompactType {
        let Some((first, rest)) = bounds.split_first() else {
            return CompactType::default();
        };

        let mut compact = self.compact_pos_id(*first, parents);
        for bound in rest {
            compact = merge_compact_types(true, compact, self.compact_pos_id(*bound, parents));
        }
        compact
    }

    fn compact_instance_bounds_ref(
        &mut self,
        instances: &[OwnedSchemeInstance],
        parents: &ParentStack,
    ) -> CompactType {
        let Some((first, rest)) = instances.split_first() else {
            return CompactType::default();
        };

        let mut compact = self.compact_pos_id(
            self.infer.materialize_compact_lower_instance(first),
            parents,
        );
        for instance in rest {
            compact = merge_compact_types(
                true,
                compact,
                self.compact_pos_id(
                    self.infer.materialize_compact_lower_instance(instance),
                    parents,
                ),
            );
        }
        compact
    }

    fn compact_neg_bounds_ref(&mut self, bounds: &[NegId], parents: &ParentStack) -> CompactType {
        let Some((first, rest)) = bounds.split_first() else {
            return CompactType::default();
        };

        let mut compact = self.compact_neg_id(*first, parents);
        for bound in rest {
            compact = merge_compact_types(false, compact, self.compact_neg_id(*bound, parents));
        }
        compact
    }

    fn compact_pos_id(&mut self, id: PosId, parents: &ParentStack) -> CompactType {
        let start = Instant::now();
        let out = match self.infer.arena.get_pos(id) {
            Pos::Bot => CompactType::default(),
            Pos::Var(tv) | Pos::Raw(tv) => self.compact_var_side(tv, true, parents),
            Pos::Atom(atom) => self.compact_effect_atom_ref(&atom),
            Pos::Forall(_, body) => self.compact_pos_id(body, &ParentStack::new()),
            Pos::Con(path, args) => CompactType::from_con(
                path,
                args.iter()
                    .map(|(p, n)| CompactBounds {
                        self_var: None,
                        lower: self.compact_pos_id(*p, &ParentStack::new()),
                        upper: self.compact_neg_id(*n, &ParentStack::new()),
                    })
                    .collect(),
            ),
            Pos::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactType::from_fun(CompactFun {
                arg: self.compact_neg_id(arg, &ParentStack::new()),
                arg_eff: self.compact_neg_id(arg_eff, &ParentStack::new()),
                ret_eff: self.compact_pos_id(ret_eff, &ParentStack::new()),
                ret: self.compact_pos_id(ret, &ParentStack::new()),
            }),
            Pos::Record(fields) => CompactType::from_record(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.compact_pos_id(field.value, &ParentStack::new()),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Pos::RecordTailSpread { fields, tail } => CompactType::from_record_spread(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.compact_pos_id(field.value, &ParentStack::new()),
                        optional: field.optional,
                    })
                    .collect(),
                self.compact_pos_id(tail, &ParentStack::new()),
                true,
            ),
            Pos::RecordHeadSpread { tail, fields } => CompactType::from_record_spread(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.compact_pos_id(field.value, &ParentStack::new()),
                        optional: field.optional,
                    })
                    .collect(),
                self.compact_pos_id(tail, &ParentStack::new()),
                false,
            ),
            Pos::PolyVariant(items) => CompactType::from_variant(
                items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.compact_pos_id(*payload, &ParentStack::new()))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Pos::Tuple(items) => CompactType::from_tuple(
                items
                    .iter()
                    .map(|item| self.compact_pos_id(*item, &ParentStack::new()))
                    .collect(),
            ),
            Pos::Row(items, tail) => CompactType::from_row_with_polarity(
                true,
                items
                    .iter()
                    .map(|item| self.compact_pos_id(*item, &ParentStack::new()))
                    .collect(),
                self.compact_pos_id(tail, &ParentStack::new()),
            ),
            Pos::Union(lhs, rhs) => merge_compact_types(
                true,
                self.compact_pos_id(lhs, parents),
                self.compact_pos_id(rhs, parents),
            ),
        };
        self.profile.compact_pos_ref += start.elapsed();
        out
    }

    fn compact_neg_id(&mut self, id: NegId, parents: &ParentStack) -> CompactType {
        let start = Instant::now();
        let out = match self.infer.arena.get_neg(id) {
            Neg::Top => CompactType::default(),
            Neg::Var(tv) => self.compact_var_side(tv, false, parents),
            Neg::Atom(atom) => self.compact_effect_atom_ref(&atom),
            Neg::Forall(_, body) => self.compact_neg_id(body, &ParentStack::new()),
            Neg::Con(path, args) => CompactType::from_con(
                path,
                args.iter()
                    .map(|(p, n)| CompactBounds {
                        self_var: None,
                        lower: self.compact_pos_id(*p, &ParentStack::new()),
                        upper: self.compact_neg_id(*n, &ParentStack::new()),
                    })
                    .collect(),
            ),
            Neg::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => CompactType::from_fun(CompactFun {
                arg: self.compact_pos_id(arg, &ParentStack::new()),
                arg_eff: self.compact_pos_id(arg_eff, &ParentStack::new()),
                ret_eff: self.compact_neg_id(ret_eff, &ParentStack::new()),
                ret: self.compact_neg_id(ret, &ParentStack::new()),
            }),
            Neg::Record(fields) => CompactType::from_record(
                fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.compact_neg_id(field.value, &ParentStack::new()),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Neg::PolyVariant(items) => CompactType::from_variant(
                items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.compact_neg_id(*payload, &ParentStack::new()))
                                .collect(),
                        )
                    })
                    .collect(),
            ),
            Neg::Tuple(items) => CompactType::from_tuple(
                items
                    .iter()
                    .map(|item| self.compact_neg_id(*item, &ParentStack::new()))
                    .collect(),
            ),
            Neg::Row(items, tail) => CompactType::from_row_with_polarity(
                false,
                items
                    .iter()
                    .map(|item| self.compact_neg_id(*item, &ParentStack::new()))
                    .collect(),
                self.compact_neg_id(tail, &ParentStack::new()),
            ),
            Neg::Intersection(lhs, rhs) => merge_compact_types(
                false,
                self.compact_neg_id(lhs, parents),
                self.compact_neg_id(rhs, parents),
            ),
        };
        self.profile.compact_neg_ref += start.elapsed();
        out
    }

    fn compact_effect_atom_ref(&mut self, atom: &crate::types::EffectAtom) -> CompactType {
        if atom.args.is_empty() {
            CompactType::from_prim(atom.path.clone())
        } else {
            CompactType::from_con(
                atom.path.clone(),
                atom.args
                    .iter()
                    .map(|(pos_tv, neg_tv)| CompactBounds {
                        self_var: None,
                        lower: CompactType::from_var(*pos_tv),
                        upper: CompactType::from_var(*neg_tv),
                    })
                    .collect(),
            )
        }
    }
}

pub(crate) fn subst_compact_type(ty: &CompactType, subst: &[(TypeVar, TypeVar)]) -> CompactType {
    CompactType {
        vars: ty
            .vars
            .iter()
            .copied()
            .map(|tv| subst_lookup_small(subst, tv))
            .collect(),
        prims: ty.prims.clone(),
        cons: ty
            .cons
            .iter()
            .map(|item| subst_compact_con(item, subst))
            .collect(),
        funs: ty
            .funs
            .iter()
            .map(|item| subst_compact_fun(item, subst))
            .collect(),
        records: ty
            .records
            .iter()
            .map(|item| subst_compact_record(item, subst))
            .collect(),
        record_spreads: ty
            .record_spreads
            .iter()
            .map(|item| subst_compact_record_spread(item, subst))
            .collect(),
        variants: ty
            .variants
            .iter()
            .map(|item| subst_compact_variant(item, subst))
            .collect(),
        tuples: ty
            .tuples
            .iter()
            .map(|tuple| {
                tuple
                    .iter()
                    .map(|item| subst_compact_type(item, subst))
                    .collect()
            })
            .collect(),
        rows: ty
            .rows
            .iter()
            .map(|item| subst_compact_row(item, subst))
            .collect(),
    }
}

pub(crate) fn subst_compact_bounds(
    bounds: &CompactBounds,
    subst: &[(TypeVar, TypeVar)],
) -> CompactBounds {
    CompactBounds {
        self_var: bounds.self_var.map(|tv| subst_lookup_small(subst, tv)),
        lower: subst_compact_type(&bounds.lower, subst),
        upper: subst_compact_type(&bounds.upper, subst),
    }
}

pub(crate) fn subst_compact_con(con: &CompactCon, subst: &[(TypeVar, TypeVar)]) -> CompactCon {
    CompactCon {
        path: con.path.clone(),
        args: con
            .args
            .iter()
            .map(|bounds| subst_compact_bounds(bounds, subst))
            .collect(),
    }
}

pub(crate) fn subst_compact_fun(fun: &CompactFun, subst: &[(TypeVar, TypeVar)]) -> CompactFun {
    CompactFun {
        arg: subst_compact_type(&fun.arg, subst),
        arg_eff: subst_compact_type(&fun.arg_eff, subst),
        ret_eff: subst_compact_type(&fun.ret_eff, subst),
        ret: subst_compact_type(&fun.ret, subst),
    }
}

pub(crate) fn subst_compact_record(
    record: &CompactRecord,
    subst: &[(TypeVar, TypeVar)],
) -> CompactRecord {
    CompactRecord {
        fields: record
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: subst_compact_type(&field.value, subst),
                optional: field.optional,
            })
            .collect(),
    }
}

pub(crate) fn subst_compact_record_spread(
    spread: &CompactRecordSpread,
    subst: &[(TypeVar, TypeVar)],
) -> CompactRecordSpread {
    CompactRecordSpread {
        fields: spread
            .fields
            .iter()
            .map(|field| RecordField {
                name: field.name.clone(),
                value: subst_compact_type(&field.value, subst),
                optional: field.optional,
            })
            .collect(),
        tail: Box::new(subst_compact_type(&spread.tail, subst)),
        tail_wins: spread.tail_wins,
    }
}

pub(crate) fn subst_compact_variant(
    variant: &CompactVariant,
    subst: &[(TypeVar, TypeVar)],
) -> CompactVariant {
    CompactVariant {
        items: variant
            .items
            .iter()
            .map(|(name, payloads)| {
                (
                    name.clone(),
                    payloads
                        .iter()
                        .map(|payload| subst_compact_type(payload, subst))
                        .collect(),
                )
            })
            .collect(),
    }
}

pub(crate) fn subst_compact_row(row: &CompactRow, subst: &[(TypeVar, TypeVar)]) -> CompactRow {
    CompactRow {
        items: row
            .items
            .iter()
            .map(|item| subst_compact_type(item, subst))
            .collect(),
        tail: Box::new(subst_compact_type(&row.tail, subst)),
    }
}

pub(crate) fn subst_lookup_small(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> TypeVar {
    subst
        .iter()
        .find_map(|(from, to)| (*from == tv).then_some(*to))
        .unwrap_or(tv)
}

pub(crate) fn normalize_compact_scheme_rows(scheme: &mut CompactTypeScheme) {
    normalize_compact_bounds_rows(&mut scheme.cty);
    for bounds in scheme.rec_vars.values_mut() {
        normalize_compact_bounds_rows(bounds);
    }
}

pub(crate) fn expose_positive_row_tails(scheme: &mut CompactTypeScheme) {
    expose_positive_row_tails_in_bounds(&mut scheme.cty);
    for bounds in scheme.rec_vars.values_mut() {
        expose_positive_row_tails_in_bounds(bounds);
    }
}

pub(crate) fn expose_negative_row_tail_vars(scheme: &mut CompactTypeScheme) {
    expose_negative_row_tail_vars_in_bounds(&mut scheme.cty);
    for bounds in scheme.rec_vars.values_mut() {
        expose_negative_row_tail_vars_in_bounds(bounds);
    }
}

fn normalize_compact_bounds_rows(bounds: &mut CompactBounds) {
    normalize_compact_type_rows(&mut bounds.lower, true);
    normalize_compact_type_rows(&mut bounds.upper, false);
}

fn normalize_compact_type_rows(ty: &mut CompactType, positive: bool) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            normalize_compact_bounds_rows(arg);
        }
    }
    for fun in &mut ty.funs {
        normalize_compact_type_rows(&mut fun.arg, !positive);
        normalize_compact_type_rows(&mut fun.arg_eff, !positive);
        normalize_compact_type_rows(&mut fun.ret_eff, positive);
        normalize_compact_type_rows(&mut fun.ret, positive);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            normalize_compact_type_rows(&mut field.value, positive);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            normalize_compact_type_rows(&mut field.value, positive);
        }
        normalize_compact_type_rows(&mut spread.tail, positive);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                normalize_compact_type_rows(payload, positive);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            normalize_compact_type_rows(item, positive);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            normalize_compact_type_rows(item, positive);
        }
        normalize_compact_type_rows(&mut row.tail, positive);
        let tail = std::mem::take(&mut *row.tail);
        match into_single_row(tail) {
            Ok(tail_row) => {
                row.items.extend(tail_row.items);
                row.tail = tail_row.tail;
            }
            Err(tail) => {
                *row.tail = tail;
            }
        }
        row.items = merge_same_effect_items(positive, std::mem::take(&mut row.items));
        absorb_tail_rows_already_present_in_outer_row(row);
    }
}

fn absorb_tail_rows_already_present_in_outer_row(row: &mut CompactRow) {
    if row.items.is_empty() || row.tail.rows.is_empty() {
        return;
    }

    let outer_tail_vars = row.tail.vars.clone();
    row.tail.rows.retain(|tail_row| {
        let tail_items_already_present = tail_row.items.iter().all(|item| row.items.contains(item));
        !(tail_items_already_present
            && row_tail_is_covered_by_outer_tail(&tail_row.tail, &outer_tail_vars))
    });
}

fn row_tail_is_covered_by_outer_tail(
    tail: &CompactType,
    outer_tail_vars: &std::collections::HashSet<TypeVar>,
) -> bool {
    is_empty_compact_type(tail)
        || compact_var_set(tail).is_some_and(|vars| vars.is_subset(outer_tail_vars))
}

fn expose_positive_row_tails_in_bounds(bounds: &mut CompactBounds) {
    expose_positive_row_tails_in_type(&mut bounds.lower, true, false);
    expose_positive_row_tails_in_type(&mut bounds.upper, false, false);
}

fn expose_positive_row_tails_in_type(
    ty: &mut CompactType,
    positive: bool,
    expose_current_row: bool,
) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            expose_positive_row_tails_in_bounds(arg);
        }
    }
    for fun in &mut ty.funs {
        expose_positive_row_tails_in_type(&mut fun.arg, !positive, false);
        expose_positive_row_tails_in_type(&mut fun.arg_eff, !positive, false);
        expose_positive_row_tails_in_type(&mut fun.ret_eff, positive, true);
        expose_positive_row_tails_in_type(&mut fun.ret, positive, false);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            expose_positive_row_tails_in_type(&mut field.value, positive, false);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            expose_positive_row_tails_in_type(&mut field.value, positive, false);
        }
        expose_positive_row_tails_in_type(&mut spread.tail, positive, false);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                expose_positive_row_tails_in_type(payload, positive, false);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            expose_positive_row_tails_in_type(item, positive, false);
        }
    }
    let mut exposed_tail_types = Vec::new();
    for row in &mut ty.rows {
        for item in &mut row.items {
            expose_positive_row_tails_in_type(item, positive, false);
        }
        expose_positive_row_tails_in_type(&mut row.tail, positive, false);
        if expose_current_row
            && positive
            && !row.items.is_empty()
            && !is_empty_compact_type(&row.tail)
        {
            exposed_tail_types.push(std::mem::take(&mut *row.tail));
        }
    }
    for tail in exposed_tail_types {
        let current = std::mem::take(ty);
        *ty = merge_compact_types(true, current, tail);
    }
}

fn expose_negative_row_tail_vars_in_bounds(bounds: &mut CompactBounds) {
    expose_negative_row_tail_vars_in_type(&mut bounds.lower, true, false);
    expose_negative_row_tail_vars_in_type(&mut bounds.upper, false, false);
}

fn expose_negative_row_tail_vars_in_type(
    ty: &mut CompactType,
    positive: bool,
    expose_current_row: bool,
) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            expose_negative_row_tail_vars_in_bounds(arg);
        }
    }
    for fun in &mut ty.funs {
        expose_negative_row_tail_vars_in_type(&mut fun.arg, !positive, false);
        expose_negative_row_tail_vars_in_type(&mut fun.arg_eff, !positive, false);
        expose_negative_row_tail_vars_in_type(&mut fun.ret_eff, positive, true);
        expose_negative_row_tail_vars_in_type(&mut fun.ret, positive, false);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            expose_negative_row_tail_vars_in_type(&mut field.value, positive, false);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            expose_negative_row_tail_vars_in_type(&mut field.value, positive, false);
        }
        expose_negative_row_tail_vars_in_type(&mut spread.tail, positive, false);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                expose_negative_row_tail_vars_in_type(payload, positive, false);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            expose_negative_row_tail_vars_in_type(item, positive, false);
        }
    }
    let mut tail_vars = Vec::new();
    for row in &mut ty.rows {
        for item in &mut row.items {
            expose_negative_row_tail_vars_in_type(item, positive, false);
        }
        expose_negative_row_tail_vars_in_type(&mut row.tail, positive, false);
        if expose_current_row && !positive && !row.items.is_empty() {
            tail_vars.extend(compact_var_set(&row.tail).into_iter().flatten());
        }
    }
    ty.vars.extend(tail_vars);
}

pub(crate) fn single_substituted_compact_var(
    ty: &CompactType,
    subst: &[(TypeVar, TypeVar)],
) -> Option<TypeVar> {
    if ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
        && ty.vars.len() == 1
    {
        ty.vars
            .iter()
            .copied()
            .next()
            .map(|tv| subst_lookup_small(subst, tv))
    } else {
        None
    }
}

fn single_alias_var(ty: &CompactType) -> Option<TypeVar> {
    (ty.vars.len() == 1
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty())
    .then(|| ty.vars.iter().copied().next())
    .flatten()
}

impl CompactType {
    fn from_var(tv: TypeVar) -> Self {
        let mut vars = std::collections::HashSet::new();
        vars.insert(tv);
        Self {
            vars,
            ..Self::default()
        }
    }

    fn from_prim(path: Path) -> Self {
        let mut prims = std::collections::HashSet::new();
        prims.insert(path);
        Self {
            prims,
            ..Self::default()
        }
    }

    fn from_con(path: Path, args: Vec<CompactBounds>) -> Self {
        Self {
            cons: vec![CompactCon { path, args }],
            ..Self::default()
        }
    }

    fn from_fun(fun: CompactFun) -> Self {
        Self {
            funs: vec![fun],
            ..Self::default()
        }
    }

    fn from_record(fields: Vec<RecordField<CompactType>>) -> Self {
        Self {
            records: vec![CompactRecord { fields }],
            ..Self::default()
        }
    }

    fn from_record_spread(
        fields: Vec<RecordField<CompactType>>,
        tail: CompactType,
        tail_wins: bool,
    ) -> Self {
        Self {
            record_spreads: vec![CompactRecordSpread {
                fields,
                tail: Box::new(tail),
                tail_wins,
            }],
            ..Self::default()
        }
    }

    fn from_variant(items: Vec<(Name, Vec<CompactType>)>) -> Self {
        Self {
            variants: vec![CompactVariant { items }],
            ..Self::default()
        }
    }

    fn from_tuple(items: Vec<CompactType>) -> Self {
        Self {
            tuples: vec![items],
            ..Self::default()
        }
    }

    fn from_row_with_polarity(positive: bool, items: Vec<CompactType>, tail: CompactType) -> Self {
        let (items, tail) = flatten_row_tail(positive, items, tail);
        Self {
            rows: vec![CompactRow {
                items,
                tail: Box::new(tail),
            }],
            ..Self::default()
        }
    }
}

fn flatten_row_tail(
    positive: bool,
    items: Vec<CompactType>,
    tail: CompactType,
) -> (Vec<CompactType>, CompactType) {
    match into_single_row(tail) {
        Ok(row) => {
            let items = items.into_iter().chain(row.items).collect();
            (merge_same_effect_items(positive, items), *row.tail)
        }
        Err(tail) => (merge_same_effect_items(positive, items), tail),
    }
}

fn into_single_row(ty: CompactType) -> Result<CompactRow, CompactType> {
    let CompactType {
        vars,
        prims,
        cons,
        funs,
        records,
        record_spreads,
        variants,
        tuples,
        mut rows,
    } = ty;
    if vars.is_empty()
        && prims.is_empty()
        && cons.is_empty()
        && funs.is_empty()
        && records.is_empty()
        && record_spreads.is_empty()
        && variants.is_empty()
        && tuples.is_empty()
        && rows.len() == 1
    {
        Ok(rows.remove(0))
    } else {
        Err(CompactType {
            vars,
            prims,
            cons,
            funs,
            records,
            record_spreads,
            variants,
            tuples,
            rows,
        })
    }
}

fn compact_var_set(ty: &CompactType) -> Option<std::collections::HashSet<TypeVar>> {
    (ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty())
    .then(|| ty.vars.clone())
}

fn merge_cons(positive: bool, lhs: Vec<CompactCon>, rhs: Vec<CompactCon>) -> Vec<CompactCon> {
    let mut out = lhs;
    for other in rhs {
        if let Some(existing) = out
            .iter_mut()
            .find(|con| con.path == other.path && con.args.len() == other.args.len())
        {
            existing.args = mem::take(&mut existing.args)
                .into_iter()
                .zip(other.args.into_iter())
                .map(|(lhs, rhs)| merge_compact_bounds(positive, lhs, rhs))
                .collect();
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

fn merge_funs(positive: bool, lhs: Vec<CompactFun>, rhs: Vec<CompactFun>) -> Vec<CompactFun> {
    let mut iter = lhs.into_iter().chain(rhs);
    let Some(mut acc) = iter.next() else {
        return vec![];
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
        return vec![];
    };
    for other in iter {
        let mut rhs_map = other
            .fields
            .into_iter()
            .map(|field| (field.name.clone(), field))
            .collect::<HashMap<_, _>>();
        let mut fields = Vec::new();

        for lhs_field in acc.fields {
            match rhs_map.remove(&lhs_field.name) {
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
            for rhs_field in rhs_map.into_values() {
                if !fields
                    .iter()
                    .any(|lhs_field| lhs_field.name == rhs_field.name)
                {
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
    lhs: Vec<CompactVariant>,
    rhs: Vec<CompactVariant>,
) -> Vec<CompactVariant> {
    let mut items = Vec::<(Name, Vec<CompactType>)>::new();
    for variant in lhs.into_iter().chain(rhs) {
        for (name, payloads) in variant.items {
            if let Some((_, existing_payloads)) =
                items.iter_mut().find(|(existing_name, existing_payloads)| {
                    *existing_name == name && existing_payloads.len() == payloads.len()
                })
            {
                *existing_payloads = mem::take(existing_payloads)
                    .into_iter()
                    .zip(payloads.into_iter())
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
        vec![CompactVariant { items }]
    }
}

fn merge_tuples(
    positive: bool,
    lhs: Vec<Vec<CompactType>>,
    rhs: Vec<Vec<CompactType>>,
) -> Vec<Vec<CompactType>> {
    let mut out = lhs;
    for other in rhs {
        if let Some(existing) = out.iter_mut().find(|tuple| tuple.len() == other.len()) {
            *existing = mem::take(existing)
                .into_iter()
                .zip(other.into_iter())
                .map(|(lhs, rhs)| merge_compact_types(positive, lhs, rhs))
                .collect();
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

fn merge_rows(positive: bool, lhs: Vec<CompactRow>, rhs: Vec<CompactRow>) -> Vec<CompactRow> {
    let mut out = lhs
        .into_iter()
        .map(|row| CompactRow {
            items: merge_same_effect_items(positive, row.items),
            tail: row.tail,
        })
        .collect::<Vec<_>>();
    for other in rhs {
        let other = CompactRow {
            items: merge_same_effect_items(positive, other.items),
            tail: other.tail,
        };
        if let Some(existing) = out.iter_mut().find(|row| row.tail == other.tail) {
            let items = mem::take(&mut existing.items)
                .into_iter()
                .chain(other.items.into_iter())
                .collect();
            existing.items = merge_same_effect_items(positive, items);
        } else if let Some(existing) = out.iter_mut().find(|row| row.items == other.items) {
            let merged_tail =
                merge_compact_types(positive, (*existing.tail).clone(), (*other.tail).clone());
            existing.tail = Box::new(merged_tail);
        } else if !out.contains(&other) {
            out.push(other);
        }
    }
    out
}

fn merge_same_effect_items(positive: bool, items: Vec<CompactType>) -> Vec<CompactType> {
    let mut out = Vec::new();
    let mut keyed = FxHashMap::default();
    for item in items {
        if let Some(key) = single_effect_item_key(&item) {
            if let Some(&index) = keyed.get(&key) {
                let existing = mem::take(&mut out[index]);
                out[index] = merge_compact_types(positive, existing, item);
                continue;
            }
            keyed.insert(key, out.len());
        }
        if !out.contains(&item) {
            out.push(item);
        }
    }
    out
}

fn single_effect_item_key(item: &CompactType) -> Option<(Path, usize)> {
    if !item.funs.is_empty()
        || !item.records.is_empty()
        || !item.record_spreads.is_empty()
        || !item.variants.is_empty()
        || !item.tuples.is_empty()
        || !item.rows.is_empty()
    {
        return None;
    }
    if item.prims.len() == 1 && item.cons.is_empty() {
        return item.prims.iter().next().cloned().map(|path| (path, 0));
    }
    if item.cons.len() == 1 && item.prims.is_empty() {
        let con = &item.cons[0];
        return Some((con.path.clone(), con.args.len()));
    }
    None
}

fn merge_unique_owned<T: PartialEq>(mut lhs: Vec<T>, rhs: Vec<T>) -> Vec<T> {
    for other in rhs {
        if !lhs.contains(&other) {
            lhs.push(other);
        }
    }
    lhs
}

fn is_empty_compact_type(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

#[cfg(test)]
mod tests {

    use super::{
        CompactBounds, CompactRow, CompactType, CompactTypeScheme,
        coalesce_function_effect_residual, compact_type_var, normalize_compact_scheme_rows,
    };
    use crate::fresh_type_var;
    use crate::solve::Infer;
    use crate::symbols::{Name, Path};
    use crate::types::{EffectAtom, Neg, Pos};

    #[test]
    fn compact_type_var_collects_function_and_prim_bounds() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        let arg_tv = fresh_type_var();
        let ret_tv = fresh_type_var();

        for current in [tv, arg_tv, ret_tv] {
            infer.register_level(current, 0);
        }

        infer.add_lower(
            tv,
            Pos::Fun {
                arg: infer.alloc_neg(Neg::Var(arg_tv)),
                arg_eff: infer.arena.top,
                ret_eff: infer.arena.bot,
                ret: infer.alloc_pos(Pos::Var(ret_tv)),
            },
        );
        infer.add_lower(
            tv,
            Pos::Con(
                Path {
                    segments: vec![Name("int".to_string())],
                },
                vec![],
            ),
        );

        let compact = compact_type_var(&infer, tv);
        assert_eq!(compact.cty.lower.cons.len(), 1);
        assert_eq!(compact.cty.lower.funs.len(), 1);
    }

    #[test]
    fn compact_type_var_recursively_expands_nested_function_bounds() {
        let infer = Infer::new();
        let root = fresh_type_var();
        let a = fresh_type_var();
        let b = fresh_type_var();
        let c = fresh_type_var();
        let d = fresh_type_var();
        let e = fresh_type_var();

        for current in [root, a, b, c, d, e] {
            infer.register_level(current, 0);
        }

        let int_path = prim_path("int");
        let str_path = prim_path("str");
        let bool_path = prim_path("bool");
        let unit_path = prim_path("unit");
        infer.add_upper(a, Neg::Con(int_path.clone(), vec![]));
        infer.add_upper(b, Neg::Con(str_path.clone(), vec![]));
        infer.add_upper(d, Neg::Con(bool_path.clone(), vec![]));
        infer.add_lower(e, Pos::Con(unit_path.clone(), vec![]));

        let c_fun = infer.alloc_pos(Pos::Fun {
            arg: infer.alloc_neg(Neg::Var(d)),
            arg_eff: infer.arena.top,
            ret_eff: infer.arena.bot,
            ret: infer.alloc_pos(Pos::Var(e)),
        });
        infer.add_lower(c, c_fun);

        let b_to_c = infer.alloc_pos(Pos::Fun {
            arg: infer.alloc_neg(Neg::Var(b)),
            arg_eff: infer.arena.top,
            ret_eff: infer.arena.bot,
            ret: infer.alloc_pos(Pos::Var(c)),
        });
        infer.add_lower(
            root,
            Pos::Fun {
                arg: infer.alloc_neg(Neg::Var(a)),
                arg_eff: infer.arena.top,
                ret_eff: infer.arena.bot,
                ret: b_to_c,
            },
        );

        let compact = compact_type_var(&infer, root);
        let a_to_rest = compact.cty.lower.funs.first().expect("a -> ...");
        assert!(compact_type_has_con(&a_to_rest.arg, &int_path));

        let b_to_rest = a_to_rest.ret.funs.first().expect("... -> b -> ...");
        assert!(compact_type_has_con(&b_to_rest.arg, &str_path));

        let d_to_e = b_to_rest.ret.funs.first().expect("... -> d -> e");
        assert!(compact_type_has_con(&d_to_e.arg, &bool_path));
        assert!(compact_type_has_con(&d_to_e.ret, &unit_path));
    }

    #[test]
    fn compact_type_var_merges_same_effect_items_in_row() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        let arg_a = fresh_type_var();
        let arg_b = fresh_type_var();
        for current in [tv, arg_a, arg_b] {
            infer.register_level(current, 0);
        }

        let path = Path {
            segments: vec![Name("var".to_string())],
        };
        infer.add_lower(
            tv,
            Pos::Row(
                vec![
                    infer.alloc_pos(Pos::Atom(EffectAtom {
                        path: path.clone(),
                        args: vec![(arg_a, arg_a)],
                    })),
                    infer.alloc_pos(Pos::Atom(EffectAtom {
                        path,
                        args: vec![(arg_b, arg_b)],
                    })),
                ],
                infer.arena.bot,
            ),
        );

        let compact = compact_type_var(&infer, tv);
        let row = &compact.cty.lower.rows[0];
        assert_eq!(row.items.len(), 1);
        assert_eq!(row.items[0].cons.len(), 1);
        assert_eq!(row.items[0].cons[0].args.len(), 1);
    }

    #[test]
    fn normalize_compact_scheme_rows_absorbs_tail_row_items_already_in_outer_row() {
        let tail = fresh_type_var();
        let io = CompactType {
            prims: std::collections::HashSet::from([prim_path("io")]),
            ..CompactType::default()
        };
        let tail_var = CompactType {
            vars: std::collections::HashSet::from([tail]),
            ..CompactType::default()
        };
        let mut scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    rows: vec![CompactRow {
                        items: vec![io.clone()],
                        tail: Box::new(CompactType {
                            vars: std::collections::HashSet::from([tail]),
                            rows: vec![CompactRow {
                                items: vec![io],
                                tail: Box::new(tail_var),
                            }],
                            ..CompactType::default()
                        }),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        normalize_compact_scheme_rows(&mut scheme);

        let row = &scheme.cty.lower.rows[0];
        assert_eq!(row.tail.vars, std::collections::HashSet::from([tail]));
        assert!(row.tail.rows.is_empty());
    }

    #[test]
    fn coalesce_function_effect_residual_exposes_adjacent_row_var_as_tail() {
        let residual = fresh_type_var();
        let io = CompactType {
            prims: std::collections::HashSet::from([prim_path("io")]),
            ..CompactType::default()
        };
        let mut arg_eff = CompactType {
            vars: std::collections::HashSet::from([residual]),
            rows: vec![CompactRow {
                items: vec![io],
                tail: Box::new(CompactType::default()),
            }],
            ..CompactType::default()
        };
        let mut ret_eff = CompactType {
            vars: std::collections::HashSet::from([residual]),
            ..CompactType::default()
        };

        coalesce_function_effect_residual(&mut arg_eff, &mut ret_eff);

        assert!(arg_eff.vars.contains(&residual));
        assert_eq!(
            arg_eff.rows[0].tail.vars,
            std::collections::HashSet::from([residual])
        );
        assert_eq!(ret_eff.vars, std::collections::HashSet::from([residual]));
    }

    #[test]
    fn coalesce_function_effect_residual_drops_single_surface_var_already_in_row_tail() {
        let residual = fresh_type_var();
        let io = CompactType {
            prims: std::collections::HashSet::from([prim_path("io")]),
            ..CompactType::default()
        };
        let mut arg_eff = CompactType {
            vars: std::collections::HashSet::from([residual]),
            rows: vec![CompactRow {
                items: vec![io],
                tail: Box::new(CompactType {
                    vars: std::collections::HashSet::from([residual]),
                    ..CompactType::default()
                }),
            }],
            ..CompactType::default()
        };
        let mut ret_eff = CompactType {
            vars: std::collections::HashSet::from([residual]),
            ..CompactType::default()
        };

        coalesce_function_effect_residual(&mut arg_eff, &mut ret_eff);

        assert!(arg_eff.vars.is_empty());
        assert_eq!(
            arg_eff.rows[0].tail.vars,
            std::collections::HashSet::from([residual])
        );
        assert_eq!(ret_eff.vars, std::collections::HashSet::from([residual]));
    }

    #[test]
    fn coalesce_function_effect_residual_keeps_surface_var_when_result_exposes_source_and_tail() {
        let source = fresh_type_var();
        let residual = fresh_type_var();
        let io = CompactType {
            prims: std::collections::HashSet::from([prim_path("io")]),
            ..CompactType::default()
        };
        let mut arg_eff = CompactType {
            vars: std::collections::HashSet::from([source]),
            rows: vec![CompactRow {
                items: vec![io],
                tail: Box::new(CompactType {
                    vars: std::collections::HashSet::from([residual]),
                    ..CompactType::default()
                }),
            }],
            ..CompactType::default()
        };
        let mut ret_eff = CompactType {
            vars: std::collections::HashSet::from([source, residual]),
            ..CompactType::default()
        };

        coalesce_function_effect_residual(&mut arg_eff, &mut ret_eff);

        assert_eq!(arg_eff.vars, std::collections::HashSet::from([residual]));
        assert_eq!(
            arg_eff.rows[0].tail.vars,
            std::collections::HashSet::from([residual])
        );
        assert_eq!(ret_eff.vars, std::collections::HashSet::from([residual]));
    }

    #[test]
    fn compact_type_var_merges_poly_variant_rows() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        let payload_tv = fresh_type_var();
        for current in [tv, payload_tv] {
            infer.register_level(current, 0);
        }

        infer.add_lower(
            tv,
            Pos::PolyVariant(vec![(
                Name("label".to_string()),
                vec![infer.alloc_pos(Pos::Var(payload_tv))],
            )]),
        );
        infer.add_lower(
            tv,
            Pos::PolyVariant(vec![(Name("disabled".to_string()), Vec::new())]),
        );

        let compact = compact_type_var(&infer, tv);
        assert_eq!(compact.cty.lower.variants.len(), 1);
        assert_eq!(compact.cty.lower.variants[0].items.len(), 2);
        let rendered = crate::display::format::format_coalesced_scheme(&compact);
        assert!(rendered.contains(":{label β, disabled}"), "{rendered}");
        assert!(!rendered.contains(" & :{disabled}"), "{rendered}");
    }

    #[test]
    fn compact_type_var_merges_poly_variant_upper_rows() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        let payload_tv = fresh_type_var();
        for current in [tv, payload_tv] {
            infer.register_level(current, 0);
        }

        infer.add_upper(
            tv,
            Neg::PolyVariant(vec![(
                Name("label".to_string()),
                vec![infer.alloc_neg(Neg::Var(payload_tv))],
            )]),
        );
        infer.add_upper(
            tv,
            Neg::PolyVariant(vec![(Name("disabled".to_string()), Vec::new())]),
        );

        let compact = compact_type_var(&infer, tv);
        assert_eq!(compact.cty.upper.variants.len(), 1);
        assert_eq!(compact.cty.upper.variants[0].items.len(), 2);
    }

    #[test]
    fn compact_type_var_ignores_spurious_self_cycle() {
        let infer = Infer::new();
        let tv = fresh_type_var();
        infer.register_level(tv, 0);
        infer.add_lower(tv, Pos::Var(tv));

        let compact = compact_type_var(&infer, tv);
        assert!(!compact.rec_vars.contains_key(&tv));
    }

    fn prim_path(name: &str) -> Path {
        Path {
            segments: vec![Name(name.to_string())],
        }
    }

    fn compact_type_has_con(ty: &super::CompactType, path: &Path) -> bool {
        ty.cons.iter().any(|con| &con.path == path)
    }
}
