use std::collections::{HashMap, HashSet};
use std::mem;

use crate::ids::{TypeVar, fresh_type_var};
use crate::lower::ctx::LowerCtx;
use crate::simplify::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRecordSpread, CompactRow,
    CompactType, CompactTypeScheme, CompactVariant, coalesce_function_effect_residual,
    compact_type_var, normalize_compact_scheme_rows,
};
use crate::solve::Infer;
use crate::symbols::{Name, Path};
use crate::types::RecordField;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Var(TypeVar),
    Prim(Path),
    Con(Path, Vec<CompactBounds>),
    Fun {
        arg: Box<Type>,
        arg_eff: Box<Type>,
        ret_eff: Box<Type>,
        ret: Box<Type>,
    },
    Record(Vec<RecordField<Type>>),
    RecordTailSpread {
        fields: Vec<RecordField<Type>>,
        tail: Box<Type>,
    },
    RecordHeadSpread {
        tail: Box<Type>,
        fields: Vec<RecordField<Type>>,
    },
    Variant(Vec<(Name, Vec<Type>)>),
    Tuple(Vec<Type>),
    Row(Vec<Type>, Box<Type>),
    Union(Vec<Type>),
    Inter(Vec<Type>),
    Rec(TypeVar, Box<Type>),
    Bot,
    Top,
}

pub fn compact_scheme_to_type(scheme: &CompactTypeScheme) -> Type {
    compact_scheme_to_type_with_observed_vars(scheme, &HashSet::new())
}

pub(crate) fn compact_scheme_to_type_with_observed_vars(
    scheme: &CompactTypeScheme,
    observed_vars: &HashSet<TypeVar>,
) -> Type {
    let mut scheme = scheme.clone();
    normalize_compact_scheme_rows(&mut scheme);
    let mut ctx = CompactToTypeCtx::new(&scheme);
    let root = normalize_render_bounds(scheme.cty.clone());
    if let Some(fun) = coalesce_root_fun(&mut ctx, &root, true, observed_vars) {
        return simplify_root_type(fun);
    }
    if let Some(fun) =
        coalesce_lower_only_root_fun(&mut ctx, &root, !scheme.rec_vars.is_empty(), observed_vars)
    {
        return simplify_root_type(fun);
    }
    simplify_root_type(ctx.coalesce_type(&root.lower, true))
}

pub fn materialize_effect_args(infer: &Infer, scheme: &mut CompactTypeScheme) {
    let mut cache = HashMap::new();
    materialize_effect_args_in_bounds(infer, &mut scheme.cty, &mut cache);
    for bounds in scheme.rec_vars.values_mut() {
        materialize_effect_args_in_bounds(infer, bounds, &mut cache);
    }
}

fn materialize_effect_args_in_bounds(
    infer: &Infer,
    bounds: &mut CompactBounds,
    cache: &mut HashMap<(TypeVar, bool), Option<CompactType>>,
) {
    materialize_effect_args_in_type(infer, &mut bounds.lower, cache);
    materialize_effect_args_in_type(infer, &mut bounds.upper, cache);
}

fn materialize_effect_args_in_type(
    infer: &Infer,
    ty: &mut CompactType,
    cache: &mut HashMap<(TypeVar, bool), Option<CompactType>>,
) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            materialize_effect_args_in_bounds(infer, arg, cache);
        }
    }
    for fun in &mut ty.funs {
        materialize_effect_args_in_type(infer, &mut fun.arg, cache);
        materialize_effect_args_in_type(infer, &mut fun.arg_eff, cache);
        materialize_effect_args_in_type(infer, &mut fun.ret_eff, cache);
        materialize_effect_args_in_type(infer, &mut fun.ret, cache);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            materialize_effect_args_in_type(infer, &mut field.value, cache);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            materialize_effect_args_in_type(infer, &mut field.value, cache);
        }
        materialize_effect_args_in_type(infer, &mut spread.tail, cache);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                materialize_effect_args_in_type(infer, payload, cache);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            materialize_effect_args_in_type(infer, item, cache);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            materialize_effect_item_args(infer, item, cache);
        }
        materialize_effect_args_in_type(infer, &mut row.tail, cache);
    }
}

fn materialize_effect_item_args(
    infer: &Infer,
    item: &mut CompactType,
    cache: &mut HashMap<(TypeVar, bool), Option<CompactType>>,
) {
    if !item.vars.is_empty()
        || !item.prims.is_empty()
        || item.cons.len() != 1
        || !item.funs.is_empty()
        || !item.records.is_empty()
        || !item.record_spreads.is_empty()
        || !item.variants.is_empty()
        || !item.tuples.is_empty()
        || !item.rows.is_empty()
    {
        materialize_effect_args_in_type(infer, item, cache);
        return;
    }
    let con = &mut item.cons[0];
    for arg in &mut con.args {
        let lower_tv = single_compact_var(&arg.lower);
        let upper_tv = single_compact_var(&arg.upper);
        let Some((lower_tv, upper_tv)) = lower_tv.zip(upper_tv) else {
            materialize_effect_args_in_bounds(infer, arg, cache);
            continue;
        };
        let lower = materialize_effect_arg_side(infer, lower_tv, true, cache);
        let upper = materialize_effect_arg_side(infer, upper_tv, false, cache);
        match (lower, upper) {
            (Some(lower), Some(upper)) if lower == upper => {
                arg.lower = lower;
                arg.upper = upper;
            }
            _ => materialize_effect_args_in_bounds(infer, arg, cache),
        }
    }
}

fn materialize_effect_arg_side(
    infer: &Infer,
    tv: TypeVar,
    positive: bool,
    cache: &mut HashMap<(TypeVar, bool), Option<CompactType>>,
) -> Option<CompactType> {
    let key = (tv, positive);
    if let Some(cached) = cache.get(&key) {
        return cached.clone();
    }
    cache.insert(key, None);
    let scheme = compact_type_var(infer, tv);
    let ty = if positive {
        scheme.cty.lower
    } else {
        scheme.cty.upper
    };
    let projected = compact_type_data_effect_arg_projection(ty);
    cache.insert(key, projected.clone());
    projected
}

fn single_compact_var(ty: &CompactType) -> Option<TypeVar> {
    if ty.vars.len() == 1
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        ty.vars.iter().next().copied()
    } else {
        None
    }
}

fn compact_type_data_effect_arg_projection(mut ty: CompactType) -> Option<CompactType> {
    if !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.rows.is_empty()
    {
        return None;
    }
    let has_data_shape = !ty.prims.is_empty() || !ty.cons.is_empty() || !ty.tuples.is_empty();
    if !has_data_shape {
        return None;
    }
    ty.vars.clear();
    for con in &mut ty.cons {
        for arg in &mut con.args {
            arg.lower = compact_type_data_effect_arg_projection(mem::take(&mut arg.lower))?;
            arg.upper = compact_type_data_effect_arg_projection(mem::take(&mut arg.upper))?;
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            *item = compact_type_data_effect_arg_projection(mem::take(item))?;
        }
    }
    Some(ty)
}

pub fn compact_side_to_type(
    rec_vars: &std::collections::HashMap<TypeVar, CompactBounds>,
    ty: &CompactType,
    positive: bool,
) -> Type {
    let scheme = CompactTypeScheme {
        cty: CompactBounds::default(),
        rec_vars: rec_vars.clone(),
    };
    let mut ctx = CompactToTypeCtx::new(&scheme);
    simplify_type(ctx.coalesce_type(ty, positive))
}

pub fn format_type(ty: &Type) -> String {
    let mut namer = VarNamer::default();
    format_type_with_namer(ty, &mut namer)
}

pub fn format_type_in_scope(ty: &Type, scope: &LowerCtx) -> String {
    let mut namer = VarNamer::with_scope(scope);
    format_type_with_namer(ty, &mut namer)
}

pub(crate) fn format_type_with_namer(ty: &Type, namer: &mut VarNamer<'_>) -> String {
    format_type_inner(ty, namer, false)
}

pub fn format_coalesced_scheme(scheme: &CompactTypeScheme) -> String {
    format_type(&compact_scheme_to_type(scheme))
}

pub fn format_coalesced_scheme_in_scope(scheme: &CompactTypeScheme, scope: &LowerCtx) -> String {
    format_type_in_scope(&compact_scheme_to_type(scheme), scope)
}

pub(crate) struct VarNamer<'scope> {
    names: HashMap<u32, String>,
    next: usize,
    scope: Option<&'scope LowerCtx>,
}

impl Default for VarNamer<'_> {
    fn default() -> Self {
        Self {
            names: HashMap::new(),
            next: 0,
            scope: None,
        }
    }
}

impl<'scope> VarNamer<'scope> {
    pub(crate) fn with_scope(scope: &'scope LowerCtx) -> Self {
        Self {
            names: HashMap::new(),
            next: 0,
            scope: Some(scope),
        }
    }

    fn name(&mut self, raw: u32) -> String {
        const GREEK: &[&str] = &[
            "α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ", "λ", "μ", "ν", "ξ", "ο", "π", "ρ",
            "σ", "τ", "υ", "φ", "χ", "ψ", "ω",
        ];

        if let Some(name) = self.names.get(&raw) {
            return name.clone();
        }

        let name = if self.next < GREEK.len() {
            GREEK[self.next].to_string()
        } else {
            format!("t{}", self.next)
        };
        self.next += 1;
        self.names.insert(raw, name.clone());
        name
    }

    pub(crate) fn render_path(&self, path: &Path) -> String {
        match self.scope {
            Some(ctx) => shortest_unique_type_path(ctx, path),
            None => path_string(path),
        }
    }
}

/// 与えられた完全修飾 Path に対して、現在のスコープから一意に同じ DefId へ
/// 解決できる最短サフィックスを返す。曖昧 or 解決不能なら完全修飾のままにする。
fn shortest_unique_type_path(ctx: &LowerCtx, full_path: &Path) -> String {
    if full_path.segments.is_empty() {
        return path_string(full_path);
    }

    let module = ctx.current_module;
    let target = ctx
        .resolve_path_type_candidates_via_snapshot(module, full_path)
        .into_iter()
        .next()
        .or_else(|| {
            crate::lower::builtin_types::canonical_builtin_type_path(full_path).and_then(
                |canonical| {
                    ctx.resolve_path_type_candidates_via_snapshot(module, &canonical)
                        .into_iter()
                        .next()
                },
            )
        });
    let Some(target) = target else {
        return path_string(full_path);
    };

    let total = full_path.segments.len();
    for k in 1..total {
        let suffix = Path {
            segments: full_path.segments[total - k..].to_vec(),
        };
        let candidates = ctx.resolve_path_type_candidates_via_snapshot(module, &suffix);
        if candidates.as_slice() == [target] {
            return path_string(&suffix);
        }
        if candidates.is_empty() && k == 1 {
            if let Some(canonical) =
                crate::lower::builtin_types::canonical_builtin_type_path(&suffix)
            {
                let canon_cands = ctx.resolve_path_type_candidates_via_snapshot(module, &canonical);
                if canon_cands.as_slice() == [target] {
                    return path_string(&suffix);
                }
            }
        }
    }
    path_string(full_path)
}

struct CompactToTypeCtx<'a> {
    scheme: &'a CompactTypeScheme,
    lower_witnesses: HashMap<TypeVar, CompactType>,
    cached_vars: HashMap<(TypeVar, bool), Type>,
    cached_types: HashMap<(String, bool), Type>,
    in_process_vars: HashMap<(TypeVar, bool), TypeVar>,
    recursive_var_hits: HashSet<(TypeVar, bool)>,
    in_process_types: HashMap<(String, bool), TypeVar>,
    recursive_type_hits: HashSet<(String, bool)>,
}

impl<'a> CompactToTypeCtx<'a> {
    fn new(scheme: &'a CompactTypeScheme) -> Self {
        Self {
            scheme,
            lower_witnesses: collect_lower_witnesses(scheme),
            cached_vars: HashMap::new(),
            cached_types: HashMap::new(),
            in_process_vars: HashMap::new(),
            recursive_var_hits: HashSet::new(),
            in_process_types: HashMap::new(),
            recursive_type_hits: HashSet::new(),
        }
    }

    fn coalesce_var(&mut self, tv: TypeVar, positive: bool) -> Type {
        let key = (tv, positive);
        if let Some(cached) = self.cached_vars.get(&key) {
            return cached.clone();
        }
        if let Some(rec_tv) = self.in_process_vars.get(&key) {
            self.recursive_var_hits.insert(key);
            return Type::Var(*rec_tv);
        }

        let Some(bounds) = self.scheme.rec_vars.get(&tv) else {
            return Type::Var(tv);
        };

        let rec_tv = fresh_type_var();
        self.in_process_vars.insert(key, rec_tv);
        let body = if positive {
            self.coalesce_type(&bounds.lower, true)
        } else {
            self.coalesce_type(&bounds.upper, false)
        };
        self.in_process_vars.remove(&key);

        let out = if self.recursive_var_hits.remove(&key) {
            Type::Rec(rec_tv, Box::new(body))
        } else {
            body
        };
        self.cached_vars.insert(key, out.clone());
        out
    }

    fn coalesce_type(&mut self, ty: &CompactType, positive: bool) -> Type {
        if should_hash_cons_type(ty) {
            let key = (compact_type_key(ty), positive);
            if let Some(cached) = self.cached_types.get(&key) {
                return cached.clone();
            }
            if let Some(rec_tv) = self.in_process_types.get(&key) {
                self.recursive_type_hits.insert(key.clone());
                return Type::Var(*rec_tv);
            }

            let rec_tv = fresh_type_var();
            self.in_process_types.insert(key.clone(), rec_tv);
            let body = self.coalesce_type_body(ty, positive);
            self.in_process_types.remove(&key);

            let out = if self.recursive_type_hits.remove(&key) {
                Type::Rec(rec_tv, Box::new(body))
            } else {
                body
            };
            self.cached_types.insert(key, out.clone());
            return out;
        }

        self.coalesce_type_body(ty, positive)
    }

    fn coalesce_type_body(&mut self, ty: &CompactType, positive: bool) -> Type {
        let mut parts = Vec::new();
        let ty = if positive {
            ty.clone()
        } else {
            self.drop_witnessed_negative_vars(ty)
        };

        let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
        vars.sort_by_key(|tv| tv.0);
        parts.extend(vars.into_iter().map(|tv| self.coalesce_var(tv, positive)));

        let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
        prims.sort_by(|a, b| path_string(a).cmp(&path_string(b)));
        parts.extend(prims.into_iter().map(Type::Prim));

        let mut cons = ty.cons.clone();
        cons.sort_by(|a, b| path_string(&a.path).cmp(&path_string(&b.path)));
        parts.extend(cons.into_iter().map(|con| Type::Con(con.path, con.args)));

        parts.extend(ty.funs.iter().map(|fun| self.coalesce_fun(fun, positive)));
        parts.extend(ty.records.iter().map(|record| {
            Type::Record(
                record
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.coalesce_type(&field.value, positive),
                        optional: field.optional,
                    })
                    .collect(),
            )
        }));
        parts.extend(ty.record_spreads.iter().map(|spread| {
            let fields = spread
                .fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: self.coalesce_type(&field.value, positive),
                    optional: field.optional,
                })
                .collect();
            let tail = Box::new(self.coalesce_type(&spread.tail, positive));
            if spread.tail_wins {
                Type::RecordTailSpread { fields, tail }
            } else {
                Type::RecordHeadSpread { tail, fields }
            }
        }));
        parts.extend(ty.variants.iter().map(|variant| {
            Type::Variant(
                variant
                    .items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.coalesce_type(payload, positive))
                                .collect(),
                        )
                    })
                    .collect(),
            )
        }));
        parts.extend(ty.tuples.iter().map(|tuple| {
            Type::Tuple(
                tuple
                    .iter()
                    .map(|item| self.coalesce_type(item, positive))
                    .collect(),
            )
        }));
        parts.extend(ty.rows.iter().map(|row| self.coalesce_row(row, positive)));

        combine_types(parts, positive)
    }

    fn coalesce_row(&mut self, row: &CompactRow, positive: bool) -> Type {
        let items = row
            .items
            .iter()
            .map(|item| self.coalesce_type(item, positive))
            .collect::<Vec<_>>();
        let tail = self.coalesce_type(&row.tail, positive);
        if positive {
            let mut parts = items;
            parts.push(tail);
            combine_types(parts, true)
        } else {
            Type::Row(items, Box::new(tail))
        }
    }

    fn coalesce_output_effect_type(&mut self, ty: &CompactType, positive: bool) -> Type {
        if has_effect_row_surface(ty) {
            self.coalesce_output_effect_surface_type(ty, positive)
        } else {
            self.coalesce_type(ty, positive)
        }
    }

    fn coalesce_output_effect_surface_type(&mut self, ty: &CompactType, positive: bool) -> Type {
        let ty = if positive {
            ty.clone()
        } else {
            self.drop_witnessed_negative_vars(ty)
        };
        let mut parts = Vec::new();

        let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
        vars.sort_by_key(|tv| tv.0);
        parts.extend(vars.into_iter().map(Type::Var));

        let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
        prims.sort_by(|a, b| path_string(a).cmp(&path_string(b)));
        parts.extend(prims.into_iter().map(Type::Prim));

        let mut cons = ty.cons.clone();
        cons.sort_by(|a, b| path_string(&a.path).cmp(&path_string(&b.path)));
        parts.extend(cons.into_iter().map(|con| Type::Con(con.path, con.args)));

        parts.extend(ty.funs.iter().map(|fun| self.coalesce_fun(fun, positive)));
        parts.extend(ty.records.iter().map(|record| {
            Type::Record(
                record
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: self.coalesce_type(&field.value, positive),
                        optional: field.optional,
                    })
                    .collect(),
            )
        }));
        parts.extend(ty.record_spreads.iter().map(|spread| {
            let fields = spread
                .fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: self.coalesce_type(&field.value, positive),
                    optional: field.optional,
                })
                .collect();
            let tail = Box::new(self.coalesce_type(&spread.tail, positive));
            if spread.tail_wins {
                Type::RecordTailSpread { fields, tail }
            } else {
                Type::RecordHeadSpread { tail, fields }
            }
        }));
        parts.extend(ty.variants.iter().map(|variant| {
            Type::Variant(
                variant
                    .items
                    .iter()
                    .map(|(name, payloads)| {
                        (
                            name.clone(),
                            payloads
                                .iter()
                                .map(|payload| self.coalesce_type(payload, positive))
                                .collect(),
                        )
                    })
                    .collect(),
            )
        }));
        parts.extend(ty.tuples.iter().map(|tuple| {
            Type::Tuple(
                tuple
                    .iter()
                    .map(|item| self.coalesce_type(item, positive))
                    .collect(),
            )
        }));
        parts.extend(
            ty.rows
                .iter()
                .map(|row| self.coalesce_output_effect_row(row, positive)),
        );

        combine_types(parts, positive)
    }

    fn coalesce_output_effect_row(&mut self, row: &CompactRow, positive: bool) -> Type {
        let items = row
            .items
            .iter()
            .map(|item| self.coalesce_type(item, positive))
            .collect::<Vec<_>>();
        let tail = self.coalesce_output_effect_tail(&row.tail, positive);
        if positive {
            let mut parts = items;
            parts.push(tail);
            combine_types(parts, true)
        } else {
            Type::Row(items, Box::new(tail))
        }
    }

    fn coalesce_output_effect_tail(&mut self, ty: &CompactType, positive: bool) -> Type {
        let ty = if positive {
            ty.clone()
        } else {
            self.drop_witnessed_negative_vars(ty)
        };
        let mut parts = Vec::new();

        let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
        vars.sort_by_key(|tv| tv.0);
        parts.extend(vars.into_iter().map(Type::Var));

        let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
        prims.sort_by(|a, b| path_string(a).cmp(&path_string(b)));
        parts.extend(prims.into_iter().map(Type::Prim));

        let mut cons = ty.cons.clone();
        cons.sort_by(|a, b| path_string(&a.path).cmp(&path_string(&b.path)));
        parts.extend(cons.into_iter().map(|con| Type::Con(con.path, con.args)));

        parts.extend(
            ty.rows
                .iter()
                .map(|row| self.coalesce_output_effect_row(row, positive)),
        );

        combine_types(parts, positive)
    }

    fn drop_witnessed_negative_vars(&self, ty: &CompactType) -> CompactType {
        let mut ty = ty.clone();
        let original = ty.clone();
        ty.vars.retain(|tv| {
            self.lower_witnesses
                .get(tv)
                .is_none_or(|witness| !compact_type_contains_witness(&original, witness))
        });
        ty
    }
}

impl CompactToTypeCtx<'_> {
    fn coalesce_fun(&mut self, fun: &CompactFun, positive: bool) -> Type {
        let mut fun = fun.clone();
        simplify_function_effect_residual_rows_for_render(&mut fun);
        if !positive {
            remove_row_tail_residual_vars_from_negative_ret_effect(&mut fun.ret_eff);
        }
        Type::Fun {
            arg: Box::new(self.coalesce_type(&fun.arg, !positive)),
            arg_eff: Box::new(self.coalesce_fun_effect_field(&fun.arg_eff, !positive)),
            ret_eff: Box::new(self.coalesce_fun_ret_effect_field(&fun.ret_eff, positive)),
            ret: Box::new(self.coalesce_type(&fun.ret, positive)),
        }
    }

    fn coalesce_fun_effect_field(&mut self, ty: &CompactType, positive: bool) -> Type {
        if is_empty_compact(ty) || is_explicit_empty_row_compact(ty) {
            Type::Bot
        } else {
            self.coalesce_type(ty, positive)
        }
    }

    fn coalesce_fun_ret_effect_field(&mut self, ty: &CompactType, positive: bool) -> Type {
        if is_empty_compact(ty) || is_explicit_empty_row_compact(ty) {
            Type::Bot
        } else {
            self.coalesce_output_effect_type(ty, positive)
        }
    }
}

fn remove_row_tail_residual_vars_from_negative_ret_effect(ty: &mut CompactType) {
    if ty.vars.is_empty() || ty.rows.is_empty() {
        return;
    }
    let tail_vars = ty
        .rows
        .iter()
        .filter(|row| !row.items.is_empty())
        .flat_map(|row| row.tail.vars.iter().copied())
        .collect::<HashSet<_>>();
    ty.vars.retain(|tv| !tail_vars.contains(tv));
}

fn coalesce_root_fun(
    ctx: &mut CompactToTypeCtx<'_>,
    bounds: &CompactBounds,
    normalize_fields: bool,
    observed_vars: &HashSet<TypeVar>,
) -> Option<Type> {
    let [lower_fun] = bounds.lower.funs.as_slice() else {
        return None;
    };
    let [upper_fun] = bounds.upper.funs.as_slice() else {
        return None;
    };
    if !root_non_fun_parts_empty(&bounds.lower) || !root_non_fun_parts_empty(&bounds.upper) {
        return None;
    }
    let mut lower_fun = lower_fun.clone();
    let upper_fun = upper_fun.clone();
    coalesce_function_effect_residual(&mut lower_fun.arg_eff, &mut lower_fun.ret_eff);
    simplify_function_effect_residual_rows_for_render(&mut lower_fun);

    if !normalize_fields {
        let arg = common_compact_type(&lower_fun.arg, &upper_fun.arg)
            .filter(|ty| !is_empty_compact(ty))
            .unwrap_or_else(|| lower_fun.arg.clone());
        let rendered_arg = if is_var_only_compact(&arg) {
            Type::Var(*arg.vars.iter().next().unwrap())
        } else {
            ctx.coalesce_type(&arg, false)
        };

        return Some(Type::Fun {
            arg: Box::new(rendered_arg),
            arg_eff: Box::new(ctx.coalesce_type(&lower_fun.arg_eff, false)),
            ret_eff: Box::new(ctx.coalesce_output_effect_type(&lower_fun.ret_eff, true)),
            ret: Box::new(ctx.coalesce_type(&lower_fun.ret, true)),
        });
    }

    let arg = coalesce_root_fun_field(
        ctx,
        &lower_fun.arg,
        &upper_fun.arg,
        false,
        &HashSet::new(),
        observed_vars,
    );
    let mut rendered_input_vars = HashSet::new();
    collect_type_vars(&arg, &mut rendered_input_vars);
    rendered_input_vars.extend(observed_vars.iter().copied());

    Some(Type::Fun {
        arg: Box::new(arg),
        arg_eff: Box::new(coalesce_root_fun_arg_effect_field(
            ctx,
            &lower_fun.arg_eff,
            &upper_fun.arg_eff,
        )),
        ret_eff: Box::new(coalesce_root_fun_effect_field(
            ctx,
            &lower_fun.ret_eff,
            &CompactType::default(),
            true,
            observed_vars,
        )),
        ret: Box::new(coalesce_root_fun_field(
            ctx,
            &lower_fun.ret,
            &upper_fun.ret,
            true,
            &rendered_input_vars,
            observed_vars,
        )),
    })
}

fn coalesce_root_fun_arg_effect_field(
    ctx: &mut CompactToTypeCtx<'_>,
    lower: &CompactType,
    upper: &CompactType,
) -> Type {
    let mut bounds = CompactBounds {
        self_var: None,
        lower: lower.clone(),
        upper: upper.clone(),
    };
    strip_generated_local_effects_from_compact_effect_bounds(&mut bounds);
    let mut ty = closed_upper_row_with_matching_lower_shape(&bounds.lower, &bounds.upper)
        .or_else(|| {
            common_compact_type(&bounds.lower, &bounds.upper).filter(|ty| {
                !is_empty_compact(ty)
                    && (has_non_var_shape(ty) || !has_non_var_shape(&bounds.lower))
            })
        })
        .unwrap_or(bounds.lower);
    remove_upper_covered_row_tail_vars(&mut ty, &bounds.upper);

    if is_empty_compact(&ty) || is_explicit_empty_row_compact(&ty) {
        Type::Bot
    } else if is_var_only_compact(&ty) {
        Type::Var(*ty.vars.iter().next().unwrap())
    } else {
        ctx.coalesce_type(&ty, false)
    }
}

fn simplify_function_effect_residual_rows_for_render(fun: &mut CompactFun) {
    if fun.arg_eff.rows.is_empty() || fun.ret_eff.vars.is_empty() {
        return;
    }

    let closed_shapes = fun
        .arg_eff
        .rows
        .iter()
        .filter(|row| !row.items.is_empty() && is_empty_compact(&row.tail))
        .filter_map(|row| sorted_effect_row_shape(row))
        .collect::<HashSet<_>>();
    let has_empty_residual_row = fun.arg_eff.rows.iter().any(|row| {
        row.items.is_empty() && row.tail.vars.iter().any(|tv| fun.ret_eff.vars.contains(tv))
    });
    let mut row_tail_vars = HashSet::new();
    let mut closed_covered_tail_vars = HashSet::new();
    for row in &fun.arg_eff.rows {
        if row.items.is_empty() {
            continue;
        }
        let tail_vars = row
            .tail
            .vars
            .intersection(&fun.ret_eff.vars)
            .copied()
            .collect::<Vec<_>>();
        if tail_vars.is_empty() {
            continue;
        }
        row_tail_vars.extend(tail_vars.iter().copied());
        if sorted_effect_row_shape(row).is_some_and(|shape| closed_shapes.contains(&shape)) {
            closed_covered_tail_vars.extend(tail_vars);
        }
    }
    if !has_empty_residual_row && closed_covered_tail_vars.is_empty() {
        return;
    }

    for tv in &row_tail_vars {
        fun.arg_eff.vars.remove(tv);
    }
    for tv in &closed_covered_tail_vars {
        fun.ret_eff.vars.remove(tv);
    }

    fun.arg_eff.rows.retain(|row| {
        if row.items.is_empty() {
            return !row_tail_is_only_vars_from(row, &row_tail_vars);
        }
        if closed_covered_tail_vars.is_empty() {
            return true;
        }
        let has_closed_shape =
            sorted_effect_row_shape(row).is_some_and(|shape| closed_shapes.contains(&shape));
        !has_closed_shape || !row_tail_has_var_from(row, &closed_covered_tail_vars)
    });
}

fn sorted_effect_row_shape(row: &CompactRow) -> Option<Vec<(String, usize)>> {
    let mut shape = effect_row_shapes(&row.items)?;
    shape.sort();
    Some(shape)
}

fn row_tail_is_only_vars_from(row: &CompactRow, vars: &HashSet<TypeVar>) -> bool {
    !row.tail.vars.is_empty()
        && row.tail.vars.iter().all(|tv| vars.contains(tv))
        && row.tail.prims.is_empty()
        && row.tail.cons.is_empty()
        && row.tail.funs.is_empty()
        && row.tail.records.is_empty()
        && row.tail.record_spreads.is_empty()
        && row.tail.variants.is_empty()
        && row.tail.tuples.is_empty()
        && row.tail.rows.is_empty()
}

fn row_tail_has_var_from(row: &CompactRow, vars: &HashSet<TypeVar>) -> bool {
    row.tail.vars.iter().any(|tv| vars.contains(tv))
}

fn closed_upper_row_with_matching_lower_shape(
    lower: &CompactType,
    upper: &CompactType,
) -> Option<CompactType> {
    let row = upper.rows.iter().find(|upper_row| {
        is_empty_compact(&upper_row.tail)
            && lower
                .rows
                .iter()
                .any(|lower_row| same_effect_row_shape(lower_row, upper_row))
    })?;
    Some(CompactType {
        vars: upper.vars.clone(),
        rows: vec![row.clone()],
        ..CompactType::default()
    })
}

fn same_effect_row_shape(lhs: &CompactRow, rhs: &CompactRow) -> bool {
    let Some(mut lhs_shapes) = effect_row_shapes(&lhs.items) else {
        return false;
    };
    let Some(mut rhs_shapes) = effect_row_shapes(&rhs.items) else {
        return false;
    };
    lhs_shapes.sort();
    rhs_shapes.sort();
    lhs_shapes == rhs_shapes
}

fn effect_row_shapes(items: &[CompactType]) -> Option<Vec<(String, usize)>> {
    items.iter().map(effect_row_item_shape).collect()
}

fn effect_row_item_shape(item: &CompactType) -> Option<(String, usize)> {
    if !item.vars.is_empty()
        || !item.funs.is_empty()
        || !item.records.is_empty()
        || !item.record_spreads.is_empty()
        || !item.variants.is_empty()
        || !item.tuples.is_empty()
        || !item.rows.is_empty()
    {
        return None;
    }
    if item.prims.len() == 1 && item.cons.is_empty() {
        let path = item.prims.iter().next()?;
        return Some((path_string_for_shape(path), 0));
    }
    if item.cons.len() == 1 && item.prims.is_empty() {
        let con = &item.cons[0];
        return Some((path_string_for_shape(&con.path), con.args.len()));
    }
    None
}

fn path_string_for_shape(path: &crate::symbols::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn remove_upper_covered_row_tail_vars(ty: &mut CompactType, upper: &CompactType) {
    if ty.rows.is_empty() || upper.vars.is_empty() {
        return;
    }
    let covered = ty
        .rows
        .iter()
        .flat_map(|row| row.tail.vars.iter().copied())
        .filter(|tv| upper.vars.contains(tv))
        .collect::<HashSet<_>>();
    for tv in covered {
        ty.vars.remove(&tv);
    }
}

fn coalesce_lower_only_root_fun(
    ctx: &mut CompactToTypeCtx<'_>,
    bounds: &CompactBounds,
    coalesce_effect_residual: bool,
    observed_vars: &HashSet<TypeVar>,
) -> Option<Type> {
    let [lower_fun] = bounds.lower.funs.as_slice() else {
        return None;
    };
    let should_coalesce_effect_residual =
        coalesce_effect_residual || lower_fun.ret_eff.vars.len() > 1;
    if !bounds.upper.funs.is_empty()
        || !root_non_fun_parts_empty(&bounds.lower)
        || !root_non_fun_parts_empty(&bounds.upper)
    {
        return None;
    }

    let mut lower_fun = lower_fun.clone();
    if should_coalesce_effect_residual
        && !lower_fun.arg_eff.rows.is_empty()
        && !lower_fun.arg_eff.vars.is_empty()
        && !lower_fun.ret_eff.vars.is_empty()
    {
        coalesce_function_effect_residual(&mut lower_fun.arg_eff, &mut lower_fun.ret_eff);
    }
    simplify_function_effect_residual_rows_for_render(&mut lower_fun);
    let arg = coalesce_lower_only_root_fun_field(ctx, &lower_fun.arg, false, &HashSet::new());
    let mut rendered_input_vars = HashSet::new();
    collect_type_vars(&arg, &mut rendered_input_vars);
    rendered_input_vars.extend(observed_vars.iter().copied());

    Some(Type::Fun {
        arg: Box::new(arg),
        arg_eff: Box::new(ctx.coalesce_type(&lower_fun.arg_eff, false)),
        ret_eff: Box::new(ctx.coalesce_output_effect_type(&lower_fun.ret_eff, true)),
        ret: Box::new(coalesce_lower_only_root_fun_field(
            ctx,
            &lower_fun.ret,
            true,
            &rendered_input_vars,
        )),
    })
}

fn coalesce_lower_only_root_fun_field(
    ctx: &mut CompactToTypeCtx<'_>,
    ty: &CompactType,
    positive: bool,
    input_vars: &HashSet<TypeVar>,
) -> Type {
    let mut ty = ty.clone();
    if has_non_var_shape(&ty) {
        if positive {
            ty.vars.retain(|var| input_vars.contains(var));
        } else {
            ty.vars.clear();
        }
    }
    if is_var_only_compact(&ty) {
        Type::Var(*ty.vars.iter().next().unwrap())
    } else {
        ctx.coalesce_type(&ty, positive)
    }
}

fn coalesce_root_fun_effect_field(
    ctx: &mut CompactToTypeCtx<'_>,
    lower: &CompactType,
    upper: &CompactType,
    positive: bool,
    observed_vars: &HashSet<TypeVar>,
) -> Type {
    let bounds = normalize_render_bounds(CompactBounds {
        self_var: None,
        lower: lower.clone(),
        upper: upper.clone(),
    });
    if let Some(fun) = coalesce_root_fun(ctx, &bounds, true, observed_vars) {
        return simplify_type(fun);
    }

    let ty = if positive
        && (is_empty_compact(&bounds.lower) || is_explicit_empty_row_compact(&bounds.lower))
    {
        bounds.upper
    } else if positive {
        bounds.lower
    } else {
        common_compact_type(&bounds.lower, &bounds.upper)
            .filter(|common| {
                !is_empty_compact(common)
                    && (has_non_var_shape(common) || !has_non_var_shape(&bounds.lower))
            })
            .unwrap_or(bounds.lower)
    };

    if is_empty_compact(&ty) || is_explicit_empty_row_compact(&ty) {
        Type::Bot
    } else if is_var_only_compact(&ty) {
        Type::Var(*ty.vars.iter().next().unwrap())
    } else {
        ctx.coalesce_output_effect_type(&ty, positive)
    }
}

fn coalesce_root_fun_field(
    ctx: &mut CompactToTypeCtx<'_>,
    lower: &CompactType,
    upper: &CompactType,
    positive: bool,
    input_vars: &HashSet<TypeVar>,
    observed_vars: &HashSet<TypeVar>,
) -> Type {
    let bounds = normalize_render_bounds(CompactBounds {
        self_var: None,
        lower: lower.clone(),
        upper: upper.clone(),
    });
    if let Some(fun) = coalesce_root_fun(ctx, &bounds, true, observed_vars) {
        return simplify_type(fun);
    }

    let ty = if positive {
        common_compact_type(&bounds.lower, &bounds.upper)
            .filter(|common| {
                !is_empty_compact(common)
                    && !has_non_var_shape_outside_common(&bounds.lower, common)
            })
            .map(|common| drop_non_input_vars_when_concrete(common, input_vars))
            .unwrap_or(bounds.lower)
    } else {
        let mut ty = common_compact_type(&bounds.lower, &bounds.upper)
            .filter(|ty| !is_empty_compact(ty))
            .unwrap_or(bounds.lower);
        if has_non_var_shape(&ty) {
            ty.vars.clear();
        }
        ty
    };

    if is_var_only_compact(&ty) {
        Type::Var(*ty.vars.iter().next().unwrap())
    } else {
        ctx.coalesce_type(&ty, positive)
    }
}

fn drop_non_input_vars_when_concrete(
    mut ty: CompactType,
    input_vars: &HashSet<TypeVar>,
) -> CompactType {
    if has_non_var_shape(&ty) {
        ty.vars.retain(|var| input_vars.contains(var));
    }
    ty
}

fn simplify_type(ty: Type) -> Type {
    match ty {
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Type::Fun {
            arg: Box::new(simplify_type(*arg)),
            arg_eff: Box::new(simplify_type(*arg_eff)),
            ret_eff: Box::new(simplify_type(*ret_eff)),
            ret: Box::new(simplify_type(*ret)),
        },
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: simplify_type(field.value),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::RecordTailSpread { fields, tail } => Type::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: simplify_type(field.value),
                    optional: field.optional,
                })
                .collect(),
            tail: Box::new(simplify_type(*tail)),
        },
        Type::RecordHeadSpread { tail, fields } => Type::RecordHeadSpread {
            tail: Box::new(simplify_type(*tail)),
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: simplify_type(field.value),
                    optional: field.optional,
                })
                .collect(),
        },
        Type::Variant(items) => Type::Variant(
            items
                .into_iter()
                .map(|(name, payloads)| (name, payloads.into_iter().map(simplify_type).collect()))
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(items.into_iter().map(simplify_type).collect()),
        Type::Row(items, tail) => {
            let mut items = items
                .into_iter()
                .map(simplify_type)
                .filter(|item| !is_empty_row(item))
                .collect::<Vec<_>>();
            let mut deduped = Vec::new();
            for item in items.drain(..) {
                if !deduped.contains(&item) {
                    deduped.push(item);
                }
            }
            Type::Row(deduped, Box::new(simplify_type(*tail)))
        }
        Type::Union(items) => {
            let mut out = Vec::new();
            for item in items.into_iter().map(simplify_type) {
                match item {
                    Type::Union(nested) => out.extend(nested),
                    other if !is_empty_row(&other) => out.push(other),
                    _ => {}
                }
            }
            combine_types(out, true)
        }
        Type::Inter(items) => {
            let mut out = Vec::new();
            for item in items.into_iter().map(simplify_type) {
                match item {
                    Type::Inter(nested) => out.extend(nested),
                    other => out.push(other),
                }
            }
            combine_types(out, false)
        }
        Type::Rec(tv, body) => {
            let body = simplify_type(*body);
            if body == Type::Var(tv) {
                Type::Var(tv)
            } else {
                Type::Rec(tv, Box::new(body))
            }
        }
        other => other,
    }
}

fn simplify_root_type(ty: Type) -> Type {
    let ty = simplify_type(ty);
    let generated_local_effect_vars = generated_local_effect_tail_vars(&ty);
    let ty = strip_generated_local_effects_from_fun_effects(ty, &generated_local_effect_vars);
    let ty = simplify_type(ty);
    normalize_root_curried_fun_effect_chain(ty)
}

fn generated_local_effect_tail_vars(ty: &Type) -> HashSet<TypeVar> {
    let mut vars = HashSet::new();
    collect_generated_local_effect_tail_vars(ty, &mut vars);
    vars
}

fn collect_generated_local_effect_tail_vars(ty: &Type, out: &mut HashSet<TypeVar>) {
    match ty {
        Type::Con(path, args) if is_generated_local_effect_path(path) => {
            for arg in args {
                collect_compact_bounds_vars(arg, out);
            }
        }
        Type::Con(_, args) => {
            for arg in args {
                collect_compact_bounds_generated_local_effect_tail_vars(arg, out);
            }
        }
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_generated_local_effect_tail_vars(arg, out);
            collect_generated_local_effect_tail_vars(arg_eff, out);
            collect_generated_local_effect_tail_vars(ret_eff, out);
            collect_generated_local_effect_tail_vars(ret, out);
        }
        Type::Record(fields) => {
            for field in fields {
                collect_generated_local_effect_tail_vars(&field.value, out);
            }
        }
        Type::RecordTailSpread { fields, tail } | Type::RecordHeadSpread { fields, tail } => {
            for field in fields {
                collect_generated_local_effect_tail_vars(&field.value, out);
            }
            collect_generated_local_effect_tail_vars(tail, out);
        }
        Type::Variant(cases) => {
            for (_, payloads) in cases {
                for payload in payloads {
                    collect_generated_local_effect_tail_vars(payload, out);
                }
            }
        }
        Type::Tuple(items) => {
            for item in items {
                collect_generated_local_effect_tail_vars(item, out);
            }
        }
        Type::Union(items) | Type::Inter(items) => {
            let has_generated_local = items.iter().any(type_contains_generated_local_effect);
            for item in items {
                collect_generated_local_effect_tail_vars(item, out);
            }
            if has_generated_local {
                for item in items {
                    collect_type_vars(item, out);
                }
            }
        }
        Type::Row(items, tail) => {
            let has_generated_local = items.iter().any(type_contains_generated_local_effect);
            for item in items {
                collect_generated_local_effect_tail_vars(item, out);
            }
            collect_generated_local_effect_tail_vars(tail, out);
            if has_generated_local {
                for item in items {
                    collect_type_vars(item, out);
                }
                collect_type_vars(tail, out);
            }
        }
        Type::Rec(_, body) => collect_generated_local_effect_tail_vars(body, out),
        Type::Var(_) | Type::Prim(_) | Type::Bot | Type::Top => {}
    }
}

fn collect_compact_bounds_generated_local_effect_tail_vars(
    bounds: &CompactBounds,
    out: &mut HashSet<TypeVar>,
) {
    collect_compact_type_generated_local_effect_tail_vars(&bounds.lower, out);
    collect_compact_type_generated_local_effect_tail_vars(&bounds.upper, out);
}

fn collect_compact_type_generated_local_effect_tail_vars(
    ty: &CompactType,
    out: &mut HashSet<TypeVar>,
) {
    for con in &ty.cons {
        if is_generated_local_effect_path(&con.path) {
            for arg in &con.args {
                collect_compact_bounds_vars(arg, out);
            }
        } else {
            for arg in &con.args {
                collect_compact_bounds_generated_local_effect_tail_vars(arg, out);
            }
        }
    }
    for fun in &ty.funs {
        collect_compact_type_generated_local_effect_tail_vars(&fun.arg, out);
        collect_compact_type_generated_local_effect_tail_vars(&fun.arg_eff, out);
        collect_compact_type_generated_local_effect_tail_vars(&fun.ret_eff, out);
        collect_compact_type_generated_local_effect_tail_vars(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_compact_type_generated_local_effect_tail_vars(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_compact_type_generated_local_effect_tail_vars(&field.value, out);
        }
        collect_compact_type_generated_local_effect_tail_vars(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_compact_type_generated_local_effect_tail_vars(payload, out);
            }
        }
    }
    for items in &ty.tuples {
        for item in items {
            collect_compact_type_generated_local_effect_tail_vars(item, out);
        }
    }
    for row in &ty.rows {
        let has_generated_local = row
            .items
            .iter()
            .any(compact_type_contains_generated_local_effect);
        for item in &row.items {
            collect_compact_type_generated_local_effect_tail_vars(item, out);
        }
        collect_compact_type_generated_local_effect_tail_vars(&row.tail, out);
        if has_generated_local {
            for item in &row.items {
                collect_compact_type_vars(item, out);
            }
            collect_compact_type_vars(&row.tail, out);
        }
    }
}

fn collect_type_vars(ty: &Type, out: &mut HashSet<TypeVar>) {
    match ty {
        Type::Var(var) => {
            out.insert(*var);
        }
        Type::Con(_, args) => {
            for arg in args {
                collect_compact_bounds_vars(arg, out);
            }
        }
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_type_vars(arg, out);
            collect_type_vars(arg_eff, out);
            collect_type_vars(ret_eff, out);
            collect_type_vars(ret, out);
        }
        Type::Record(fields) => {
            for field in fields {
                collect_type_vars(&field.value, out);
            }
        }
        Type::RecordTailSpread { fields, tail } | Type::RecordHeadSpread { fields, tail } => {
            for field in fields {
                collect_type_vars(&field.value, out);
            }
            collect_type_vars(tail, out);
        }
        Type::Variant(cases) => {
            for (_, payloads) in cases {
                for payload in payloads {
                    collect_type_vars(payload, out);
                }
            }
        }
        Type::Tuple(items) | Type::Union(items) | Type::Inter(items) => {
            for item in items {
                collect_type_vars(item, out);
            }
        }
        Type::Row(items, tail) => {
            for item in items {
                collect_type_vars(item, out);
            }
            collect_type_vars(tail, out);
        }
        Type::Rec(var, body) => {
            out.insert(*var);
            collect_type_vars(body, out);
        }
        Type::Prim(_) | Type::Bot | Type::Top => {}
    }
}

pub(crate) fn collect_compact_bounds_observed_vars(
    bounds: &CompactBounds,
    out: &mut HashSet<TypeVar>,
) {
    if let Some(tv) = bounds.self_var {
        out.insert(tv);
    }
    collect_compact_bounds_vars(bounds, out);
}

fn collect_compact_bounds_vars(bounds: &CompactBounds, out: &mut HashSet<TypeVar>) {
    collect_compact_type_vars(&bounds.lower, out);
    collect_compact_type_vars(&bounds.upper, out);
}

fn collect_compact_type_vars(ty: &CompactType, out: &mut HashSet<TypeVar>) {
    out.extend(ty.vars.iter().copied());
    for con in &ty.cons {
        for arg in &con.args {
            collect_compact_bounds_vars(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_compact_type_vars(&fun.arg, out);
        collect_compact_type_vars(&fun.arg_eff, out);
        collect_compact_type_vars(&fun.ret_eff, out);
        collect_compact_type_vars(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_compact_type_vars(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_compact_type_vars(&field.value, out);
        }
        collect_compact_type_vars(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_compact_type_vars(payload, out);
            }
        }
    }
    for items in &ty.tuples {
        for item in items {
            collect_compact_type_vars(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_compact_type_vars(item, out);
        }
        collect_compact_type_vars(&row.tail, out);
    }
}

fn strip_generated_local_effects_from_fun_effects(ty: Type, tainted: &HashSet<TypeVar>) -> Type {
    match ty {
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Type::Fun {
            arg: Box::new(strip_generated_local_effects_from_fun_effects(
                *arg, tainted,
            )),
            arg_eff: Box::new(strip_generated_local_effect_type(*arg_eff, tainted)),
            ret_eff: Box::new(strip_generated_local_effect_type(*ret_eff, tainted)),
            ret: Box::new(strip_generated_local_effects_from_fun_effects(
                *ret, tainted,
            )),
        },
        Type::Record(fields) => Type::Record(
            fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: strip_generated_local_effects_from_fun_effects(field.value, tainted),
                    optional: field.optional,
                })
                .collect(),
        ),
        Type::RecordTailSpread { fields, tail } => Type::RecordTailSpread {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: strip_generated_local_effects_from_fun_effects(field.value, tainted),
                    optional: field.optional,
                })
                .collect(),
            tail: Box::new(strip_generated_local_effects_from_fun_effects(
                *tail, tainted,
            )),
        },
        Type::RecordHeadSpread { tail, fields } => Type::RecordHeadSpread {
            tail: Box::new(strip_generated_local_effects_from_fun_effects(
                *tail, tainted,
            )),
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: strip_generated_local_effects_from_fun_effects(field.value, tainted),
                    optional: field.optional,
                })
                .collect(),
        },
        Type::Variant(cases) => Type::Variant(
            cases
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                strip_generated_local_effects_from_fun_effects(payload, tainted)
                            })
                            .collect(),
                    )
                })
                .collect(),
        ),
        Type::Tuple(items) => Type::Tuple(
            items
                .into_iter()
                .map(|item| strip_generated_local_effects_from_fun_effects(item, tainted))
                .collect(),
        ),
        Type::Union(items) => Type::Union(
            items
                .into_iter()
                .map(|item| strip_generated_local_effects_from_fun_effects(item, tainted))
                .collect(),
        ),
        Type::Inter(items) => Type::Inter(
            items
                .into_iter()
                .map(|item| strip_generated_local_effects_from_fun_effects(item, tainted))
                .collect(),
        ),
        Type::Row(items, tail) => Type::Row(
            items
                .into_iter()
                .map(|item| strip_generated_local_effects_from_fun_effects(item, tainted))
                .collect(),
            Box::new(strip_generated_local_effects_from_fun_effects(
                *tail, tainted,
            )),
        ),
        Type::Rec(var, body) => Type::Rec(
            var,
            Box::new(strip_generated_local_effects_from_fun_effects(
                *body, tainted,
            )),
        ),
        other => other,
    }
}

fn strip_generated_local_effect_type(ty: Type, tainted: &HashSet<TypeVar>) -> Type {
    match ty {
        Type::Var(var) if tainted.contains(&var) => Type::Bot,
        Type::Con(path, _) if is_generated_local_effect_path(&path) => Type::Bot,
        Type::Row(items, tail) => {
            let items = items
                .into_iter()
                .map(|item| strip_generated_local_effect_type(item, tainted))
                .filter(|item| !is_empty_effect_placeholder(item))
                .collect();
            let tail = strip_generated_local_effect_type(*tail, tainted);
            Type::Row(items, Box::new(tail))
        }
        Type::Union(items) => Type::Union(
            items
                .into_iter()
                .map(|item| strip_generated_local_effect_type(item, tainted))
                .filter(|item| !is_empty_effect_placeholder(item))
                .collect(),
        ),
        Type::Inter(items) => Type::Inter(
            items
                .into_iter()
                .map(|item| strip_generated_local_effect_type(item, tainted))
                .filter(|item| !is_empty_effect_placeholder(item))
                .collect(),
        ),
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => Type::Fun {
            arg: Box::new(strip_generated_local_effects_from_fun_effects(
                *arg, tainted,
            )),
            arg_eff: Box::new(strip_generated_local_effect_type(*arg_eff, tainted)),
            ret_eff: Box::new(strip_generated_local_effect_type(*ret_eff, tainted)),
            ret: Box::new(strip_generated_local_effects_from_fun_effects(
                *ret, tainted,
            )),
        },
        other => strip_generated_local_effects_from_fun_effects(other, tainted),
    }
}

fn type_contains_generated_local_effect(ty: &Type) -> bool {
    match ty {
        Type::Con(path, args) => {
            is_generated_local_effect_path(path)
                || args
                    .iter()
                    .any(compact_bounds_contains_generated_local_effect)
        }
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            type_contains_generated_local_effect(arg)
                || type_contains_generated_local_effect(arg_eff)
                || type_contains_generated_local_effect(ret_eff)
                || type_contains_generated_local_effect(ret)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_contains_generated_local_effect(&field.value)),
        Type::RecordTailSpread { fields, tail } | Type::RecordHeadSpread { fields, tail } => {
            fields
                .iter()
                .any(|field| type_contains_generated_local_effect(&field.value))
                || type_contains_generated_local_effect(tail)
        }
        Type::Variant(cases) => cases
            .iter()
            .any(|(_, payloads)| payloads.iter().any(type_contains_generated_local_effect)),
        Type::Tuple(items) | Type::Union(items) | Type::Inter(items) => {
            items.iter().any(type_contains_generated_local_effect)
        }
        Type::Row(items, tail) => {
            items.iter().any(type_contains_generated_local_effect)
                || type_contains_generated_local_effect(tail)
        }
        Type::Rec(_, body) => type_contains_generated_local_effect(body),
        Type::Var(_) | Type::Prim(_) | Type::Bot | Type::Top => false,
    }
}

fn compact_bounds_contains_generated_local_effect(bounds: &CompactBounds) -> bool {
    compact_type_contains_generated_local_effect(&bounds.lower)
        || compact_type_contains_generated_local_effect(&bounds.upper)
}

fn compact_type_contains_generated_local_effect(ty: &CompactType) -> bool {
    ty.cons.iter().any(|con| {
        is_generated_local_effect_path(&con.path)
            || con
                .args
                .iter()
                .any(compact_bounds_contains_generated_local_effect)
    }) || ty.funs.iter().any(|fun| {
        compact_type_contains_generated_local_effect(&fun.arg)
            || compact_type_contains_generated_local_effect(&fun.arg_eff)
            || compact_type_contains_generated_local_effect(&fun.ret_eff)
            || compact_type_contains_generated_local_effect(&fun.ret)
    }) || ty.records.iter().any(|record| {
        record
            .fields
            .iter()
            .any(|field| compact_type_contains_generated_local_effect(&field.value))
    }) || ty.record_spreads.iter().any(|spread| {
        spread
            .fields
            .iter()
            .any(|field| compact_type_contains_generated_local_effect(&field.value))
            || compact_type_contains_generated_local_effect(&spread.tail)
    }) || ty.variants.iter().any(|variant| {
        variant.items.iter().any(|(_, payloads)| {
            payloads
                .iter()
                .any(compact_type_contains_generated_local_effect)
        })
    }) || ty.tuples.iter().any(|items| {
        items
            .iter()
            .any(compact_type_contains_generated_local_effect)
    }) || ty.rows.iter().any(|row| {
        row.items
            .iter()
            .any(compact_type_contains_generated_local_effect)
            || compact_type_contains_generated_local_effect(&row.tail)
    })
}

fn strip_generated_local_effects_from_compact_effect_bounds(bounds: &mut CompactBounds) {
    let mut tainted = HashSet::new();
    collect_compact_type_generated_local_effect_tail_vars(&bounds.lower, &mut tainted);
    collect_compact_type_generated_local_effect_tail_vars(&bounds.upper, &mut tainted);
    strip_generated_local_effects_from_compact_effect_type(&mut bounds.lower, &tainted);
    strip_generated_local_effects_from_compact_effect_type(&mut bounds.upper, &tainted);
}

fn strip_generated_local_effects_from_compact_effect_type(
    ty: &mut CompactType,
    tainted: &HashSet<TypeVar>,
) {
    ty.vars.retain(|var| !tainted.contains(var));
    ty.cons
        .retain(|con| !is_generated_local_effect_path(&con.path));
    for fun in &mut ty.funs {
        strip_generated_local_effects_from_compact_effect_type(&mut fun.arg_eff, tainted);
        strip_generated_local_effects_from_compact_effect_type(&mut fun.ret_eff, tainted);
    }
    for row in &mut ty.rows {
        row.items
            .retain(|item| !is_generated_local_effect_compact_item(item));
        for item in &mut row.items {
            strip_generated_local_effects_from_compact_effect_type(item, tainted);
        }
        strip_generated_local_effects_from_compact_effect_type(&mut row.tail, tainted);
    }
    ty.rows
        .retain(|row| !row.items.is_empty() || !is_empty_compact(&row.tail));
}

fn is_generated_local_effect_compact_item(item: &CompactType) -> bool {
    item.vars.is_empty()
        && item.prims.is_empty()
        && item.cons.len() == 1
        && item
            .cons
            .first()
            .is_some_and(|con| is_generated_local_effect_path(&con.path))
        && item.funs.is_empty()
        && item.records.is_empty()
        && item.record_spreads.is_empty()
        && item.variants.is_empty()
        && item.tuples.is_empty()
        && item.rows.is_empty()
}

fn is_generated_local_effect_path(path: &Path) -> bool {
    path.segments
        .first()
        .is_some_and(|segment| segment.0.starts_with('&'))
}

fn normalize_root_curried_fun_effect_chain(ty: Type) -> Type {
    let Some((mut chain, tail)) = collect_root_fun_chain(ty.clone()) else {
        return ty;
    };

    clear_prefix_latent_effects_before_effectful_arg(&mut chain);
    clear_unshared_intermediate_ret_effect_vars(&mut chain, &tail);
    let latent = common_non_empty_root_ret_effect(&chain);
    if let Some(effect) = latent {
        let last = chain.len().saturating_sub(1);
        for (idx, (_, _, ret_eff)) in chain.iter_mut().enumerate() {
            *ret_eff = Box::new(if idx == last {
                effect.clone()
            } else {
                empty_fun_effect_placeholder()
            });
        }
    }

    rebuild_root_fun_chain(chain, tail)
}

fn clear_unshared_intermediate_ret_effect_vars(chain: &mut [RootFunLink], tail: &Type) {
    if chain.len() < 2 {
        return;
    }
    for idx in 0..chain.len() - 1 {
        let Some(var) = bare_or_empty_row_tail_var(&chain[idx].2) else {
            continue;
        };
        if root_fun_var_is_used_outside_ret_eff(var, chain, tail, idx) {
            continue;
        }
        chain[idx].2 = Box::new(empty_fun_effect_placeholder());
    }
}

fn bare_or_empty_row_tail_var(ty: &Type) -> Option<TypeVar> {
    match ty {
        Type::Var(var) => Some(*var),
        Type::Row(items, tail) if items.is_empty() => match tail.as_ref() {
            Type::Var(var) => Some(*var),
            _ => None,
        },
        _ => None,
    }
}

fn root_fun_var_is_used_outside_ret_eff(
    var: TypeVar,
    chain: &[RootFunLink],
    tail: &Type,
    ret_eff_idx: usize,
) -> bool {
    for (idx, (arg, arg_eff, ret_eff)) in chain.iter().enumerate() {
        if type_contains_var(arg, var) || type_contains_var(arg_eff, var) {
            return true;
        }
        if idx != ret_eff_idx && type_contains_var(ret_eff, var) {
            return true;
        }
    }
    type_contains_var(tail, var)
}

fn type_contains_var(ty: &Type, var: TypeVar) -> bool {
    match ty {
        Type::Var(tv) => *tv == var,
        Type::Con(_, args) => args.iter().any(|arg| compact_bounds_contains_var(arg, var)),
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            type_contains_var(arg, var)
                || type_contains_var(arg_eff, var)
                || type_contains_var(ret_eff, var)
                || type_contains_var(ret, var)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_contains_var(&field.value, var)),
        Type::RecordTailSpread { fields, tail } | Type::RecordHeadSpread { tail, fields } => {
            fields
                .iter()
                .any(|field| type_contains_var(&field.value, var))
                || type_contains_var(tail, var)
        }
        Type::Variant(cases) => cases.iter().any(|(_, payloads)| {
            payloads
                .iter()
                .any(|payload| type_contains_var(payload, var))
        }),
        Type::Tuple(items) | Type::Union(items) | Type::Inter(items) => {
            items.iter().any(|item| type_contains_var(item, var))
        }
        Type::Row(items, tail) => {
            items.iter().any(|item| type_contains_var(item, var)) || type_contains_var(tail, var)
        }
        Type::Rec(tv, body) => *tv == var || type_contains_var(body, var),
        Type::Prim(_) | Type::Bot | Type::Top => false,
    }
}

fn compact_bounds_contains_var(bounds: &CompactBounds, var: TypeVar) -> bool {
    compact_type_contains_var_for_render(&bounds.lower, var)
        || compact_type_contains_var_for_render(&bounds.upper, var)
}

fn compact_type_contains_var_for_render(ty: &CompactType, var: TypeVar) -> bool {
    ty.vars.contains(&var)
        || ty.cons.iter().any(|con| {
            con.args
                .iter()
                .any(|arg| compact_bounds_contains_var(arg, var))
        })
        || ty.funs.iter().any(|fun| {
            compact_type_contains_var_for_render(&fun.arg, var)
                || compact_type_contains_var_for_render(&fun.arg_eff, var)
                || compact_type_contains_var_for_render(&fun.ret_eff, var)
                || compact_type_contains_var_for_render(&fun.ret, var)
        })
        || ty.records.iter().any(|record| {
            record
                .fields
                .iter()
                .any(|field| compact_type_contains_var_for_render(&field.value, var))
        })
        || ty.record_spreads.iter().any(|spread| {
            spread
                .fields
                .iter()
                .any(|field| compact_type_contains_var_for_render(&field.value, var))
                || compact_type_contains_var_for_render(&spread.tail, var)
        })
        || ty.variants.iter().any(|variant| {
            variant.items.iter().any(|(_, payloads)| {
                payloads
                    .iter()
                    .any(|payload| compact_type_contains_var_for_render(payload, var))
            })
        })
        || ty.tuples.iter().any(|items| {
            items
                .iter()
                .any(|item| compact_type_contains_var_for_render(item, var))
        })
        || ty.rows.iter().any(|row| {
            row.items
                .iter()
                .any(|item| compact_type_contains_var_for_render(item, var))
                || compact_type_contains_var_for_render(&row.tail, var)
        })
}

fn collect_lower_witnesses(scheme: &CompactTypeScheme) -> HashMap<TypeVar, CompactType> {
    let mut out = HashMap::new();
    collect_bounds_lower_witnesses(&scheme.cty, &mut out);
    for bounds in scheme.rec_vars.values() {
        collect_bounds_lower_witnesses(bounds, &mut out);
    }
    out
}

fn collect_bounds_lower_witnesses(bounds: &CompactBounds, out: &mut HashMap<TypeVar, CompactType>) {
    if let Some(upper_vars) = compact_var_set(&bounds.upper) {
        for var in upper_vars {
            let witness = compact_type_without_var(&bounds.lower, var);
            if !is_empty_compact(&witness) {
                out.entry(var)
                    .and_modify(|existing| {
                        *existing = crate::simplify::compact::merge_compact_types(
                            true,
                            existing.clone(),
                            witness.clone(),
                        );
                    })
                    .or_insert(witness);
            }
        }
    }
    collect_type_lower_witnesses(&bounds.lower, out);
    collect_type_lower_witnesses(&bounds.upper, out);
}

fn collect_type_lower_witnesses(ty: &CompactType, out: &mut HashMap<TypeVar, CompactType>) {
    for con in &ty.cons {
        for arg in &con.args {
            collect_bounds_lower_witnesses(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_type_lower_witnesses(&fun.arg, out);
        collect_type_lower_witnesses(&fun.arg_eff, out);
        collect_type_lower_witnesses(&fun.ret_eff, out);
        collect_type_lower_witnesses(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_type_lower_witnesses(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_type_lower_witnesses(&field.value, out);
        }
        collect_type_lower_witnesses(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_type_lower_witnesses(payload, out);
            }
        }
    }
    for items in &ty.tuples {
        for item in items {
            collect_type_lower_witnesses(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_type_lower_witnesses(item, out);
        }
        collect_type_lower_witnesses(&row.tail, out);
    }
}

fn compact_type_without_var(ty: &CompactType, var: TypeVar) -> CompactType {
    let mut ty = ty.clone();
    ty.vars.remove(&var);
    ty
}

fn compact_type_contains_witness(ty: &CompactType, witness: &CompactType) -> bool {
    common_compact_type(ty, witness)
        .is_some_and(|common| !is_empty_compact(&common) && common == *witness)
}

fn clear_prefix_latent_effects_before_effectful_arg(chain: &mut [RootFunLink]) {
    let Some(first_effectful_arg) = chain
        .iter()
        .position(|(_, arg_eff, _)| !is_empty_fun_effect(arg_eff))
    else {
        return;
    };
    for (_, _, ret_eff) in &mut chain[..first_effectful_arg] {
        *ret_eff = Box::new(empty_fun_effect_placeholder());
    }
}

fn is_empty_fun_effect(ty: &Type) -> bool {
    matches!(ty, Type::Bot)
        || is_empty_row(ty)
        || matches!(ty, Type::Row(items, tail) if items.is_empty() && matches!(tail.as_ref(), Type::Top))
}

fn empty_fun_effect_placeholder() -> Type {
    Type::Row(vec![], Box::new(Type::Bot))
}

fn collect_root_fun_chain(mut ty: Type) -> Option<(Vec<RootFunLink>, Type)> {
    let mut chain = Vec::new();

    loop {
        match ty {
            Type::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                chain.push((arg, arg_eff, ret_eff));
                ty = *ret;
            }
            tail => {
                if chain.is_empty() {
                    return None;
                }
                return Some((chain, tail));
            }
        }
    }
}

fn common_non_empty_root_ret_effect(chain: &[RootFunLink]) -> Option<Type> {
    let mut effects = chain.iter().filter_map(|(_, _, ret_eff)| {
        if is_empty_fun_effect(ret_eff) {
            None
        } else {
            Some((**ret_eff).clone())
        }
    });
    let first = effects.next()?;
    if effects.all(|eff| eff == first) {
        Some(first)
    } else {
        None
    }
}

fn rebuild_root_fun_chain(mut chain: Vec<RootFunLink>, tail: Type) -> Type {
    let mut out = tail;
    while let Some((arg, arg_eff, ret_eff)) = chain.pop() {
        out = Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret: Box::new(out),
        };
    }
    out
}

type RootFunLink = (Box<Type>, Box<Type>, Box<Type>);

fn combine_types(parts: Vec<Type>, positive: bool) -> Type {
    let mut flat = Vec::new();
    for part in parts {
        let items = match part {
            Type::Union(items) if positive => items,
            Type::Inter(items) if !positive => items,
            Type::Bot if positive => continue,
            Type::Top if !positive => continue,
            other => vec![other],
        };
        for item in items {
            match item {
                Type::Bot if positive => {}
                Type::Top if !positive => {}
                Type::Row(items, tail)
                    if !positive && items.is_empty() && matches!(tail.as_ref(), Type::Top) => {}
                other if !flat.contains(&other) => flat.push(other),
                _ => {}
            }
        }
    }

    if positive && flat.iter().any(is_float_like_type) {
        flat.retain(|item| !is_int_like_type(item));
    }

    flat = merge_variant_parts(flat, positive);
    if !positive
        && flat.len() > 1
        && let Some(row) = merge_negative_top_tail_rows(&flat)
    {
        flat = vec![row];
    }
    match flat.len() {
        0 => {
            if positive {
                Type::Bot
            } else {
                Type::Top
            }
        }
        1 => flat.into_iter().next().unwrap(),
        _ => {
            if positive {
                Type::Union(flat)
            } else {
                Type::Inter(flat)
            }
        }
    }
}

fn merge_negative_top_tail_rows(parts: &[Type]) -> Option<Type> {
    let mut items = Vec::new();
    let mut tail_parts = Vec::new();
    let mut saw_row = false;

    for part in parts {
        match part {
            Type::Row(row_items, tail) if matches!(tail.as_ref(), Type::Top) => {
                saw_row = true;
                for item in row_items {
                    if !items.contains(item) {
                        items.push(item.clone());
                    }
                }
            }
            Type::Var(_) => tail_parts.push(part.clone()),
            _ => return None,
        }
    }

    if !saw_row || items.is_empty() {
        return None;
    }

    let tail = if tail_parts.is_empty() {
        Type::Top
    } else {
        combine_types(tail_parts, false)
    };
    Some(Type::Row(items, Box::new(tail)))
}

fn merge_variant_parts(parts: Vec<Type>, positive: bool) -> Vec<Type> {
    let mut out = Vec::new();
    let mut variant_items = Vec::<(Name, Vec<Type>)>::new();

    for part in parts {
        match part {
            Type::Variant(items) => merge_variant_items(&mut variant_items, items, positive),
            other => out.push(other),
        }
    }

    if !variant_items.is_empty() {
        out.push(Type::Variant(variant_items));
    }
    out
}

fn merge_variant_items(
    out: &mut Vec<(Name, Vec<Type>)>,
    items: Vec<(Name, Vec<Type>)>,
    positive: bool,
) {
    for (name, payloads) in items {
        if let Some((_, existing_payloads)) =
            out.iter_mut().find(|(existing_name, existing_payloads)| {
                *existing_name == name && existing_payloads.len() == payloads.len()
            })
        {
            *existing_payloads = std::mem::take(existing_payloads)
                .into_iter()
                .zip(payloads.into_iter())
                .map(|(lhs, rhs)| combine_types(vec![lhs, rhs], positive))
                .collect();
        } else {
            out.push((name, payloads));
        }
    }
}

fn is_float_like_type(ty: &Type) -> bool {
    match ty {
        Type::Prim(path) => path.segments.last().map(|name| name.0.as_str()) == Some("float"),
        Type::Con(path, args) => {
            args.is_empty() && path.segments.last().map(|name| name.0.as_str()) == Some("float")
        }
        _ => false,
    }
}

fn is_int_like_type(ty: &Type) -> bool {
    match ty {
        Type::Prim(path) => path.segments.last().map(|name| name.0.as_str()) == Some("int"),
        Type::Con(path, args) => {
            args.is_empty() && path.segments.last().map(|name| name.0.as_str()) == Some("int")
        }
        _ => false,
    }
}

fn format_type_inner(ty: &Type, namer: &mut VarNamer<'_>, needs_paren: bool) -> String {
    match ty {
        Type::Var(tv) => namer.name(tv.0),
        Type::Prim(path) => namer.render_path(path),
        Type::Con(path, args) => {
            let name = namer.render_path(path);
            if args.is_empty() {
                return name;
            }
            let args = args
                .iter()
                .map(|arg| format_compact_bounds(arg, namer))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{name}<{args}>")
        }
        Type::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            let arg = format_type_inner(arg, namer, true);
            let ret = format_type_inner(ret, namer, false);
            let arg_eff = format_row_inline(arg_eff, namer);
            let ret_eff = format_ret_row_inline(ret_eff, namer);
            let rendered = match (arg_eff, ret_eff) {
                (None, None) => format!("{arg} -> {ret}"),
                (Some(ae), None) => format!("{arg} [{ae}] -> {ret}"),
                (None, Some(re)) => format!("{arg} -> [{re}] {ret}"),
                (Some(ae), Some(re)) => format!("{arg} [{ae}] -> [{re}] {ret}"),
            };
            if needs_paren {
                format!("({rendered})")
            } else {
                rendered
            }
        }
        Type::Record(fields) => {
            let fields = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}{}: {}",
                        field.name.0,
                        if field.optional { "?" } else { "" },
                        format_type_inner(&field.value, namer, false)
                    )
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!("{{{fields}}}")
        }
        Type::RecordTailSpread { fields, tail } => {
            let mut items = fields
                .iter()
                .map(|field| {
                    format!(
                        "{}{}: {}",
                        field.name.0,
                        if field.optional { "?" } else { "" },
                        format_type_inner(&field.value, namer, false)
                    )
                })
                .collect::<Vec<_>>();
            items.push(format!("..{}", format_type_inner(tail, namer, false)));
            format!("{{{}}}", items.join(", "))
        }
        Type::RecordHeadSpread { tail, fields } => {
            let mut items = vec![format!("..{}", format_type_inner(tail, namer, false))];
            items.extend(fields.iter().map(|field| {
                format!(
                    "{}{}: {}",
                    field.name.0,
                    if field.optional { "?" } else { "" },
                    format_type_inner(&field.value, namer, false)
                )
            }));
            format!("{{{}}}", items.join(", "))
        }
        Type::Variant(items) => {
            let items = items
                .iter()
                .map(|(name, payloads)| {
                    if payloads.is_empty() {
                        name.0.clone()
                    } else {
                        format!(
                            "{} {}",
                            name.0,
                            payloads
                                .iter()
                                .map(|payload| format_type_inner(payload, namer, true))
                                .collect::<Vec<_>>()
                                .join(" ")
                        )
                    }
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!(":{{{items}}}")
        }
        Type::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| format_type_inner(item, namer, false))
                .collect::<Vec<_>>()
                .join(", ");
            format!("({items})")
        }
        Type::Row(items, tail) => {
            let items = items
                .iter()
                .map(|item| format_type_inner(item, namer, false))
                .collect::<Vec<_>>();
            if matches!(tail.as_ref(), Type::Bot) {
                format!("[{};]", items.join(", "))
            } else {
                let tail = format_type_inner(tail, namer, false);
                if items.is_empty() {
                    format!("[; {tail}]")
                } else {
                    format!("[{}; {tail}]", items.join(", "))
                }
            }
        }
        Type::Union(items) => {
            let joined = items
                .iter()
                .map(|item| format_type_inner(item, namer, true))
                .collect::<Vec<_>>()
                .join(" | ");
            if needs_paren {
                format!("({joined})")
            } else {
                joined
            }
        }
        Type::Inter(items) => {
            let joined = items
                .iter()
                .map(|item| format_type_inner(item, namer, true))
                .collect::<Vec<_>>()
                .join(" & ");
            if needs_paren {
                format!("({joined})")
            } else {
                joined
            }
        }
        Type::Rec(tv, body) => {
            let name = namer.name(tv.0);
            let body = format_type_inner(body, namer, false);
            format!("rec {{{name} = {body}}}. {name}")
        }
        Type::Bot => "⊥".to_string(),
        Type::Top => "⊤".to_string(),
    }
}

fn format_row_inline(ty: &Type, namer: &mut VarNamer<'_>) -> Option<String> {
    if is_empty_row(ty) {
        return None;
    }
    match ty {
        Type::Bot | Type::Top => None,
        Type::Union(items) => {
            let mut parts = items
                .iter()
                .filter_map(|item| format_row_inline(item, namer))
                .collect::<Vec<_>>();
            parts.sort();
            parts.dedup();
            if parts.is_empty() {
                None
            } else {
                Some(parts.join(", "))
            }
        }
        Type::Row(items, tail) => {
            let items = items
                .iter()
                .map(|item| format_type_inner(item, namer, false))
                .collect::<Vec<_>>();
            if is_empty_row(tail) {
                return if items.is_empty() {
                    None
                } else {
                    Some(items.join(", "))
                };
            }
            match tail.as_ref() {
                Type::Bot | Type::Top => {
                    if items.is_empty() {
                        None
                    } else {
                        Some(items.join(", "))
                    }
                }
                _ => {
                    let tail = format_row_inline(tail, namer)
                        .unwrap_or_else(|| format_type_inner(tail, namer, false));
                    if items.is_empty() {
                        Some(tail)
                    } else {
                        Some(format!("{}; {tail}", items.join(", ")))
                    }
                }
            }
        }
        _ => Some(format_type_inner(ty, namer, false)),
    }
}

fn format_ret_row_inline(ty: &Type, namer: &mut VarNamer<'_>) -> Option<String> {
    match ty {
        Type::Top => Some("⊤".to_string()),
        Type::Row(items, tail) if matches!(tail.as_ref(), Type::Top) => {
            let items = items
                .iter()
                .map(|item| format_type_inner(item, namer, false))
                .collect::<Vec<_>>();
            if items.is_empty() {
                Some("⊤".to_string())
            } else {
                Some(format!("{}; ⊤", items.join(", ")))
            }
        }
        _ => format_row_inline(ty, namer),
    }
}

fn format_compact_bounds(bounds: &CompactBounds, namer: &mut VarNamer<'_>) -> String {
    let normalized = normalize_format_bounds(bounds.clone());
    let bounds = &normalized;
    if let Some(rendered) = format_compact_bounds_with_center(bounds, namer) {
        return rendered;
    }
    let lower_empty = is_empty_compact(&bounds.lower);
    let upper_empty = is_empty_compact(&bounds.upper);
    match (lower_empty, upper_empty) {
        (true, true) => bounds
            .self_var
            .map(|tv| namer.name(tv.0))
            .unwrap_or_else(|| "_".to_string()),
        (false, true) => format_compact_type(&bounds.lower, namer, false),
        (true, false) => format!("_ <: {}", format_compact_type(&bounds.upper, namer, false)),
        (false, false) => {
            if let (Some(lower_vars), Some(upper_vars)) = (
                compact_var_set(&bounds.lower),
                compact_var_set(&bounds.upper),
            ) {
                if lower_vars.is_subset(&upper_vars) {
                    return format_compact_type(&bounds.lower, namer, false);
                }
            }
            let lower = format_compact_type(&bounds.lower, namer, false);
            let upper = format_compact_type(&bounds.upper, namer, false);
            if lower == upper {
                lower
            } else {
                format!("{lower} <: {upper}")
            }
        }
    }
}

pub(crate) fn format_compact_role_constraint_arg_with_namer(
    arg: &CompactBounds,
    namer: &mut VarNamer<'_>,
) -> String {
    let normalized = normalize_format_bounds(arg.clone());
    let arg = &normalized;
    if let Some(rendered) = format_compact_bounds_with_center(arg, namer) {
        return rendered;
    }
    match (is_empty_compact(&arg.lower), is_empty_compact(&arg.upper)) {
        (true, true) => "_".to_string(),
        (false, true) => format_compact_type(&arg.lower, namer, false),
        (true, false) => format_compact_type_with_join(&arg.upper, namer, false, " & "),
        (false, false) if arg.lower == arg.upper => format_compact_type(&arg.lower, namer, false),
        (false, false) => format_compact_interval_arg(&arg.lower, &arg.upper, namer),
    }
}

fn format_compact_bounds_with_center(
    bounds: &CompactBounds,
    namer: &mut VarNamer<'_>,
) -> Option<String> {
    let shared = shared_center_vars(bounds);
    if shared.is_empty() {
        return None;
    }
    let mut lower = bounds.lower.clone();
    let mut upper = bounds.upper.clone();
    for tv in &shared {
        lower.vars.remove(tv);
        upper.vars.remove(tv);
    }

    let lower_empty = is_empty_compact(&lower);
    let upper_empty = is_empty_compact(&upper);

    if !lower_empty && !upper_empty && lower == upper && has_non_var_shape(&lower) {
        return Some(format_compact_type(&lower, namer, false));
    }

    let center = format_shared_center_vars(&shared, namer);

    match (lower_empty, upper_empty) {
        (true, true) => Some(center),
        (false, true) => Some(format!(
            "{} | {center}",
            format_compact_type(&lower, namer, false)
        )),
        (true, false) => Some(format!(
            "{center} & {}",
            format_compact_type_with_join(&upper, namer, false, " & ")
        )),
        (false, false) => Some(format!(
            "{} | {center} & {}",
            format_compact_type(&lower, namer, false),
            format_compact_type_with_join(&upper, namer, false, " & ")
        )),
    }
}

fn shared_center_vars(bounds: &CompactBounds) -> Vec<TypeVar> {
    let mut shared = bounds
        .lower
        .vars
        .intersection(&bounds.upper.vars)
        .copied()
        .collect::<Vec<_>>();
    shared.sort_by_key(|tv| tv.0);
    shared
}

fn format_shared_center_vars(shared: &[TypeVar], namer: &mut VarNamer<'_>) -> String {
    shared
        .iter()
        .map(|tv| namer.name(tv.0))
        .collect::<Vec<_>>()
        .join(" | ")
}

fn format_compact_type(ty: &CompactType, namer: &mut VarNamer<'_>, needs_paren: bool) -> String {
    format_compact_type_with_join(ty, namer, needs_paren, " | ")
}

fn format_compact_type_with_join(
    ty: &CompactType,
    namer: &mut VarNamer<'_>,
    needs_paren: bool,
    join: &str,
) -> String {
    let mut parts = Vec::new();

    let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    parts.extend(vars.into_iter().map(|tv| namer.name(tv.0)));

    let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
    prims.sort_by(|a, b| path_string(a).cmp(&path_string(b)));
    let prim_strings: Vec<String> = prims.iter().map(|path| namer.render_path(path)).collect();
    parts.extend(prim_strings);

    let mut cons = ty.cons.clone();
    cons.sort_by(|a, b| path_string(&a.path).cmp(&path_string(&b.path)));
    parts.extend(cons.into_iter().map(|con| format_compact_con(&con, namer)));

    parts.extend(ty.funs.iter().map(|fun| format_compact_fun(fun, namer)));
    parts.extend(
        ty.records
            .iter()
            .map(|record| format_compact_record(record, namer)),
    );
    parts.extend(
        ty.record_spreads
            .iter()
            .map(|spread| format_compact_record_spread(spread, namer)),
    );
    parts.extend(
        ty.variants
            .iter()
            .map(|variant| format_compact_variant(variant, namer)),
    );
    parts.extend(ty.tuples.iter().map(|tuple| {
        let items = tuple
            .iter()
            .map(|item| format_compact_type(item, namer, false))
            .collect::<Vec<_>>();
        format!("({})", items.join(", "))
    }));
    parts.extend(ty.rows.iter().map(|row| format_compact_row(row, namer)));

    if parts.is_empty() {
        return "_".to_string();
    }
    if parts.len() == 1 {
        return parts.remove(0);
    }
    let joined = parts.join(join);
    if needs_paren {
        format!("({joined})")
    } else {
        joined
    }
}

fn format_compact_interval_arg(
    lower: &CompactType,
    upper: &CompactType,
    namer: &mut VarNamer<'_>,
) -> String {
    let mut lower_parts = format_compact_type_parts(lower, namer);
    let upper_parts = format_compact_type_parts(upper, namer);
    if lower_parts.is_empty() {
        return upper_parts.join(" & ");
    }
    if upper_parts.is_empty() {
        return lower_parts.join(" | ");
    }

    let shared = lower_parts
        .iter()
        .rposition(|part| upper_parts.iter().any(|upper| upper == part));
    if let Some(index) = shared {
        let shared_part = lower_parts.remove(index);
        let mut intersection = vec![shared_part.clone()];
        intersection.extend(upper_parts.into_iter().filter(|part| part != &shared_part));
        let intersection = if intersection.len() == 1 {
            shared_part
        } else {
            format!("{} & {}", shared_part, intersection[1..].join(" & "))
        };
        if lower_parts.is_empty() {
            intersection
        } else {
            format!("{} | {}", lower_parts.join(" | "), intersection)
        }
    } else {
        format!("{} <: {}", lower_parts.join(" | "), upper_parts.join(" & "))
    }
}

fn format_compact_type_parts(ty: &CompactType, namer: &mut VarNamer<'_>) -> Vec<String> {
    let mut parts = Vec::new();

    let mut vars = ty.vars.iter().copied().collect::<Vec<_>>();
    vars.sort_by_key(|tv| tv.0);
    parts.extend(vars.into_iter().map(|tv| namer.name(tv.0)));

    let mut prims = ty.prims.iter().cloned().collect::<Vec<_>>();
    prims.sort_by(|a, b| path_string(a).cmp(&path_string(b)));
    let prim_strings: Vec<String> = prims.iter().map(|path| namer.render_path(path)).collect();
    parts.extend(prim_strings);

    let mut cons = ty.cons.clone();
    cons.sort_by(|a, b| path_string(&a.path).cmp(&path_string(&b.path)));
    parts.extend(cons.into_iter().map(|con| format_compact_con(&con, namer)));

    parts.extend(ty.funs.iter().map(|fun| format_compact_fun(fun, namer)));
    parts.extend(
        ty.records
            .iter()
            .map(|record| format_compact_record(record, namer)),
    );
    parts.extend(
        ty.record_spreads
            .iter()
            .map(|spread| format_compact_record_spread(spread, namer)),
    );
    parts.extend(
        ty.variants
            .iter()
            .map(|variant| format_compact_variant(variant, namer)),
    );
    parts.extend(ty.tuples.iter().map(|tuple| {
        let items = tuple
            .iter()
            .map(|item| format_compact_type(item, namer, false))
            .collect::<Vec<_>>();
        format!("({})", items.join(", "))
    }));
    parts.extend(ty.rows.iter().map(|row| format_compact_row(row, namer)));

    parts
}

fn format_compact_con(con: &CompactCon, namer: &mut VarNamer<'_>) -> String {
    let name = namer.render_path(&con.path);
    if con.args.is_empty() {
        return name;
    }
    let args = con
        .args
        .iter()
        .map(|arg| format_compact_bounds(arg, namer))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{name}<{args}>")
}

fn format_compact_fun(fun: &CompactFun, namer: &mut VarNamer<'_>) -> String {
    let arg = format_compact_type(&fun.arg, namer, true);
    let ret = format_compact_type(&fun.ret, namer, false);
    let arg_eff = format_compact_row_inline(&fun.arg_eff, namer);
    let ret_eff = format_compact_row_inline(&fun.ret_eff, namer);
    match (arg_eff, ret_eff) {
        (None, None) => format!("{arg} -> {ret}"),
        (Some(ae), None) => format!("{arg} [{ae}] -> {ret}"),
        (None, Some(re)) => format!("{arg} -> [{re}] {ret}"),
        (Some(ae), Some(re)) => format!("{arg} [{ae}] -> [{re}] {ret}"),
    }
}

fn format_compact_record(record: &CompactRecord, namer: &mut VarNamer<'_>) -> String {
    let fields = record
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}{}: {}",
                field.name.0,
                if field.optional { "?" } else { "" },
                format_compact_type(&field.value, namer, false)
            )
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!("{{{fields}}}")
}

fn format_compact_record_spread(spread: &CompactRecordSpread, namer: &mut VarNamer<'_>) -> String {
    let fields = spread
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}{}: {}",
                field.name.0,
                if field.optional { "?" } else { "" },
                format_compact_type(&field.value, namer, false)
            )
        })
        .collect::<Vec<_>>();
    let tail = format_compact_type(&spread.tail, namer, false);
    if spread.tail_wins {
        let mut items = fields;
        items.push(format!("..{tail}"));
        format!("{{{}}}", items.join(", "))
    } else {
        let mut items = vec![format!("..{tail}")];
        items.extend(fields);
        format!("{{{}}}", items.join(", "))
    }
}

fn format_compact_variant(variant: &CompactVariant, namer: &mut VarNamer<'_>) -> String {
    let items = variant
        .items
        .iter()
        .map(|(name, payloads)| {
            if payloads.is_empty() {
                name.0.clone()
            } else {
                format!(
                    "{} {}",
                    name.0,
                    payloads
                        .iter()
                        .map(|payload| format_compact_type(payload, namer, true))
                        .collect::<Vec<_>>()
                        .join(" ")
                )
            }
        })
        .collect::<Vec<_>>()
        .join(", ");
    format!(":{{{items}}}")
}

fn format_compact_row(row: &CompactRow, namer: &mut VarNamer<'_>) -> String {
    let items = row
        .items
        .iter()
        .map(|item| format_compact_type(item, namer, false))
        .collect::<Vec<_>>();
    if is_empty_compact(&row.tail) || is_explicit_empty_row_compact(&row.tail) {
        format!("[{};]", items.join(", "))
    } else {
        let tail = format_compact_type(&row.tail, namer, false);
        if items.is_empty() {
            format!("[; {tail}]")
        } else {
            format!("[{}; {tail}]", items.join(", "))
        }
    }
}

fn format_compact_row_inline(ty: &CompactType, namer: &mut VarNamer<'_>) -> Option<String> {
    match ty.rows.as_slice() {
        [] if is_empty_compact(ty) => None,
        [row]
            if ty.vars.is_empty()
                && ty.prims.is_empty()
                && ty.cons.is_empty()
                && ty.funs.is_empty()
                && ty.records.is_empty()
                && ty.variants.is_empty()
                && ty.tuples.is_empty() =>
        {
            let items = row
                .items
                .iter()
                .map(|item| format_compact_type(item, namer, false))
                .collect::<Vec<_>>();
            if is_empty_compact(&row.tail) || is_explicit_empty_row_compact(&row.tail) {
                if items.is_empty() {
                    None
                } else {
                    Some(items.join(", "))
                }
            } else {
                let tail = format_compact_type(&row.tail, namer, false);
                if items.is_empty() {
                    Some(tail)
                } else {
                    Some(format!("{}; {tail}", items.join(", ")))
                }
            }
        }
        _ => Some(format_compact_type(ty, namer, false)),
    }
}

fn normalize_format_bounds(mut bounds: CompactBounds) -> CompactBounds {
    normalize_format_compact_type_in_place(&mut bounds.lower);
    normalize_format_compact_type_in_place(&mut bounds.upper);
    bounds
}

fn normalize_format_compact_type_in_place(ty: &mut CompactType) {
    for con in &mut ty.cons {
        for arg in &mut con.args {
            *arg = normalize_format_bounds(arg.clone());
        }
    }
    for fun in &mut ty.funs {
        normalize_format_compact_type_in_place(&mut fun.arg);
        normalize_format_compact_type_in_place(&mut fun.arg_eff);
        normalize_format_compact_type_in_place(&mut fun.ret_eff);
        normalize_format_compact_type_in_place(&mut fun.ret);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            normalize_format_compact_type_in_place(&mut field.value);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            normalize_format_compact_type_in_place(&mut field.value);
        }
        normalize_format_compact_type_in_place(&mut spread.tail);
    }
    for variant in &mut ty.variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                normalize_format_compact_type_in_place(payload);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in tuple {
            normalize_format_compact_type_in_place(item);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            normalize_format_compact_type_in_place(item);
        }
        normalize_format_compact_type_in_place(&mut row.tail);
        if is_explicit_empty_row_compact(&row.tail) {
            row.tail = Box::new(CompactType::default());
        }
    }
}

fn normalize_render_bounds(mut bounds: CompactBounds) -> CompactBounds {
    render_absorb_upper_vars_from_row_lower(&mut bounds);
    bounds
}

fn render_absorb_upper_vars_from_row_lower(bounds: &mut CompactBounds) {
    let Some(upper) = compact_var_set(&bounds.upper) else {
        return;
    };
    if upper.is_empty()
        || bounds.lower.rows.is_empty()
        || !bounds.lower.prims.is_empty()
        || !bounds.lower.cons.is_empty()
        || !bounds.lower.funs.is_empty()
        || !bounds.lower.records.is_empty()
        || !bounds.lower.record_spreads.is_empty()
        || !bounds.lower.variants.is_empty()
        || !bounds.lower.tuples.is_empty()
        || !upper.is_subset(&bounds.lower.vars)
    {
        return;
    }
    for tv in upper {
        if bounds.self_var == Some(tv) {
            continue;
        }
        bounds.lower.vars.remove(&tv);
        bounds.upper.vars.remove(&tv);
    }
}

fn compact_var_set(ty: &CompactType) -> Option<HashSet<TypeVar>> {
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

fn should_hash_cons_type(ty: &CompactType) -> bool {
    !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
}

fn compact_type_key(ty: &CompactType) -> String {
    let mut vars = ty.vars.iter().map(|tv| tv.0).collect::<Vec<_>>();
    vars.sort_unstable();
    let mut prims = ty.prims.iter().map(path_string).collect::<Vec<_>>();
    prims.sort();
    let mut cons = ty.cons.iter().map(compact_con_key).collect::<Vec<_>>();
    cons.sort();
    let mut funs = ty.funs.iter().map(compact_fun_key).collect::<Vec<_>>();
    funs.sort();
    let mut records = ty
        .records
        .iter()
        .map(compact_record_key)
        .collect::<Vec<_>>();
    records.sort();
    let mut record_spreads = ty
        .record_spreads
        .iter()
        .map(compact_record_spread_key)
        .collect::<Vec<_>>();
    record_spreads.sort();
    let mut variants = ty
        .variants
        .iter()
        .map(compact_variant_key)
        .collect::<Vec<_>>();
    variants.sort();
    let mut tuples = ty
        .tuples
        .iter()
        .map(|tuple| compact_tuple_key(tuple))
        .collect::<Vec<_>>();
    tuples.sort();
    let mut rows = ty.rows.iter().map(compact_row_key).collect::<Vec<_>>();
    rows.sort();
    format!(
        "T[v={vars:?};p={prims:?};c={cons:?};f={funs:?};r={records:?};rs={record_spreads:?};vnt={variants:?};t={tuples:?};rw={rows:?}]"
    )
}

fn compact_bounds_key(bounds: &CompactBounds) -> String {
    format!(
        "B[{}<:{}]",
        compact_type_key(&bounds.lower),
        compact_type_key(&bounds.upper)
    )
}

fn compact_con_key(con: &CompactCon) -> String {
    let args = con.args.iter().map(compact_bounds_key).collect::<Vec<_>>();
    format!("{}<{args:?}>", path_string(&con.path))
}

fn compact_fun_key(fun: &CompactFun) -> String {
    format!(
        "({}->{}/{})",
        compact_type_key(&fun.arg),
        compact_type_key(&fun.arg_eff),
        compact_type_key(&fun.ret_eff),
    ) + &format!("->{}", compact_type_key(&fun.ret))
}

fn compact_record_key(record: &CompactRecord) -> String {
    let mut fields = record
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}{}:{}",
                field.name.0,
                if field.optional { "?" } else { "" },
                compact_type_key(&field.value)
            )
        })
        .collect::<Vec<_>>();
    fields.sort();
    format!("{{{}}}", fields.join(","))
}

fn compact_record_spread_key(spread: &CompactRecordSpread) -> String {
    let mut fields = spread
        .fields
        .iter()
        .map(|field| {
            format!(
                "{}{}:{}",
                field.name.0,
                if field.optional { "?" } else { "" },
                compact_type_key(&field.value)
            )
        })
        .collect::<Vec<_>>();
    fields.sort();
    let tail = compact_type_key(&spread.tail);
    if spread.tail_wins {
        fields.push(format!("..{tail}"));
    } else {
        fields.insert(0, format!("..{tail}"));
    }
    format!("{{{}}}", fields.join(","))
}

fn compact_variant_key(variant: &CompactVariant) -> String {
    let mut items = variant
        .items
        .iter()
        .map(|(name, payloads)| {
            let payloads = payloads.iter().map(compact_type_key).collect::<Vec<_>>();
            format!("{}({})", name.0, payloads.join(","))
        })
        .collect::<Vec<_>>();
    items.sort();
    format!("[{}]", items.join("|"))
}

fn compact_tuple_key(tuple: &[CompactType]) -> String {
    let items = tuple.iter().map(compact_type_key).collect::<Vec<_>>();
    format!("({})", items.join(","))
}

fn compact_row_key(row: &CompactRow) -> String {
    let mut items = row.items.iter().map(compact_type_key).collect::<Vec<_>>();
    items.sort();
    format!("[{};{}]", items.join(","), compact_type_key(&row.tail))
}

fn root_non_fun_parts_empty(ty: &CompactType) -> bool {
    ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn common_compact_type(lhs: &CompactType, rhs: &CompactType) -> Option<CompactType> {
    Some(CompactType {
        vars: lhs.vars.intersection(&rhs.vars).copied().collect(),
        prims: lhs.prims.intersection(&rhs.prims).cloned().collect(),
        cons: common_compact_cons(&lhs.cons, &rhs.cons),
        funs: lhs
            .funs
            .iter()
            .filter(|item| rhs.funs.contains(item))
            .cloned()
            .collect(),
        records: lhs
            .records
            .iter()
            .filter(|item| rhs.records.contains(item))
            .cloned()
            .collect(),
        record_spreads: lhs
            .record_spreads
            .iter()
            .filter(|item| rhs.record_spreads.contains(item))
            .cloned()
            .collect(),
        variants: lhs
            .variants
            .iter()
            .filter(|item| rhs.variants.contains(item))
            .cloned()
            .collect(),
        tuples: lhs
            .tuples
            .iter()
            .filter(|item| rhs.tuples.contains(item))
            .cloned()
            .collect(),
        rows: lhs
            .rows
            .iter()
            .filter(|item| rhs.rows.contains(item))
            .cloned()
            .collect(),
    })
}

fn common_compact_cons(lhs: &[CompactCon], rhs: &[CompactCon]) -> Vec<CompactCon> {
    let mut out = Vec::new();
    for lhs_con in lhs {
        for rhs_con in rhs {
            if lhs_con.path != rhs_con.path || lhs_con.args.len() != rhs_con.args.len() {
                continue;
            }
            let args = lhs_con
                .args
                .iter()
                .zip(&rhs_con.args)
                .map(|(lhs_arg, rhs_arg)| common_compact_bounds(lhs_arg, rhs_arg))
                .collect::<Vec<_>>();
            if args.iter().all(compact_bounds_has_surface) {
                let con = CompactCon {
                    path: lhs_con.path.clone(),
                    args,
                };
                if !out.contains(&con) {
                    out.push(con);
                }
            }
        }
    }
    out
}

fn common_compact_bounds(lhs: &CompactBounds, rhs: &CompactBounds) -> CompactBounds {
    CompactBounds {
        self_var: (lhs.self_var == rhs.self_var)
            .then_some(lhs.self_var)
            .flatten(),
        lower: common_compact_type(&lhs.lower, &rhs.lower).unwrap_or_default(),
        upper: common_compact_type(&lhs.upper, &rhs.upper).unwrap_or_default(),
    }
}

fn compact_bounds_has_surface(bounds: &CompactBounds) -> bool {
    bounds.self_var.is_some()
        || !is_empty_compact(&bounds.lower)
        || !is_empty_compact(&bounds.upper)
}

fn is_empty_compact(ty: &CompactType) -> bool {
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

fn has_non_var_shape(ty: &CompactType) -> bool {
    !ty.prims.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
}

fn has_effect_row_surface(ty: &CompactType) -> bool {
    !ty.prims.is_empty() || !ty.cons.is_empty() || !ty.rows.is_empty()
}

fn has_non_var_shape_outside_common(ty: &CompactType, common: &CompactType) -> bool {
    ty.prims.iter().any(|item| !common.prims.contains(item))
        || ty.cons.iter().any(|item| {
            !common
                .cons
                .iter()
                .any(|common| compact_con_covers(common, item))
        })
        || ty.funs.iter().any(|item| !common.funs.contains(item))
        || ty.records.iter().any(|item| !common.records.contains(item))
        || ty
            .record_spreads
            .iter()
            .any(|item| !common.record_spreads.contains(item))
        || ty
            .variants
            .iter()
            .any(|item| !common.variants.contains(item))
        || ty.tuples.iter().any(|item| !common.tuples.contains(item))
        || ty.rows.iter().any(|item| !common.rows.contains(item))
}

fn compact_con_covers(common: &CompactCon, item: &CompactCon) -> bool {
    common.path == item.path
        && common.args.len() == item.args.len()
        && common
            .args
            .iter()
            .zip(&item.args)
            .all(|(common, item)| compact_bounds_cover(common, item))
}

fn compact_bounds_cover(common: &CompactBounds, item: &CompactBounds) -> bool {
    compact_type_covers(&common.lower, &item.lower)
        && compact_type_covers(&common.upper, &item.upper)
}

fn compact_type_covers(common: &CompactType, item: &CompactType) -> bool {
    common.vars.is_subset(&item.vars)
        && common.prims.is_subset(&item.prims)
        && common.cons.iter().all(|common_con| {
            item.cons
                .iter()
                .any(|item_con| compact_con_covers(common_con, item_con))
        })
        && common.funs.iter().all(|fun| item.funs.contains(fun))
        && common
            .records
            .iter()
            .all(|record| item.records.contains(record))
        && common
            .record_spreads
            .iter()
            .all(|spread| item.record_spreads.contains(spread))
        && common
            .variants
            .iter()
            .all(|variant| item.variants.contains(variant))
        && common
            .tuples
            .iter()
            .all(|tuple| item.tuples.contains(tuple))
        && common.rows.iter().all(|row| item.rows.contains(row))
}

fn is_explicit_empty_row_compact(ty: &CompactType) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && matches!(
            ty.rows.as_slice(),
            [CompactRow { items, tail }] if items.is_empty() && is_empty_compact(tail)
        )
}

fn is_var_only_compact(ty: &CompactType) -> bool {
    ty.vars.len() == 1
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn is_empty_row(ty: &Type) -> bool {
    matches!(ty, Type::Row(items, tail) if items.is_empty() && matches!(tail.as_ref(), Type::Bot))
        || matches!(ty, Type::Rec(tv, body)
            if matches!(body.as_ref(), Type::Row(items, tail)
                if items.is_empty() && matches!(tail.as_ref(), Type::Var(inner) if inner == tv)))
}

fn is_empty_effect_placeholder(ty: &Type) -> bool {
    matches!(ty, Type::Bot | Type::Top) || is_empty_row(ty)
}

fn path_string(path: &Path) -> String {
    path.segments
        .iter()
        .map(|name| display_name_segment(name.0.as_str()))
        .collect::<Vec<_>>()
        .join("::")
}

fn display_name_segment(name: &str) -> &str {
    name
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use crate::ids::TypeVar;
    use crate::simplify::compact::{
        CompactBounds, CompactCon, CompactFun, CompactRow, CompactType, CompactTypeScheme,
        merge_compact_types,
    };
    use crate::symbols::{Name, Path};

    use super::{VarNamer, format_coalesced_scheme, format_compact_bounds};

    #[test]
    fn compact_bounds_format_closes_nested_empty_row_tail() {
        let effect_tail = TypeVar(10);
        let value = TypeVar(11);
        let item = CompactType {
            cons: vec![CompactCon {
                path: path(&["std", "var", "var"]),
                args: vec![CompactBounds {
                    self_var: None,
                    lower: var_type(value),
                    upper: var_type(value),
                }],
            }],
            ..CompactType::default()
        };
        let closed_row = CompactType {
            rows: vec![CompactRow {
                items: vec![item.clone()],
                tail: Box::new(CompactType::default()),
            }],
            ..CompactType::default()
        };
        let explicit_empty_row = CompactType {
            rows: vec![CompactRow {
                items: Vec::new(),
                tail: Box::new(CompactType::default()),
            }],
            ..CompactType::default()
        };
        let open_to_empty_row = CompactType {
            rows: vec![CompactRow {
                items: vec![item],
                tail: Box::new(explicit_empty_row),
            }],
            ..CompactType::default()
        };
        let bounds = CompactBounds {
            self_var: None,
            lower: merge_var_part(closed_row, effect_tail),
            upper: merge_var_part(open_to_empty_row, effect_tail),
        };

        let rendered = format_compact_bounds(&bounds, &mut VarNamer::default());

        assert_eq!(rendered, "[std::var::var<α>;]");
    }

    #[test]
    fn coalesced_scheme_keeps_surface_effect_when_local_effect_is_stripped() {
        let value = TypeVar(1);
        let tail = TypeVar(2);
        let ret_alias = TypeVar(3);
        let err_alias = TypeVar(4);
        let parse_item = con_type(
            &["parse"],
            vec![
                same_bounds(prim_type("int")),
                same_bounds(prim_type("str_error")),
            ],
        );
        let cut_item = con_type(&["&cut#test"], vec![same_bounds(prim_type("bool"))]);
        let lower_arg_eff = merge_var_part(
            row_type(vec![parse_item.clone(), cut_item], CompactType::default()),
            tail,
        );
        let upper_arg_eff =
            merge_var_part(row_type(vec![parse_item], CompactType::default()), tail);
        let lower_ret = merge_var_part(
            con_type(
                &["result"],
                vec![
                    same_bounds(var_type(value)),
                    CompactBounds {
                        self_var: None,
                        lower: merge_compact_types(
                            true,
                            var_type(err_alias),
                            prim_type("str_error"),
                        ),
                        upper: prim_type("str_error"),
                    },
                ],
            ),
            ret_alias,
        );
        let upper_ret = merge_var_part(
            con_type(
                &["result"],
                vec![
                    same_bounds(var_type(value)),
                    same_bounds(prim_type("str_error")),
                ],
            ),
            ret_alias,
        );
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: fun_type(var_type(value), lower_arg_eff, lower_ret),
                upper: fun_type(var_type(value), upper_arg_eff, upper_ret),
            },
            rec_vars: Default::default(),
        };

        let rendered = format_coalesced_scheme(&scheme);

        assert_eq!(
            rendered,
            "α [parse<int, str_error>; β] -> result<α, str_error>"
        );
    }

    fn merge_var_part(mut ty: CompactType, tv: TypeVar) -> CompactType {
        ty.vars.insert(tv);
        ty
    }

    fn var_type(tv: TypeVar) -> CompactType {
        CompactType {
            vars: HashSet::from([tv]),
            ..CompactType::default()
        }
    }

    fn prim_type(name: &str) -> CompactType {
        CompactType {
            prims: HashSet::from([path(&[name])]),
            ..CompactType::default()
        }
    }

    fn con_type(path_segments: &[&str], args: Vec<CompactBounds>) -> CompactType {
        CompactType {
            cons: vec![CompactCon {
                path: path(path_segments),
                args,
            }],
            ..CompactType::default()
        }
    }

    fn same_bounds(ty: CompactType) -> CompactBounds {
        CompactBounds {
            self_var: None,
            lower: ty.clone(),
            upper: ty,
        }
    }

    fn row_type(items: Vec<CompactType>, tail: CompactType) -> CompactType {
        CompactType {
            rows: vec![CompactRow {
                items,
                tail: Box::new(tail),
            }],
            ..CompactType::default()
        }
    }

    fn fun_type(arg: CompactType, arg_eff: CompactType, ret: CompactType) -> CompactType {
        CompactType {
            funs: vec![CompactFun {
                arg,
                arg_eff,
                ret_eff: CompactType::default(),
                ret,
            }],
            ..CompactType::default()
        }
    }

    fn path(segments: &[&str]) -> Path {
        Path {
            segments: segments
                .iter()
                .map(|segment| Name((*segment).to_string()))
                .collect(),
        }
    }
}
