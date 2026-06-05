use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use serde::{Deserialize, Serialize};

mod analysis;
mod polarity;
mod representative;

use crate::ids::TypeVar;
use crate::solve::effect_row::normalize_rewritten_bounds;
use crate::symbols::Path;
use crate::types::RecordField;

use super::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRow, CompactType,
    CompactTypeScheme, CompactVariant, coalesce_root_function_interval_effect_residuals,
    merge_compact_bounds, merge_compact_types, normalize_compact_scheme_rows,
};
use super::polar::{apply_polar_variable_removal, rewrite_polar_occurrences};
use super::role_constraints::rewrite_role_constraints_with_role_arg_inputs;
use analysis::{
    analyze_co_occurrences_with_role_constraints,
    analyze_co_occurrences_with_role_constraints_for_vars,
};
use polarity::analyze_polar_occurrences_with_role_constraints;
use representative::lower_representatives_for_subst;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CoOccurrences {
    pub positive: HashMap<TypeVar, HashSet<AlongItem>>,
    pub negative: HashMap<TypeVar, HashSet<AlongItem>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum AlongItem {
    Var(TypeVar),
    Exact(ExactKey),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactRoleConstraint {
    pub role: Path,
    pub args: Vec<CompactBounds>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExactKey {
    digest: u64,
    kind: ExactKeyKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) enum ExactKeyKind {
    Other,
    Fun,
    EmptyRow,
    ConcreteRow,
}

pub fn analyze_co_occurrences(scheme: &CompactTypeScheme) -> CoOccurrences {
    analyze_co_occurrences_with_role_constraints(scheme, &[])
}

pub fn coalesce_by_co_occurrence(scheme: &CompactTypeScheme) -> CompactTypeScheme {
    coalesce_by_co_occurrence_with_role_constraints(scheme, &[]).0
}

pub fn coalesce_by_co_occurrence_with_role_constraints(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> (CompactTypeScheme, Vec<CompactRoleConstraint>) {
    let output = coalesce_by_co_occurrence_with_role_constraints_report(scheme, constraints);
    (output.scheme, output.constraints)
}

pub fn coalesce_by_co_occurrence_with_role_constraint_inputs(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    role_arg_inputs: impl Fn(&Path) -> Option<Vec<bool>>,
    var_levels: &HashMap<TypeVar, u32>,
    boundary: u32,
) -> (CompactTypeScheme, Vec<CompactRoleConstraint>) {
    let output = coalesce_by_co_occurrence_with_role_constraints_report_inner(
        scheme,
        constraints,
        &role_arg_inputs,
        std::env::var_os("YULANG_USE_COALESCE_REPRESENTATIVES").is_some(),
        var_levels,
        boundary,
        None,
    );
    (output.scheme, output.constraints)
}

pub fn coalesce_by_co_occurrence_with_role_constraint_inputs_report(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    role_arg_inputs: impl Fn(&Path) -> Option<Vec<bool>>,
    var_levels: &HashMap<TypeVar, u32>,
    boundary: u32,
) -> CoalesceOutput {
    coalesce_by_co_occurrence_with_role_constraints_report_inner(
        scheme,
        constraints,
        &role_arg_inputs,
        std::env::var_os("YULANG_USE_COALESCE_REPRESENTATIVES").is_some(),
        var_levels,
        boundary,
        None,
    )
}

pub(crate) fn coalesce_by_co_occurrence_with_role_constraint_input_candidates_report(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    role_arg_inputs: impl Fn(&Path) -> Option<Vec<bool>>,
    var_levels: &HashMap<TypeVar, u32>,
    boundary: u32,
    candidates: &HashSet<TypeVar>,
) -> CoalesceOutput {
    coalesce_by_co_occurrence_with_role_constraints_report_inner(
        scheme,
        constraints,
        &role_arg_inputs,
        std::env::var_os("YULANG_USE_COALESCE_REPRESENTATIVES").is_some(),
        var_levels,
        boundary,
        Some(candidates),
    )
}

pub fn coalesce_by_co_occurrence_with_role_constraints_report(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> CoalesceOutput {
    coalesce_by_co_occurrence_with_role_constraints_report_inner(
        scheme,
        constraints,
        &no_role_arg_inputs,
        std::env::var_os("YULANG_USE_COALESCE_REPRESENTATIVES").is_some(),
        &HashMap::new(),
        0,
        None,
    )
}

fn no_role_arg_inputs(_: &Path) -> Option<Vec<bool>> {
    None
}

fn coalesce_by_co_occurrence_with_role_constraints_report_inner(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    role_arg_inputs: &dyn Fn(&Path) -> Option<Vec<bool>>,
    use_representatives: bool,
    var_levels: &HashMap<TypeVar, u32>,
    boundary: u32,
    candidates: Option<&HashSet<TypeVar>>,
) -> CoalesceOutput {
    let boundary_candidates = candidates.map_or_else(
        || collect_boundary_coalescence_candidates(scheme, constraints, var_levels, boundary),
        |candidates| {
            candidates
                .iter()
                .copied()
                .filter(|tv| var_levels.get(tv).copied().unwrap_or(u32::MAX) >= boundary)
                .collect::<HashSet<_>>()
        },
    );
    if boundary_candidates.is_empty() {
        let mut scheme = scheme.clone();
        coalesce_root_function_interval_effect_residuals(&mut scheme);
        normalize_compact_scheme_rows(&mut scheme);
        let constraints = rewrite_role_constraints_with_role_arg_inputs(
            &scheme,
            constraints,
            &HashMap::new(),
            role_arg_inputs,
        );
        return CoalesceOutput {
            scheme,
            constraints,
            rounds: Vec::new(),
        };
    }
    let current_scheme = scheme.clone();
    let current_constraints = constraints.to_vec();
    let mut rounds = Vec::new();

    loop {
        let mut polar_analysis =
            analyze_polar_occurrences_with_role_constraints(&current_scheme, &current_constraints);
        let analysis = analyze_co_occurrences_with_role_constraints_for_vars(
            &current_scheme,
            &current_constraints,
            Some(&boundary_candidates),
        );
        let rec_vars = current_scheme.rec_vars.clone();
        let mut all_vars = collect_all_vars(&current_scheme, &analysis);
        all_vars.extend(polar_analysis.positive.iter().copied());
        all_vars.extend(polar_analysis.negative.iter().copied());
        all_vars.sort_by_key(|tv| tv.0);
        all_vars.dedup();
        // 量化されうる変数（level >= boundary）だけを解析対象に残す。外側スコープの変数は
        // 走査しない。情報(analysis/polar_analysis)は全変数のままなので、極性消去でも
        // (false,false) 扱いにならず、外側変数は消されない。
        all_vars.retain(|tv| {
            boundary_candidates.contains(tv)
                && var_levels.get(tv).copied().unwrap_or(u32::MAX) >= boundary
        });
        all_vars.sort_by_key(|tv| std::cmp::Reverse(tv.0));

        let mut subst = HashMap::<TypeVar, Option<TypeVar>>::new();
        rewrite_polar_occurrences(&mut polar_analysis, &subst);
        apply_polar_variable_removal(&all_vars, &polar_analysis, &rec_vars, &mut subst);
        apply_indistinguishable_unification(&all_vars, &analysis, &mut subst);
        apply_sandwich_flattening(&all_vars, &analysis, &mut subst);
        let representatives = lower_representatives_for_subst(
            &current_scheme,
            &current_constraints,
            &rec_vars,
            &subst,
        );
        let use_representatives_now = use_representatives;
        let mut rewritten_scheme = if use_representatives_now {
            rewrite_scheme_with_representatives(
                &current_scheme,
                &rec_vars,
                &subst,
                &representatives,
            )
        } else {
            rewrite_scheme(&current_scheme, &rec_vars, &subst)
        };
        coalesce_root_function_interval_effect_residuals(&mut rewritten_scheme);
        let rewritten_constraints = if use_representatives_now {
            rewrite_constraints_with_representatives(
                &rewritten_scheme,
                &current_constraints,
                &subst,
                &representatives,
                role_arg_inputs,
            )
        } else {
            rewrite_role_constraints_with_role_arg_inputs(
                &rewritten_scheme,
                &current_constraints,
                &subst,
                role_arg_inputs,
            )
        };

        if rewritten_scheme == current_scheme && rewritten_constraints == current_constraints {
            let mut scheme = rewritten_scheme;
            normalize_compact_scheme_rows(&mut scheme);
            return CoalesceOutput {
                scheme,
                constraints: rewritten_constraints,
                rounds,
            };
        }

        if !subst.is_empty() {
            rounds.push(CoalesceRound {
                subst,
                representatives,
            });
        }

        // 固定点ループは廃止。co-occurrence simplification は 1 パスで完了する。
        let mut scheme = rewritten_scheme;
        normalize_compact_scheme_rows(&mut scheme);
        return CoalesceOutput {
            scheme,
            constraints: rewritten_constraints,
            rounds,
        };
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoalesceOutput {
    pub scheme: CompactTypeScheme,
    pub constraints: Vec<CompactRoleConstraint>,
    pub rounds: Vec<CoalesceRound>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoalesceRound {
    pub subst: HashMap<TypeVar, Option<TypeVar>>,
    pub representatives: HashMap<TypeVar, CompactType>,
}

/// subst を辿って代表変数を返す。None(除去済み)に当たったら None。
fn resolve_subst_var(subst: &HashMap<TypeVar, Option<TypeVar>>, v: TypeVar) -> Option<TypeVar> {
    let mut cur = v;
    let mut seen = HashSet::new();
    loop {
        match subst.get(&cur) {
            Some(Some(next)) => {
                if !seen.insert(cur) {
                    return Some(cur);
                }
                cur = *next;
            }
            Some(None) => return None,
            None => return Some(cur),
        }
    }
}

/// a と b を等価として統合する。両者の代表を辿り、番号の大きい方を小さい方へ向ける。
/// 既に同一代表 or どちらか除去済みなら何もしない。常に from.0 > to.0 を保つので循環しない。
fn merge_equiv_vars(subst: &mut HashMap<TypeVar, Option<TypeVar>>, a: TypeVar, b: TypeVar) {
    let (Some(ra), Some(rb)) = (resolve_subst_var(subst, a), resolve_subst_var(subst, b)) else {
        return;
    };
    if ra == rb {
        return;
    }
    let (from, to) = if ra.0 > rb.0 { (ra, rb) } else { (rb, ra) };
    subst.insert(from, Some(to));
}

/// 論文 4.3.1 の indistinguishable unification: α と β が positive(または negative)で
/// 常に共に現れる(互いの always-共起集合に入っている)なら判別不可なので統合する。
/// 向きは merge_equiv_vars が「大きい番号→小さい番号」へ正規化する(sandwich と循環しない)。
fn apply_indistinguishable_unification(
    all_vars: &[TypeVar],
    analysis: &CoOccurrences,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) {
    let all_var_set = all_vars.iter().copied().collect::<HashSet<_>>();
    for &alpha in all_vars {
        merge_mutual_co_occurrence_vars(alpha, &analysis.positive, &all_var_set, subst);
        merge_mutual_co_occurrence_vars(alpha, &analysis.negative, &all_var_set, subst);
    }
}

fn merge_mutual_co_occurrence_vars(
    alpha: TypeVar,
    occurrences: &HashMap<TypeVar, HashSet<AlongItem>>,
    all_vars: &HashSet<TypeVar>,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) {
    let Some(alpha_items) = occurrences.get(&alpha) else {
        return;
    };
    for item in alpha_items {
        let AlongItem::Var(beta) = item else {
            continue;
        };
        if beta.0 >= alpha.0 || !all_vars.contains(beta) {
            continue;
        }
        if matches!(subst.get(&alpha), Some(None)) || matches!(subst.get(beta), Some(None)) {
            continue;
        }
        if occurrences
            .get(beta)
            .is_some_and(|items| items.contains(&AlongItem::Var(alpha)))
        {
            merge_equiv_vars(subst, alpha, *beta);
        }
    }
}

/// 論文 4.3.1 の variable sandwich flattening(polar removal の一般化): 変数 v が
/// ある型 τ(変数 or concrete = AlongItem)と positive・negative の両方で常に共起するなら、
/// v は τ と等価なので消す。τ=Var(w) なら v→w に統合、τ=Exact(concrete) なら v を除去する。
fn apply_sandwich_flattening(
    all_vars: &[TypeVar],
    analysis: &CoOccurrences,
    subst: &mut HashMap<TypeVar, Option<TypeVar>>,
) {
    for &v in all_vars {
        if subst.contains_key(&v) {
            continue;
        }
        let (Some(pos), Some(neg)) = (analysis.positive.get(&v), analysis.negative.get(&v)) else {
            continue;
        };
        let sandwich = pos
            .iter()
            .find(|item| **item != AlongItem::Var(v) && neg.contains(item));
        if let Some(item) = sandwich {
            match item {
                AlongItem::Var(w) => {
                    merge_equiv_vars(subst, v, *w);
                }
                AlongItem::Exact(_) => {
                    subst.insert(v, None);
                }
            }
        }
    }
}

pub(crate) fn rewrite_scheme_with_subst(
    scheme: &CompactTypeScheme,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> CompactTypeScheme {
    rewrite_scheme(scheme, &scheme.rec_vars, subst)
}

fn collect_all_vars(scheme: &CompactTypeScheme, analysis: &CoOccurrences) -> Vec<TypeVar> {
    let mut vars = scheme.rec_vars.keys().copied().collect::<HashSet<_>>();
    collect_vars_in_bounds(&scheme.cty, &mut vars);
    for bounds in scheme.rec_vars.values() {
        collect_vars_in_bounds(bounds, &mut vars);
    }
    vars.extend(analysis.positive.keys().copied());
    vars.extend(analysis.negative.keys().copied());
    vars.into_iter().collect()
}

fn collect_boundary_coalescence_candidates(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    var_levels: &HashMap<TypeVar, u32>,
    boundary: u32,
) -> HashSet<TypeVar> {
    let mut out = HashSet::new();
    collect_boundary_coalescence_candidates_in_bounds(&scheme.cty, var_levels, boundary, &mut out);
    for (&tv, bounds) in &scheme.rec_vars {
        collect_boundary_coalescence_candidate_var(tv, var_levels, boundary, &mut out);
        collect_boundary_coalescence_candidates_in_bounds(bounds, var_levels, boundary, &mut out);
    }
    for constraint in constraints {
        for arg in &constraint.args {
            collect_boundary_coalescence_candidates_in_bounds(arg, var_levels, boundary, &mut out);
        }
    }
    out
}

fn collect_boundary_coalescence_candidates_in_bounds(
    bounds: &CompactBounds,
    var_levels: &HashMap<TypeVar, u32>,
    boundary: u32,
    out: &mut HashSet<TypeVar>,
) {
    if let Some(tv) = bounds.self_var {
        collect_boundary_coalescence_candidate_var(tv, var_levels, boundary, out);
    }
    collect_boundary_coalescence_candidates_in_type(&bounds.lower, var_levels, boundary, out);
    collect_boundary_coalescence_candidates_in_type(&bounds.upper, var_levels, boundary, out);
}

fn collect_boundary_coalescence_candidates_in_type(
    ty: &CompactType,
    var_levels: &HashMap<TypeVar, u32>,
    boundary: u32,
    out: &mut HashSet<TypeVar>,
) {
    for &tv in &ty.vars {
        collect_boundary_coalescence_candidate_var(tv, var_levels, boundary, out);
    }
    for con in &ty.cons {
        for arg in &con.args {
            collect_boundary_coalescence_candidates_in_bounds(arg, var_levels, boundary, out);
        }
    }
    for fun in &ty.funs {
        collect_boundary_coalescence_candidates_in_type(&fun.arg, var_levels, boundary, out);
        collect_boundary_coalescence_candidates_in_type(&fun.arg_eff, var_levels, boundary, out);
        collect_boundary_coalescence_candidates_in_type(&fun.ret_eff, var_levels, boundary, out);
        collect_boundary_coalescence_candidates_in_type(&fun.ret, var_levels, boundary, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_boundary_coalescence_candidates_in_type(
                &field.value,
                var_levels,
                boundary,
                out,
            );
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_boundary_coalescence_candidates_in_type(
                &field.value,
                var_levels,
                boundary,
                out,
            );
        }
        collect_boundary_coalescence_candidates_in_type(&spread.tail, var_levels, boundary, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_boundary_coalescence_candidates_in_type(payload, var_levels, boundary, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_boundary_coalescence_candidates_in_type(item, var_levels, boundary, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_boundary_coalescence_candidates_in_type(item, var_levels, boundary, out);
        }
        collect_boundary_coalescence_candidates_in_type(&row.tail, var_levels, boundary, out);
    }
}

fn collect_boundary_coalescence_candidate_var(
    tv: TypeVar,
    var_levels: &HashMap<TypeVar, u32>,
    boundary: u32,
    out: &mut HashSet<TypeVar>,
) {
    if var_levels.get(&tv).copied().unwrap_or(u32::MAX) >= boundary {
        out.insert(tv);
    }
}

fn collect_vars_in_bounds(bounds: &CompactBounds, out: &mut HashSet<TypeVar>) {
    if let Some(tv) = bounds.self_var {
        out.insert(tv);
    }
    collect_vars_in_type(&bounds.lower, out);
    collect_vars_in_type(&bounds.upper, out);
}

fn collect_vars_in_type(ty: &CompactType, out: &mut HashSet<TypeVar>) {
    out.extend(ty.vars.iter().copied());
    for con in &ty.cons {
        for arg in &con.args {
            collect_vars_in_bounds(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_vars_in_type(&fun.arg, out);
        collect_vars_in_type(&fun.arg_eff, out);
        collect_vars_in_type(&fun.ret_eff, out);
        collect_vars_in_type(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_vars_in_type(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_vars_in_type(&field.value, out);
        }
        collect_vars_in_type(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_vars_in_type(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_vars_in_type(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_vars_in_type(item, out);
        }
        collect_vars_in_type(&row.tail, out);
    }
}

fn rewrite_scheme(
    scheme: &CompactTypeScheme,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> CompactTypeScheme {
    rewrite_scheme_with_representatives(scheme, rec_vars, subst, &HashMap::new())
}

fn rewrite_scheme_with_representatives(
    scheme: &CompactTypeScheme,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
) -> CompactTypeScheme {
    let mut rewritten_rec_vars = HashMap::new();
    let mut rec_vars = rec_vars.iter().collect::<Vec<_>>();
    rec_vars.sort_by_key(|(tv, _)| tv.0);
    for (&tv, bounds) in rec_vars {
        if is_trivial_self_bounds(tv, bounds) {
            continue;
        }
        let Some(key) = rewrite_var(tv, subst) else {
            continue;
        };
        let rewritten = rewrite_bounds_with_representatives(bounds, subst, representatives);
        rewritten_rec_vars
            .entry(key)
            .and_modify(|existing: &mut CompactBounds| {
                *existing = merge_compact_bounds(true, existing.clone(), rewritten.clone());
            })
            .or_insert(rewritten);
    }

    CompactTypeScheme {
        cty: rewrite_bounds_with_representatives(&scheme.cty, subst, representatives),
        rec_vars: rewritten_rec_vars,
    }
}

pub(crate) fn rewrite_bounds(
    bounds: &CompactBounds,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> CompactBounds {
    rewrite_bounds_with_representatives(bounds, subst, &HashMap::new())
}

fn rewrite_constraints_with_representatives(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
    role_arg_inputs: &dyn Fn(&Path) -> Option<Vec<bool>>,
) -> Vec<CompactRoleConstraint> {
    let rewritten = constraints
        .iter()
        .map(|constraint| CompactRoleConstraint {
            role: constraint.role.clone(),
            args: constraint
                .args
                .iter()
                .map(|arg| rewrite_bounds_with_representatives(arg, subst, representatives))
                .collect(),
        })
        .collect::<Vec<_>>();
    rewrite_role_constraints_with_role_arg_inputs(
        scheme,
        &rewritten,
        &HashMap::new(),
        role_arg_inputs,
    )
}

fn rewrite_bounds_with_representatives(
    bounds: &CompactBounds,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
) -> CompactBounds {
    normalize_rewritten_bounds(CompactBounds {
        self_var: bounds.self_var.and_then(|tv| rewrite_var(tv, subst)),
        lower: rewrite_compact_type(&bounds.lower, subst, representatives),
        upper: rewrite_compact_type(&bounds.upper, subst, representatives),
    })
}

fn rewrite_compact_type(
    ty: &CompactType,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
) -> CompactType {
    let mut vars = HashSet::new();
    let mut representative_parts = CompactType::default();
    for &tv in &ty.vars {
        match rewrite_var_with_representative(tv, subst, representatives) {
            VarRewrite::Keep(tv) => {
                vars.insert(tv);
            }
            VarRewrite::Representative(representative) => {
                representative_parts =
                    merge_compact_types(true, representative_parts, representative);
            }
            VarRewrite::Remove => {}
        }
    }
    let cons = ty
        .cons
        .iter()
        .map(|con| CompactCon {
            path: con.path.clone(),
            args: con
                .args
                .iter()
                .map(|arg| rewrite_bounds_with_representatives(arg, subst, representatives))
                .collect(),
        })
        .collect();
    let funs = ty
        .funs
        .iter()
        .map(|fun| CompactFun {
            arg: rewrite_compact_type(&fun.arg, subst, representatives),
            arg_eff: rewrite_compact_type(&fun.arg_eff, subst, representatives),
            ret_eff: rewrite_compact_type(&fun.ret_eff, subst, representatives),
            ret: rewrite_compact_type(&fun.ret, subst, representatives),
        })
        .collect();
    let records = ty
        .records
        .iter()
        .map(|record| CompactRecord {
            fields: record
                .fields
                .iter()
                .map(|field| RecordField {
                    name: field.name.clone(),
                    value: rewrite_compact_type(&field.value, subst, representatives),
                    optional: field.optional,
                })
                .collect(),
        })
        .collect();
    let variants = ty
        .variants
        .iter()
        .map(|variant| CompactVariant {
            items: variant
                .items
                .iter()
                .map(|(name, payloads)| {
                    (
                        name.clone(),
                        payloads
                            .iter()
                            .map(|payload| rewrite_compact_type(payload, subst, representatives))
                            .collect(),
                    )
                })
                .collect(),
        })
        .collect();
    let tuples = ty
        .tuples
        .iter()
        .map(|tuple| {
            tuple
                .iter()
                .map(|item| rewrite_compact_type(item, subst, representatives))
                .collect()
        })
        .collect();
    let rows = ty
        .rows
        .iter()
        .map(|row| CompactRow {
            items: row
                .items
                .iter()
                .map(|item| rewrite_compact_type(item, subst, representatives))
                .collect(),
            tail: Box::new(rewrite_compact_type(&row.tail, subst, representatives)),
        })
        .collect();
    let rewritten = CompactType {
        vars,
        prims: ty.prims.clone(),
        cons,
        funs,
        records,
        record_spreads: ty
            .record_spreads
            .iter()
            .map(|spread| crate::simplify::compact::CompactRecordSpread {
                fields: spread
                    .fields
                    .iter()
                    .map(|field| RecordField {
                        name: field.name.clone(),
                        value: rewrite_compact_type(&field.value, subst, representatives),
                        optional: field.optional,
                    })
                    .collect(),
                tail: Box::new(rewrite_compact_type(&spread.tail, subst, representatives)),
                tail_wins: spread.tail_wins,
            })
            .collect(),
        variants,
        tuples,
        rows,
    };
    merge_compact_types(true, rewritten, representative_parts)
}

enum VarRewrite {
    Keep(TypeVar),
    Representative(CompactType),
    Remove,
}

fn rewrite_var_with_representative(
    tv: TypeVar,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
    representatives: &HashMap<TypeVar, CompactType>,
) -> VarRewrite {
    let mut cur = tv;
    let mut seen = HashSet::new();
    while let Some(next) = subst.get(&cur) {
        if let Some(representative) = representatives
            .get(&cur)
            .or_else(|| representatives.get(&tv))
            .cloned()
        {
            return VarRewrite::Representative(representative);
        }
        if !seen.insert(cur) {
            break;
        }
        match *next {
            Some(next) if next != cur => cur = next,
            Some(_) => break,
            None => {
                return representatives
                    .get(&tv)
                    .cloned()
                    .map(VarRewrite::Representative)
                    .unwrap_or(VarRewrite::Remove);
            }
        }
    }
    representatives
        .get(&cur)
        .or_else(|| representatives.get(&tv))
        .cloned()
        .map(VarRewrite::Representative)
        .unwrap_or(VarRewrite::Keep(cur))
}

fn rewrite_var(tv: TypeVar, subst: &HashMap<TypeVar, Option<TypeVar>>) -> Option<TypeVar> {
    let mut cur = tv;
    let mut seen = HashSet::new();
    while let Some(next) = subst.get(&cur) {
        if !seen.insert(cur) {
            break;
        }
        match *next {
            Some(next) if next != cur => cur = next,
            Some(_) => break,
            None => return None,
        }
    }
    Some(cur)
}

pub(crate) fn is_effectively_recursive(
    tv: TypeVar,
    rec_vars: &HashMap<TypeVar, CompactBounds>,
) -> bool {
    rec_vars
        .get(&tv)
        .is_some_and(|bounds| !is_trivial_self_bounds(tv, bounds))
}

fn is_trivial_self_bounds(tv: TypeVar, bounds: &CompactBounds) -> bool {
    (is_empty_compact_type(&bounds.lower) && is_only_self_var(&bounds.upper, tv))
        || (is_only_self_var(&bounds.lower, tv) && is_empty_compact_type(&bounds.upper))
        || (is_empty_compact_type(&bounds.lower) && is_only_self_empty_row(&bounds.upper, tv))
        || (is_only_self_empty_row(&bounds.lower, tv) && is_empty_compact_type(&bounds.upper))
        || (is_empty_compact_type(&bounds.lower)
            && is_self_with_guarded_self_rows(&bounds.upper, tv))
        || (is_self_with_guarded_self_rows(&bounds.lower, tv)
            && is_empty_compact_type(&bounds.upper))
        || is_var_only_self_alias_bounds(tv, bounds)
}

fn is_var_only_self_alias_bounds(tv: TypeVar, bounds: &CompactBounds) -> bool {
    let mut saw_self = false;
    compact_type_is_var_only_self_alias(&bounds.lower, tv, &mut saw_self)
        && compact_type_is_var_only_self_alias(&bounds.upper, tv, &mut saw_self)
        && saw_self
}

fn compact_type_is_var_only_self_alias(ty: &CompactType, tv: TypeVar, saw_self: &mut bool) -> bool {
    if !ty.prims.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
    {
        return false;
    }
    if ty.vars.contains(&tv) {
        *saw_self = true;
    }
    ty.rows.iter().all(|row| {
        row.items.is_empty() && compact_type_is_var_only_self_alias(&row.tail, tv, saw_self)
    })
}

fn is_only_self_var(ty: &CompactType, tv: TypeVar) -> bool {
    ty.vars.len() == 1
        && ty.vars.contains(&tv)
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
}

fn is_only_self_empty_row(ty: &CompactType, tv: TypeVar) -> bool {
    ty.vars.is_empty()
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && matches!(ty.rows.as_slice(), [row] if row.items.is_empty() && is_only_self_var(&row.tail, tv))
}

fn is_self_with_guarded_self_rows(ty: &CompactType, tv: TypeVar) -> bool {
    ty.vars.len() == 1
        && ty.vars.contains(&tv)
        && ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && !ty.rows.is_empty()
        && ty
            .rows
            .iter()
            .all(|row| !row.items.is_empty() && is_only_self_var(&row.tail, tv))
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

pub(super) fn exact_key_from_hash(kind: ExactKeyKind, value: impl Hash) -> ExactKey {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut hasher);
    ExactKey {
        digest: hasher.finish(),
        kind,
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use super::polarity::analyze_polar_occurrences_with_role_constraints;
    use super::{
        AlongItem, CompactRoleConstraint, ExactKeyKind, analyze_co_occurrences,
        coalesce_by_co_occurrence, coalesce_by_co_occurrence_with_role_constraint_inputs_report,
        coalesce_by_co_occurrence_with_role_constraints_report,
        coalesce_by_co_occurrence_with_role_constraints_report_inner,
    };
    use crate::simplify::compact::merge_compact_types;
    use crate::simplify::compact::{
        CompactBounds, CompactCon, CompactRecordSpread, CompactRow, CompactType, CompactTypeScheme,
    };
    use crate::symbols::{Name, Path};
    use crate::types::RecordField;
    use crate::{fresh_type_var, ids::TypeVar};

    #[test]
    fn analyze_co_occurrences_collects_positive_group() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a, b]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert_eq!(
            analysis.positive[&a],
            HashSet::from([AlongItem::Var(a), AlongItem::Var(b)]),
        );
        assert_eq!(
            analysis.positive[&b],
            HashSet::from([AlongItem::Var(a), AlongItem::Var(b)]),
        );
    }

    #[test]
    fn analyze_co_occurrences_collects_exact_along_items() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert!(analysis.positive[&a].iter().any(
            |item| matches!(item, AlongItem::Exact(exact) if exact.kind == ExactKeyKind::Other)
        ));
    }

    #[test]
    fn analyze_co_occurrences_reads_constructor_arg_bounds_as_input_intervals() {
        let lower_arg = fresh_type_var();
        let upper_arg = fresh_type_var();
        let scheme = invariant_box_in_function_arg_scheme(lower_arg, upper_arg);

        let analysis = analyze_co_occurrences(&scheme);
        let polar = analyze_polar_occurrences_with_role_constraints(&scheme, &[]);

        assert!(
            analysis.positive.contains_key(&lower_arg),
            "lower half of a constructor arg interval is the result side of the input interval",
        );
        assert!(
            analysis.negative.contains_key(&upper_arg),
            "upper half of a constructor arg interval is the argument side of the input interval",
        );
        assert!(polar.positive.contains(&lower_arg));
        assert!(polar.negative.contains(&upper_arg));
    }

    #[test]
    fn coalesce_by_co_occurrence_keeps_ref_update_like_effect_vars_distinct() {
        let residual = fresh_type_var();
        let captured = fresh_type_var();
        let value = fresh_type_var();
        let scheme = ref_update_like_curried_effect_scheme(residual, captured, value);

        let analysis = analyze_co_occurrences(&scheme);
        assert_eq!(
            analysis.positive[&residual],
            HashSet::from([AlongItem::Var(residual)])
        );
        assert_eq!(
            analysis.negative[&captured],
            HashSet::from([AlongItem::Var(captured)])
        );
        assert!(analysis.negative[&residual].contains(&AlongItem::Var(captured)));
        assert!(analysis.positive[&captured].contains(&AlongItem::Var(residual)));

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let fun = &coalesced.cty.lower.funs[0];
        assert_eq!(
            fun.arg.cons[0].args[0].lower.vars,
            HashSet::from([residual])
        );
        assert_eq!(
            fun.arg.cons[0].args[0].upper.vars,
            HashSet::from([residual, captured])
        );
        assert_eq!(fun.arg.cons[0].args[1], var_bounds(value));
        let callback_fun = &fun.ret.funs[0];
        assert_eq!(
            callback_fun.arg.funs[0].ret_eff.vars,
            HashSet::from([captured])
        );
        assert_eq!(
            callback_fun.ret_eff.vars,
            HashSet::from([residual, captured])
        );
    }

    #[test]
    fn coalesce_by_co_occurrence_merges_same_signature_vars() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert_eq!(coalesced.cty.lower.funs[0].arg.vars.len(), 1);
        assert_eq!(coalesced.cty.lower.funs[0].ret.vars.len(), 1);

        let report = coalesce_by_co_occurrence_with_role_constraints_report(&scheme, &[]);
        assert_eq!(report.rounds.len(), 1);
        assert_eq!(report.rounds[0].subst.get(&b), Some(&Some(a)));
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_positive_only_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());

        let report = coalesce_by_co_occurrence_with_role_constraints_report(&scheme, &[]);
        assert_eq!(report.rounds.len(), 1);
        assert_eq!(report.rounds[0].subst.get(&a), Some(&None));
    }

    #[test]
    fn coalesce_report_records_lower_representative_for_removed_var() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path.clone()]),
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let report = coalesce_by_co_occurrence_with_role_constraints_report(&scheme, &[]);
        assert_eq!(report.rounds.len(), 1);
        assert_eq!(report.rounds[0].subst.get(&a), Some(&None));
        assert_eq!(
            report.rounds[0].representatives.get(&a),
            Some(&CompactType {
                prims: HashSet::from([int_path]),
                ..CompactType::default()
            })
        );
    }

    #[test]
    fn coalesce_rewrites_removed_var_to_lower_representative() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path.clone()]),
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence_with_role_constraints_report_inner(
            &scheme,
            &[],
            &super::no_role_arg_inputs,
            true,
            &std::collections::HashMap::new(),
            0,
            None,
        )
        .scheme;
        assert!(coalesced.cty.lower.vars.is_empty());
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert_eq!(
            coalesced.cty.lower.funs[0].ret,
            CompactType {
                prims: HashSet::from([int_path]),
                ..CompactType::default()
            }
        );
    }

    #[test]
    fn coalesce_role_constraints_uses_input_args_not_associated_args_for_head_equality() {
        let input_a = fresh_type_var();
        let input_b = fresh_type_var();
        let associated = fresh_type_var();
        let role = Path {
            segments: vec![Name("Index".to_string())],
        };
        let constraints = vec![
            CompactRoleConstraint {
                role: role.clone(),
                args: vec![var_bounds(input_a), var_bounds(associated)],
            },
            CompactRoleConstraint {
                role: role.clone(),
                args: vec![var_bounds(input_b), var_bounds(associated)],
            },
        ];

        let coalesced = coalesce_by_co_occurrence_with_role_constraint_inputs_report(
            &CompactTypeScheme::default(),
            &constraints,
            |path| (path == &role).then_some(vec![true, false]),
            &std::collections::HashMap::new(),
            0,
        );

        assert_eq!(coalesced.constraints.len(), 2);
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_negative_only_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert!(coalesced.cty.lower.funs[0].arg.vars.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_positive_only_effect_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert!(coalesced.cty.lower.funs[0].ret_eff.vars.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_negative_only_effect_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                        ret_eff: CompactType::default(),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert!(coalesced.cty.lower.funs[0].arg_eff.vars.is_empty());
    }

    #[test]
    fn coalesce_by_polarity_removes_root_upper_mirrored_effect_input_vars() {
        let value = fresh_type_var();
        let scrutinee = fresh_type_var();
        let residual = fresh_type_var();
        let io_path = Path {
            segments: vec![Name("io".to_string())],
        };
        let row = CompactRow {
            items: vec![CompactType {
                prims: HashSet::from([io_path]),
                ..CompactType::default()
            }],
            tail: Box::new(CompactType {
                vars: HashSet::from([residual]),
                ..CompactType::default()
            }),
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType {
                            vars: HashSet::from([value]),
                            ..CompactType::default()
                        },
                        arg_eff: CompactType {
                            vars: HashSet::from([scrutinee]),
                            rows: vec![row.clone()],
                            ..CompactType::default()
                        },
                        ret_eff: CompactType {
                            vars: HashSet::from([residual]),
                            ..CompactType::default()
                        },
                        ret: CompactType {
                            vars: HashSet::from([value]),
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
                upper: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType {
                            vars: HashSet::from([value]),
                            ..CompactType::default()
                        },
                        arg_eff: CompactType {
                            vars: HashSet::from([scrutinee]),
                            ..CompactType::default()
                        },
                        ret_eff: CompactType {
                            vars: HashSet::from([residual]),
                            ..CompactType::default()
                        },
                        ret: CompactType {
                            vars: HashSet::from([value]),
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let fun = &coalesced.cty.lower.funs[0];
        assert!(
            fun.arg_eff.vars.is_empty(),
            "the mirrored root upper effect input must not keep a negative-only effect variable alive",
        );
        assert_eq!(fun.arg_eff.rows[0].tail.vars, HashSet::from([residual]));
        assert_eq!(fun.ret_eff.vars, HashSet::from([residual]));
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_positive_only_effect_arg_type_vars() {
        let a = fresh_type_var();
        let eff_path = Path {
            segments: vec![Name("eff".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            rows: vec![CompactRow {
                                items: vec![CompactType {
                                    cons: vec![CompactCon {
                                        path: eff_path,
                                        args: vec![CompactBounds {
                                            self_var: None,
                                            lower: CompactType {
                                                vars: HashSet::from([a]),
                                                ..CompactType::default()
                                            },
                                            upper: CompactType::default(),
                                        }],
                                    }],
                                    ..CompactType::default()
                                }],
                                tail: Box::new(CompactType::default()),
                            }],
                            ..CompactType::default()
                        },
                        ret_eff: CompactType::default(),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let arg = &coalesced.cty.lower.funs[0].arg_eff.rows[0].items[0].cons[0].args[0];
        assert!(arg.lower.vars.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_negative_only_effect_arg_type_vars() {
        let a = fresh_type_var();
        let eff_path = Path {
            segments: vec![Name("eff".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            rows: vec![CompactRow {
                                items: vec![CompactType {
                                    cons: vec![CompactCon {
                                        path: eff_path,
                                        args: vec![CompactBounds {
                                            self_var: None,
                                            lower: CompactType::default(),
                                            upper: CompactType {
                                                vars: HashSet::from([a]),
                                                ..CompactType::default()
                                            },
                                        }],
                                    }],
                                    ..CompactType::default()
                                }],
                                tail: Box::new(CompactType::default()),
                            }],
                            ..CompactType::default()
                        },
                        ret_eff: CompactType::default(),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let arg = &coalesced.cty.lower.funs[0].arg_eff.rows[0].items[0].cons[0].args[0];
        assert!(arg.upper.vars.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_primitive_sandwich() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path.clone()]),
                    ..CompactType::default()
                },
                upper: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path]),
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());
        assert!(coalesced.cty.upper.vars.is_empty());
    }

    #[test]
    fn analyze_co_occurrences_tracks_root_upper_along_items() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType::default(),
                upper: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert_eq!(
            analysis.negative[&a],
            HashSet::from([AlongItem::Var(a), AlongItem::Var(b)]),
        );
        assert_eq!(
            analysis.negative[&b],
            HashSet::from([AlongItem::Var(a), AlongItem::Var(b)]),
        );
    }

    #[test]
    fn analyze_co_occurrences_ignores_root_upper_direct_vars() {
        let a = fresh_type_var();
        let int_path = Path {
            segments: vec![Name("int".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType::default(),
                upper: CompactType {
                    vars: HashSet::from([a]),
                    prims: HashSet::from([int_path]),
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert!(!analysis.negative.contains_key(&a));
    }

    #[test]
    fn analyze_co_occurrences_tracks_record_spread_tail_vars() {
        let a = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    record_spreads: vec![CompactRecordSpread {
                        fields: vec![RecordField::required(
                            Name("x".to_string()),
                            CompactType::default(),
                        )],
                        tail: Box::new(CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        }),
                        tail_wins: true,
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert!(
            analysis.positive.contains_key(&a),
            "record spread tail vars should participate in positive co-occurrence analysis",
        );
    }

    #[test]
    fn analyze_co_occurrences_tracks_effect_row_tail_vars_in_row_plane() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let io_path = Path {
            segments: vec![Name("io".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    rows: vec![CompactRow {
                        items: vec![CompactType {
                            prims: HashSet::from([io_path]),
                            ..CompactType::default()
                        }],
                        tail: Box::new(CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        }),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert!(analysis.positive[&a].contains(&AlongItem::Var(b)));
        assert!(analysis.positive[&b].contains(&AlongItem::Var(a)));
    }

    #[test]
    fn analyze_co_occurrences_does_not_mix_effect_row_outer_vars_with_tail_vars() {
        let outer = fresh_type_var();
        let tail = fresh_type_var();
        let io_path = Path {
            segments: vec![Name("io".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([outer]),
                    rows: vec![CompactRow {
                        items: vec![CompactType {
                            prims: HashSet::from([io_path]),
                            ..CompactType::default()
                        }],
                        tail: Box::new(CompactType {
                            vars: HashSet::from([tail]),
                            ..CompactType::default()
                        }),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let analysis = analyze_co_occurrences(&scheme);
        assert!(!analysis.positive[&outer].contains(&AlongItem::Var(tail)));
        assert!(!analysis.positive[&tail].contains(&AlongItem::Var(outer)));
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_function_sandwich() {
        let a = fresh_type_var();
        let fun = crate::simplify::compact::CompactFun {
            arg: CompactType::default(),
            arg_eff: CompactType::default(),
            ret_eff: CompactType::default(),
            ret: CompactType::default(),
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    funs: vec![fun.clone()],
                    ..CompactType::default()
                },
                upper: CompactType {
                    vars: HashSet::from([a]),
                    funs: vec![fun],
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());
        assert!(coalesced.cty.upper.vars.is_empty());
        assert_eq!(coalesced.cty.lower.funs.len(), 1);
        assert_eq!(coalesced.cty.upper.funs.len(), 1);
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_output_only_exact_alias() {
        let a = fresh_type_var();
        let unit = CompactType {
            prims: HashSet::from([Path {
                segments: vec![Name("unit".to_string())],
            }]),
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: merge_compact_types(
                            true,
                            CompactType {
                                vars: HashSet::from([a]),
                                ..CompactType::default()
                            },
                            unit.clone(),
                        ),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType {
                            vars: HashSet::from([a]),
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let ret = &coalesced.cty.lower.funs[0].ret;
        assert!(ret.vars.is_empty());
        assert_eq!(ret.prims, unit.prims);
    }

    #[test]
    fn coalesce_by_co_occurrence_keeps_input_var_in_output_union() {
        let a = fresh_type_var();
        let int = CompactType {
            prims: HashSet::from([Path {
                segments: vec![Name("int".to_string())],
            }]),
            ..CompactType::default()
        };
        let var = CompactType {
            vars: HashSet::from([a]),
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: var.clone(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: merge_compact_types(true, var.clone(), int.clone()),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: var.clone(),
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: var.clone(),
                    }],
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let ret = &coalesced.cty.lower.funs[0].ret;
        assert!(ret.vars.contains(&a));
        assert_eq!(ret.prims, int.prims);
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_exact_row_sandwich() {
        let a = fresh_type_var();
        let io_path = Path {
            segments: vec![Name("io".to_string())],
        };
        let row = CompactType {
            rows: vec![CompactRow {
                items: vec![CompactType {
                    prims: HashSet::from([io_path]),
                    ..CompactType::default()
                }],
                tail: Box::new(CompactType::default()),
            }],
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    rows: row.rows.clone(),
                    ..CompactType::default()
                },
                upper: CompactType {
                    vars: HashSet::from([a]),
                    rows: row.rows,
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());
        assert!(coalesced.cty.upper.vars.is_empty());
        assert_eq!(coalesced.cty.lower.rows.len(), 1);
        assert_eq!(coalesced.cty.upper.rows.len(), 1);
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_record_spread_sandwich() {
        let a = fresh_type_var();
        let spread = CompactRecordSpread {
            fields: vec![RecordField::required(
                Name("x".to_string()),
                CompactType {
                    prims: HashSet::from([Path {
                        segments: vec![Name("int".to_string())],
                    }]),
                    ..CompactType::default()
                },
            )],
            tail: Box::new(CompactType::default()),
            tail_wins: true,
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    vars: HashSet::from([a]),
                    record_spreads: vec![spread.clone()],
                    ..CompactType::default()
                },
                upper: CompactType {
                    vars: HashSet::from([a]),
                    record_spreads: vec![spread],
                    ..CompactType::default()
                },
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        assert!(coalesced.cty.lower.vars.is_empty());
        assert!(coalesced.cty.upper.vars.is_empty());
        assert_eq!(coalesced.cty.lower.record_spreads.len(), 1);
        assert_eq!(coalesced.cty.upper.record_spreads.len(), 1);
    }

    #[test]
    fn coalesce_by_co_occurrence_removes_nested_constructor_arg_sandwich() {
        let a = fresh_type_var();
        let opt_path = Path {
            segments: vec![Name("opt".to_string())],
        };
        let tuple_payload = CompactType {
            tuples: vec![vec![
                CompactType {
                    prims: HashSet::from([Path {
                        segments: vec![Name("int".to_string())],
                    }]),
                    ..CompactType::default()
                },
                CompactType {
                    prims: HashSet::from([Path {
                        segments: vec![Name("int".to_string())],
                    }]),
                    ..CompactType::default()
                },
            ]],
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    cons: vec![CompactCon {
                        path: opt_path.clone(),
                        args: vec![CompactBounds {
                            self_var: None,
                            lower: merge_compact_types(
                                true,
                                CompactType {
                                    vars: HashSet::from([a]),
                                    ..CompactType::default()
                                },
                                tuple_payload.clone(),
                            ),
                            upper: merge_compact_types(
                                false,
                                CompactType {
                                    vars: HashSet::from([a]),
                                    ..CompactType::default()
                                },
                                tuple_payload.clone(),
                            ),
                        }],
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let arg = &coalesced.cty.lower.cons[0].args[0];
        assert!(arg.lower.vars.is_empty());
        assert!(arg.upper.vars.is_empty());
        assert_eq!(arg.lower.tuples.len(), 1);
        assert_eq!(arg.upper.tuples.len(), 1);
    }

    #[test]
    fn coalesce_by_co_occurrence_coalesces_effect_atom_interval_with_direct_arg() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let ref_path = Path {
            segments: vec![Name("ref".to_string())],
        };
        let var_path = Path {
            segments: vec![Name("var".to_string())],
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    cons: vec![CompactCon {
                        path: ref_path,
                        args: vec![
                            CompactBounds {
                                self_var: None,
                                lower: CompactType {
                                    rows: vec![CompactRow {
                                        items: vec![CompactType {
                                            cons: vec![CompactCon {
                                                path: var_path,
                                                args: vec![CompactBounds {
                                                    self_var: None,
                                                    lower: CompactType {
                                                        vars: HashSet::from([a, b]),
                                                        ..CompactType::default()
                                                    },
                                                    upper: CompactType {
                                                        vars: HashSet::from([a, b]),
                                                        ..CompactType::default()
                                                    },
                                                }],
                                            }],
                                            ..CompactType::default()
                                        }],
                                        tail: Box::new(CompactType::default()),
                                    }],
                                    ..CompactType::default()
                                },
                                upper: CompactType::default(),
                            },
                            CompactBounds {
                                self_var: None,
                                lower: CompactType {
                                    vars: HashSet::from([a]),
                                    ..CompactType::default()
                                },
                                upper: CompactType {
                                    vars: HashSet::from([b]),
                                    ..CompactType::default()
                                },
                            },
                        ],
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let con = &coalesced.cty.lower.cons[0];
        let row_item_con = &con.args[0].lower.rows[0].items[0].cons[0];
        assert_eq!(row_item_con.args[0].lower.vars, HashSet::from([a]));
        assert_eq!(row_item_con.args[0].upper.vars, HashSet::from([a]));
        assert_eq!(con.args[1].lower.vars, HashSet::from([a]));
        assert_eq!(con.args[1].upper.vars, HashSet::from([a]));
    }

    #[test]
    fn coalesce_by_co_occurrence_does_not_merge_effect_row_outer_vars_with_tail_vars() {
        let outer_var = fresh_type_var();
        let tail_var = fresh_type_var();
        let io_path = Path {
            segments: vec![Name("io".to_string())],
        };
        let effect_input = CompactType {
            vars: HashSet::from([outer_var]),
            rows: vec![CompactRow {
                items: vec![CompactType {
                    prims: HashSet::from([io_path]),
                    ..CompactType::default()
                }],
                tail: Box::new(CompactType {
                    vars: HashSet::from([tail_var]),
                    ..CompactType::default()
                }),
            }],
            ..CompactType::default()
        };
        let effect_output = CompactType {
            vars: HashSet::from([tail_var]),
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: effect_input,
                        ret_eff: effect_output,
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let fun = &coalesced.cty.lower.funs[0];
        let coalesced_tail = single_var(&fun.arg_eff.rows[0].tail.vars);
        assert!(
            fun.arg_eff.vars.is_empty(),
            "a negative-only effect var outside the row must be removed, not unified with the row tail",
        );
        assert_eq!(fun.ret_eff.vars, HashSet::from([coalesced_tail]));
    }

    #[test]
    fn coalesce_by_co_occurrence_merges_indistinguishable_effect_vars() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                        ret_eff: CompactType {
                            vars: HashSet::from([a, b]),
                            ..CompactType::default()
                        },
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let fun = &coalesced.cty.lower.funs[0];
        assert_eq!(fun.arg_eff.vars.len(), 1);
        assert_eq!(fun.ret_eff.vars.len(), 1);
        assert_eq!(fun.arg_eff.vars, fun.ret_eff.vars);
    }

    fn single_var(vars: &HashSet<TypeVar>) -> TypeVar {
        assert_eq!(vars.len(), 1);
        *vars.iter().next().unwrap()
    }

    fn var_bounds(tv: TypeVar) -> CompactBounds {
        CompactBounds {
            self_var: None,
            lower: CompactType {
                vars: HashSet::from([tv]),
                ..CompactType::default()
            },
            upper: CompactType {
                vars: HashSet::from([tv]),
                ..CompactType::default()
            },
        }
    }

    fn invariant_box_in_function_arg_scheme(
        lower_arg: TypeVar,
        upper_arg: TypeVar,
    ) -> CompactTypeScheme {
        CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType {
                            cons: vec![CompactCon {
                                path: Path {
                                    segments: vec![Name("Box".to_string())],
                                },
                                args: vec![CompactBounds {
                                    self_var: None,
                                    lower: CompactType {
                                        vars: HashSet::from([lower_arg]),
                                        ..CompactType::default()
                                    },
                                    upper: CompactType {
                                        vars: HashSet::from([upper_arg]),
                                        ..CompactType::default()
                                    },
                                }],
                            }],
                            ..CompactType::default()
                        },
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        }
    }

    fn ref_update_like_curried_effect_scheme(
        residual: TypeVar,
        captured: TypeVar,
        value: TypeVar,
    ) -> CompactTypeScheme {
        CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType {
                            cons: vec![CompactCon {
                                path: Path {
                                    segments: vec![Name("ref".to_string())],
                                },
                                args: vec![
                                    CompactBounds {
                                        self_var: None,
                                        lower: CompactType {
                                            vars: HashSet::from([residual]),
                                            ..CompactType::default()
                                        },
                                        upper: CompactType {
                                            vars: HashSet::from([residual, captured]),
                                            ..CompactType::default()
                                        },
                                    },
                                    var_bounds(value),
                                ],
                            }],
                            ..CompactType::default()
                        },
                        arg_eff: CompactType::default(),
                        ret_eff: CompactType::default(),
                        ret: CompactType {
                            funs: vec![crate::simplify::compact::CompactFun {
                                arg: CompactType {
                                    funs: vec![crate::simplify::compact::CompactFun {
                                        arg: CompactType {
                                            vars: HashSet::from([value]),
                                            ..CompactType::default()
                                        },
                                        arg_eff: CompactType::default(),
                                        ret_eff: CompactType {
                                            vars: HashSet::from([captured]),
                                            ..CompactType::default()
                                        },
                                        ret: CompactType {
                                            vars: HashSet::from([value]),
                                            ..CompactType::default()
                                        },
                                    }],
                                    ..CompactType::default()
                                },
                                arg_eff: CompactType::default(),
                                ret_eff: CompactType {
                                    vars: HashSet::from([residual, captured]),
                                    ..CompactType::default()
                                },
                                ret: CompactType::default(),
                            }],
                            ..CompactType::default()
                        },
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        }
    }
}
