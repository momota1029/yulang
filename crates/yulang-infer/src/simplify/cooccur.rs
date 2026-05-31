use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

use serde::{Deserialize, Serialize};

mod analysis;
mod group;
mod passes;
mod representative;

use crate::ids::TypeVar;
use crate::solve::effect_row::normalize_rewritten_bounds;
use crate::symbols::Path;
use crate::types::RecordField;

use super::compact::{
    CompactBounds, CompactCon, CompactFun, CompactRecord, CompactRow, CompactType,
    CompactTypeScheme, CompactVariant, merge_compact_bounds, merge_compact_types,
    normalize_compact_scheme_rows,
};
use super::polar::apply_polar_variable_removal;
use super::role_constraints::rewrite_role_constraints;
use analysis::analyze_co_occurrences_with_role_constraints;
use group::analyze_group_co_occurrences_with_role_constraints;
use passes::{
    apply_exact_row_unifications, apply_exact_sandwich_removal,
    apply_function_effect_residual_unifications, apply_group_co_occurrence_substitutions,
    apply_one_sided_exact_alias_collapse, apply_row_residual_unifications,
    apply_shadow_var_collapse, expose_positive_row_residual_tails,
};
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub(super) struct ExactSignature {
    positive: Vec<ExactKey>,
    negative: Vec<ExactKey>,
}

#[derive(Debug, Clone, Default)]
pub(super) struct ExactInfo {
    positive: HashMap<TypeVar, HashSet<ExactKey>>,
    negative: HashMap<TypeVar, HashSet<ExactKey>>,
    signatures: HashMap<TypeVar, ExactSignature>,
    has_concrete_row: HashSet<TypeVar>,
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
) -> (CompactTypeScheme, Vec<CompactRoleConstraint>) {
    coalesce_by_co_occurrence_with_role_constraint_inputs_and_boundary_vars(
        scheme,
        constraints,
        role_arg_inputs,
        &HashSet::new(),
    )
}

pub fn coalesce_by_co_occurrence_with_role_constraint_inputs_and_boundary_vars(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    role_arg_inputs: impl Fn(&Path) -> Option<Vec<bool>>,
    generalization_boundary_vars: &HashSet<TypeVar>,
) -> (CompactTypeScheme, Vec<CompactRoleConstraint>) {
    let output = coalesce_by_co_occurrence_with_role_constraints_report_inner(
        scheme,
        constraints,
        Some(&role_arg_inputs),
        std::env::var_os("YULANG_USE_COALESCE_REPRESENTATIVES").is_some(),
        generalization_boundary_vars,
    );
    (output.scheme, output.constraints)
}

pub fn coalesce_by_co_occurrence_with_role_constraints_report(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
) -> CoalesceOutput {
    coalesce_by_co_occurrence_with_role_constraints_report_inner(
        scheme,
        constraints,
        None,
        std::env::var_os("YULANG_USE_COALESCE_REPRESENTATIVES").is_some(),
        &HashSet::new(),
    )
}

type RoleArgInputs<'a> = dyn Fn(&Path) -> Option<Vec<bool>> + 'a;

fn coalesce_by_co_occurrence_with_role_constraints_report_inner(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    role_arg_inputs: Option<&RoleArgInputs<'_>>,
    use_representatives: bool,
    generalization_boundary_vars: &HashSet<TypeVar>,
) -> CoalesceOutput {
    let mut current_scheme = scheme.clone();
    let mut current_constraints = constraints.to_vec();
    let mut rounds = Vec::new();

    loop {
        let mut rigid_vars = role_constraint_rigid_vars(&current_constraints, role_arg_inputs);
        rigid_vars.extend(generalization_boundary_vars.iter().copied());
        collect_open_interval_vars(&current_scheme.cty, &mut rigid_vars);
        let positive_scheme_vars = collect_positive_scheme_vars(&current_scheme);
        collect_open_interval_vars_in_constraints(
            &current_constraints,
            &positive_scheme_vars,
            &mut rigid_vars,
        );
        let mut analysis =
            analyze_co_occurrences_with_role_constraints(&current_scheme, &current_constraints);
        let mut rec_vars = current_scheme.rec_vars.clone();
        let mut all_vars = collect_all_vars(&current_scheme, &analysis);
        let group_analysis = analyze_group_co_occurrences_with_role_constraints(
            &current_scheme,
            &current_constraints,
        );
        all_vars.extend(group_analysis.types.keys().copied());
        all_vars.extend(group_analysis.effect_types.keys().copied());
        all_vars.extend(group_analysis.effects.keys().copied());
        all_vars.sort_by_key(|tv| tv.0);
        all_vars.dedup();
        all_vars.sort_by_key(|tv| std::cmp::Reverse(tv.0));

        let mut subst = HashMap::<TypeVar, Option<TypeVar>>::new();
        apply_group_co_occurrence_substitutions(
            &group_analysis,
            &mut analysis,
            &mut rec_vars,
            &rigid_vars,
            &mut subst,
        );
        let exposed_row_residual_vars = apply_row_residual_unifications(
            &current_scheme,
            &current_constraints,
            &mut rec_vars,
            &mut analysis,
            &rigid_vars,
            &mut subst,
        );
        apply_function_effect_residual_unifications(
            &current_scheme,
            &current_constraints,
            &mut rec_vars,
            &mut analysis,
            &rigid_vars,
            &mut subst,
        );
        apply_polar_variable_removal(&all_vars, &analysis, &rec_vars, &rigid_vars, &mut subst);
        let exact_info = ExactInfo::from_analysis(&analysis);
        apply_exact_row_unifications(&all_vars, &exact_info, &rec_vars, &rigid_vars, &mut subst);
        apply_exact_sandwich_removal(&all_vars, &exact_info, &rigid_vars, &mut subst);
        apply_shadow_var_collapse(&all_vars, &analysis, &rigid_vars, &mut subst);
        let mut exact_alias_rigid_vars = rigid_vars.clone();
        collect_function_input_vars_in_scheme(&current_scheme, &mut exact_alias_rigid_vars);
        collect_escaping_function_input_vars_in_scheme(
            &current_scheme,
            &positive_scheme_vars,
            &mut exact_alias_rigid_vars,
        );
        collect_data_payload_interval_vars_in_scheme(&current_scheme, &mut exact_alias_rigid_vars);
        apply_one_sided_exact_alias_collapse(
            &all_vars,
            &analysis,
            &exact_alias_rigid_vars,
            &mut subst,
        );
        let guarded_row_representatives =
            guarded_row_recursion_representatives(&rec_vars, &rigid_vars, &subst);
        for &var in guarded_row_representatives.keys() {
            subst.entry(var).or_insert(None);
        }
        let mut representatives = lower_representatives_for_subst(
            &current_scheme,
            &current_constraints,
            &rec_vars,
            &subst,
        );
        representatives.extend(
            guarded_row_representatives
                .iter()
                .map(|(&tv, ty)| (tv, ty.clone())),
        );
        let use_representatives_now =
            use_representatives || !guarded_row_representatives.is_empty();
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
        expose_positive_row_residual_tails(&mut rewritten_scheme, &exposed_row_residual_vars);
        let rewritten_constraints = if use_representatives_now {
            rewrite_constraints_with_representatives(
                &rewritten_scheme,
                &current_constraints,
                &subst,
                &representatives,
            )
        } else {
            rewrite_role_constraints(&rewritten_scheme, &current_constraints, &subst)
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

        current_scheme = rewritten_scheme;
        current_constraints = rewritten_constraints;
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

fn role_constraint_rigid_vars(
    constraints: &[CompactRoleConstraint],
    role_arg_inputs: Option<&RoleArgInputs<'_>>,
) -> HashSet<TypeVar> {
    constraints
        .iter()
        .flat_map(|constraint| {
            let inputs = role_arg_inputs
                .and_then(|lookup| lookup(&constraint.role))
                .filter(|inputs| inputs.len() == constraint.args.len());
            constraint
                .args
                .iter()
                .enumerate()
                .filter_map(move |(index, arg)| role_arg_rigid_var(arg, inputs.as_deref(), index))
        })
        .collect()
}

fn guarded_row_recursion_representatives(
    rec_vars: &HashMap<TypeVar, CompactBounds>,
    rigid_vars: &HashSet<TypeVar>,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> HashMap<TypeVar, CompactType> {
    let mut out = HashMap::new();
    let mut items = rec_vars.iter().collect::<Vec<_>>();
    items.sort_by_key(|(tv, _)| tv.0);
    for (&tv, bounds) in items {
        if rigid_vars.contains(&tv) || subst.contains_key(&tv) {
            continue;
        }
        let mut rows = Vec::new();
        collect_guarded_row_candidates(tv, &bounds.lower, &mut rows);
        collect_guarded_row_candidates(tv, &bounds.upper, &mut rows);
        if rows.is_empty() {
            continue;
        }
        let Some(first_shape) = guarded_row_shape(&rows[0]) else {
            continue;
        };
        if rows
            .iter()
            .any(|row| guarded_row_shape(row).as_ref() != Some(&first_shape))
        {
            continue;
        }
        rows.sort_by_key(|row| {
            (
                compact_type_mentions_var(&row.tail, tv),
                row.tail.vars.is_empty(),
            )
        });
        let row = rows.remove(0);
        out.insert(
            tv,
            CompactType {
                rows: vec![row],
                ..CompactType::default()
            },
        );
    }
    out
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct GuardedRowItemShape {
    path: Path,
    arity: usize,
}

fn guarded_row_shape(row: &CompactRow) -> Option<Vec<GuardedRowItemShape>> {
    let mut shapes = row
        .items
        .iter()
        .map(guarded_row_item_shape)
        .collect::<Option<Vec<_>>>()?;
    shapes
        .sort_by(|lhs, rhs| guarded_row_item_shape_key(lhs).cmp(&guarded_row_item_shape_key(rhs)));
    Some(shapes)
}

fn guarded_row_item_shape(item: &CompactType) -> Option<GuardedRowItemShape> {
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
        return item
            .prims
            .iter()
            .next()
            .cloned()
            .map(|path| GuardedRowItemShape { path, arity: 0 });
    }
    if item.cons.len() == 1 && item.prims.is_empty() {
        let con = &item.cons[0];
        return Some(GuardedRowItemShape {
            path: con.path.clone(),
            arity: con.args.len(),
        });
    }
    None
}

fn guarded_row_item_shape_key(shape: &GuardedRowItemShape) -> (String, usize) {
    (
        shape
            .path
            .segments
            .iter()
            .map(|segment| segment.0.as_str())
            .collect::<Vec<_>>()
            .join("::"),
        shape.arity,
    )
}

fn collect_guarded_row_candidates(tv: TypeVar, ty: &CompactType, out: &mut Vec<CompactRow>) {
    for row in &ty.rows {
        if !row.items.is_empty() && !compact_type_mentions_var(&row.tail, tv) {
            out.push(row.clone());
        }
        for item in &row.items {
            collect_guarded_row_candidates(tv, item, out);
        }
        collect_guarded_row_candidates(tv, &row.tail, out);
    }
    for con in &ty.cons {
        for arg in &con.args {
            collect_guarded_row_candidates(tv, &arg.lower, out);
            collect_guarded_row_candidates(tv, &arg.upper, out);
        }
    }
    for fun in &ty.funs {
        collect_guarded_row_candidates(tv, &fun.arg, out);
        collect_guarded_row_candidates(tv, &fun.arg_eff, out);
        collect_guarded_row_candidates(tv, &fun.ret_eff, out);
        collect_guarded_row_candidates(tv, &fun.ret, out);
    }
}

fn compact_type_mentions_var(ty: &CompactType, tv: TypeVar) -> bool {
    ty.vars.contains(&tv)
        || ty.cons.iter().any(|con| {
            con.args.iter().any(|arg| {
                compact_type_mentions_var(&arg.lower, tv)
                    || compact_type_mentions_var(&arg.upper, tv)
            })
        })
        || ty.funs.iter().any(|fun| {
            compact_type_mentions_var(&fun.arg, tv)
                || compact_type_mentions_var(&fun.arg_eff, tv)
                || compact_type_mentions_var(&fun.ret_eff, tv)
                || compact_type_mentions_var(&fun.ret, tv)
        })
        || ty.records.iter().any(|record| {
            record
                .fields
                .iter()
                .any(|field| compact_type_mentions_var(&field.value, tv))
        })
        || ty.record_spreads.iter().any(|spread| {
            spread
                .fields
                .iter()
                .any(|field| compact_type_mentions_var(&field.value, tv))
                || compact_type_mentions_var(&spread.tail, tv)
        })
        || ty.variants.iter().any(|variant| {
            variant.items.iter().any(|(_, payloads)| {
                payloads
                    .iter()
                    .any(|payload| compact_type_mentions_var(payload, tv))
            })
        })
        || ty
            .tuples
            .iter()
            .any(|tuple| tuple.iter().any(|item| compact_type_mentions_var(item, tv)))
        || ty.rows.iter().any(|row| {
            row.items
                .iter()
                .any(|item| compact_type_mentions_var(item, tv))
                || compact_type_mentions_var(&row.tail, tv)
        })
}

fn collect_function_input_vars_in_scheme(scheme: &CompactTypeScheme, out: &mut HashSet<TypeVar>) {
    collect_function_input_vars_in_bounds(&scheme.cty, false, out);
    for bounds in scheme.rec_vars.values() {
        collect_function_input_vars_in_bounds(bounds, false, out);
    }
}

fn collect_escaping_function_input_vars_in_scheme(
    scheme: &CompactTypeScheme,
    positive_scheme_vars: &HashSet<TypeVar>,
    out: &mut HashSet<TypeVar>,
) {
    collect_escaping_function_input_vars_in_bounds(&scheme.cty, false, positive_scheme_vars, out);
    for bounds in scheme.rec_vars.values() {
        collect_escaping_function_input_vars_in_bounds(bounds, false, positive_scheme_vars, out);
    }
}

fn collect_escaping_function_input_vars_in_bounds(
    bounds: &CompactBounds,
    inside_input: bool,
    positive_scheme_vars: &HashSet<TypeVar>,
    out: &mut HashSet<TypeVar>,
) {
    collect_escaping_function_input_vars_in_type(
        &bounds.lower,
        inside_input,
        false,
        positive_scheme_vars,
        out,
    );
    collect_escaping_function_input_vars_in_type(
        &bounds.upper,
        inside_input,
        false,
        positive_scheme_vars,
        out,
    );
}

fn collect_escaping_function_input_vars_in_type(
    ty: &CompactType,
    inside_input: bool,
    inside_effect_row_item: bool,
    positive_scheme_vars: &HashSet<TypeVar>,
    out: &mut HashSet<TypeVar>,
) {
    if inside_input && !inside_effect_row_item {
        out.extend(
            ty.vars
                .iter()
                .copied()
                .filter(|var| positive_scheme_vars.contains(var)),
        );
    }
    for con in &ty.cons {
        for arg in &con.args {
            collect_escaping_function_input_vars_in_bounds(
                arg,
                inside_input && !inside_effect_row_item,
                positive_scheme_vars,
                out,
            );
        }
    }
    for fun in &ty.funs {
        collect_escaping_function_input_vars_in_type(
            &fun.arg,
            true,
            false,
            positive_scheme_vars,
            out,
        );
        collect_escaping_function_input_vars_in_type(
            &fun.arg_eff,
            true,
            false,
            positive_scheme_vars,
            out,
        );
        collect_escaping_function_input_vars_in_type(
            &fun.ret_eff,
            inside_input,
            false,
            positive_scheme_vars,
            out,
        );
        collect_escaping_function_input_vars_in_type(
            &fun.ret,
            inside_input,
            false,
            positive_scheme_vars,
            out,
        );
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_escaping_function_input_vars_in_type(
                &field.value,
                inside_input,
                false,
                positive_scheme_vars,
                out,
            );
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_escaping_function_input_vars_in_type(
                &field.value,
                inside_input,
                false,
                positive_scheme_vars,
                out,
            );
        }
        collect_escaping_function_input_vars_in_type(
            &spread.tail,
            inside_input,
            false,
            positive_scheme_vars,
            out,
        );
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_escaping_function_input_vars_in_type(
                    payload,
                    inside_input,
                    false,
                    positive_scheme_vars,
                    out,
                );
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_escaping_function_input_vars_in_type(
                item,
                inside_input,
                false,
                positive_scheme_vars,
                out,
            );
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_escaping_function_input_vars_in_type(
                item,
                inside_input,
                true,
                positive_scheme_vars,
                out,
            );
        }
        collect_escaping_function_input_vars_in_type(
            &row.tail,
            inside_input,
            false,
            positive_scheme_vars,
            out,
        );
    }
}

fn collect_function_input_vars_in_bounds(
    bounds: &CompactBounds,
    inside_input: bool,
    out: &mut HashSet<TypeVar>,
) {
    collect_function_input_vars_in_type(&bounds.lower, inside_input, false, false, out);
    collect_function_input_vars_in_type(&bounds.upper, inside_input, false, false, out);
}

fn collect_function_input_vars_in_type(
    ty: &CompactType,
    inside_input: bool,
    inside_effect_position: bool,
    inside_effect_row_item: bool,
    out: &mut HashSet<TypeVar>,
) {
    if inside_input
        && !inside_effect_row_item
        && (inside_effect_position || !compact_type_has_shape(ty))
    {
        out.extend(ty.vars.iter().copied());
    }
    for con in &ty.cons {
        for arg in &con.args {
            collect_function_input_vars_in_bounds(
                arg,
                inside_input && !inside_effect_row_item,
                out,
            );
        }
    }
    for fun in &ty.funs {
        collect_function_input_vars_in_type(&fun.arg, true, false, false, out);
        collect_function_input_vars_in_type(&fun.arg_eff, true, true, false, out);
        collect_function_input_vars_in_type(&fun.ret_eff, inside_input, true, false, out);
        collect_function_input_vars_in_type(&fun.ret, inside_input, false, false, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_function_input_vars_in_type(
                &field.value,
                inside_input,
                inside_effect_position,
                false,
                out,
            );
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_function_input_vars_in_type(
                &field.value,
                inside_input,
                inside_effect_position,
                false,
                out,
            );
        }
        collect_function_input_vars_in_type(
            &spread.tail,
            inside_input,
            inside_effect_position,
            false,
            out,
        );
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_function_input_vars_in_type(
                    payload,
                    inside_input,
                    inside_effect_position,
                    false,
                    out,
                );
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_function_input_vars_in_type(
                item,
                inside_input,
                inside_effect_position,
                false,
                out,
            );
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_function_input_vars_in_type(
                item,
                inside_input,
                inside_effect_position,
                true,
                out,
            );
        }
        collect_function_input_vars_in_type(
            &row.tail,
            inside_input,
            inside_effect_position,
            false,
            out,
        );
    }
}

fn collect_data_payload_interval_vars_in_scheme(
    scheme: &CompactTypeScheme,
    out: &mut HashSet<TypeVar>,
) {
    collect_data_payload_interval_vars_in_bounds(&scheme.cty, out);
    for bounds in scheme.rec_vars.values() {
        collect_data_payload_interval_vars_in_bounds(bounds, out);
    }
}

fn collect_data_payload_interval_vars_in_bounds(
    bounds: &CompactBounds,
    out: &mut HashSet<TypeVar>,
) {
    collect_data_payload_interval_vars_in_type(&bounds.lower, out);
    collect_data_payload_interval_vars_in_type(&bounds.upper, out);
}

fn collect_data_payload_interval_vars_in_type(ty: &CompactType, out: &mut HashSet<TypeVar>) {
    for con in &ty.cons {
        for arg in &con.args {
            collect_open_payload_interval_vars(arg, out);
            collect_data_payload_interval_vars_in_bounds(arg, out);
        }
    }
    for fun in &ty.funs {
        collect_data_payload_interval_vars_in_type(&fun.arg, out);
        collect_data_payload_interval_vars_in_type(&fun.arg_eff, out);
        collect_data_payload_interval_vars_in_type(&fun.ret_eff, out);
        collect_data_payload_interval_vars_in_type(&fun.ret, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_data_payload_interval_vars_in_type(&field.value, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_data_payload_interval_vars_in_type(&field.value, out);
        }
        collect_data_payload_interval_vars_in_type(&spread.tail, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_data_payload_interval_vars_in_type(payload, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_data_payload_interval_vars_in_type(item, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_data_payload_interval_vars_in_type(item, out);
        }
        collect_data_payload_interval_vars_in_type(&row.tail, out);
    }
}

fn collect_open_payload_interval_vars(bounds: &CompactBounds, out: &mut HashSet<TypeVar>) {
    collect_open_interval_vars(bounds, out);
}

fn collect_open_interval_vars_in_constraints(
    constraints: &[CompactRoleConstraint],
    positive_scheme_vars: &HashSet<TypeVar>,
    out: &mut HashSet<TypeVar>,
) {
    for constraint in constraints {
        for arg in &constraint.args {
            collect_open_interval_vars_matching(arg, out, |var| {
                positive_scheme_vars.contains(&var)
            });
        }
    }
}

fn collect_open_interval_vars(bounds: &CompactBounds, out: &mut HashSet<TypeVar>) {
    collect_open_interval_vars_matching(bounds, out, |_| true);
}

fn collect_open_interval_vars_matching(
    bounds: &CompactBounds,
    out: &mut HashSet<TypeVar>,
    keep: impl Fn(TypeVar) -> bool,
) {
    let Some(upper_vars) = compact_type_var_set(&bounds.upper) else {
        return;
    };
    if upper_vars.len() != 1 || !compact_type_has_data_shape(&bounds.lower) {
        return;
    }
    for var in upper_vars {
        if keep(var) && bounds.lower.vars.contains(&var) {
            out.insert(var);
        }
    }
}

fn collect_positive_scheme_vars(scheme: &CompactTypeScheme) -> HashSet<TypeVar> {
    let mut out = HashSet::new();
    collect_positive_vars_in_bounds(&scheme.cty, true, &mut out);
    for bounds in scheme.rec_vars.values() {
        collect_positive_vars_in_bounds(bounds, true, &mut out);
    }
    out
}

fn collect_positive_vars_in_bounds(
    bounds: &CompactBounds,
    positive: bool,
    out: &mut HashSet<TypeVar>,
) {
    collect_positive_vars_in_type(&bounds.lower, positive, out);
    collect_positive_vars_in_type(&bounds.upper, !positive, out);
}

fn collect_positive_vars_in_type(ty: &CompactType, positive: bool, out: &mut HashSet<TypeVar>) {
    if positive {
        out.extend(ty.vars.iter().copied());
    }
    for con in &ty.cons {
        for arg in &con.args {
            collect_positive_vars_in_bounds(arg, true, out);
        }
    }
    for fun in &ty.funs {
        collect_positive_vars_in_type(&fun.arg, !positive, out);
        collect_positive_vars_in_type(&fun.arg_eff, !positive, out);
        collect_positive_vars_in_type(&fun.ret_eff, positive, out);
        collect_positive_vars_in_type(&fun.ret, positive, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_positive_vars_in_type(&field.value, positive, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_positive_vars_in_type(&field.value, positive, out);
        }
        collect_positive_vars_in_type(&spread.tail, positive, out);
    }
    for variant in &ty.variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_positive_vars_in_type(payload, positive, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in tuple {
            collect_positive_vars_in_type(item, positive, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            collect_positive_vars_in_type(item, positive, out);
        }
        collect_positive_vars_in_type(&row.tail, positive, out);
    }
}

fn compact_type_var_set(ty: &CompactType) -> Option<HashSet<TypeVar>> {
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

fn compact_type_has_data_shape(ty: &CompactType) -> bool {
    !ty.prims.is_empty()
        || !ty.cons.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
}

fn compact_type_has_shape(ty: &CompactType) -> bool {
    !ty.prims.is_empty()
        || !ty.cons.is_empty()
        || !ty.funs.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.variants.is_empty()
        || !ty.tuples.is_empty()
        || !ty.rows.is_empty()
}

fn role_arg_rigid_var(
    bounds: &CompactBounds,
    role_arg_inputs: Option<&[bool]>,
    index: usize,
) -> Option<TypeVar> {
    match role_arg_inputs.and_then(|inputs| inputs.get(index).copied()) {
        Some(true) => exact_center_var(bounds),
        Some(false) => projection_target_var(bounds),
        None => projection_target_var(bounds),
    }
}

fn exact_center_var(bounds: &CompactBounds) -> Option<TypeVar> {
    bounds.self_var.or_else(|| {
        let lower = single_compact_var(&bounds.lower);
        let upper = single_compact_var(&bounds.upper);
        match (lower, upper) {
            (Some(lhs), Some(rhs)) if lhs == rhs => Some(lhs),
            _ => None,
        }
    })
}

fn projection_target_var(bounds: &CompactBounds) -> Option<TypeVar> {
    exact_center_var(bounds).or_else(|| {
        let lower = single_compact_var(&bounds.lower);
        let upper = single_compact_var(&bounds.upper);
        match (lower, upper) {
            (Some(tv), None) | (None, Some(tv)) => Some(tv),
            _ => None,
        }
    })
}

fn single_compact_var(ty: &CompactType) -> Option<TypeVar> {
    (ty.prims.is_empty()
        && ty.cons.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
        && ty.vars.len() == 1)
        .then(|| ty.vars.iter().copied().next())
        .flatten()
}

pub(crate) fn rewrite_scheme_with_subst(
    scheme: &CompactTypeScheme,
    subst: &HashMap<TypeVar, Option<TypeVar>>,
) -> CompactTypeScheme {
    rewrite_scheme(scheme, &scheme.rec_vars, subst)
}

fn collect_all_vars(scheme: &CompactTypeScheme, analysis: &CoOccurrences) -> Vec<TypeVar> {
    let mut vars = scheme.rec_vars.keys().copied().collect::<HashSet<_>>();
    vars.extend(analysis.positive.keys().copied());
    vars.extend(analysis.negative.keys().copied());
    vars.into_iter().collect()
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
    rewrite_role_constraints(scheme, &rewritten, &HashMap::new())
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

pub(crate) fn has_matching_polar_signature(
    analysis: &CoOccurrences,
    lhs: TypeVar,
    rhs: TypeVar,
) -> bool {
    matching_occurrence_side(&analysis.positive, lhs, rhs)
        || matching_occurrence_side(&analysis.negative, lhs, rhs)
}

fn matching_occurrence_side(
    map: &HashMap<TypeVar, HashSet<AlongItem>>,
    lhs: TypeVar,
    rhs: TypeVar,
) -> bool {
    let Some(lhs_occurs) = map.get(&lhs) else {
        return false;
    };
    let Some(rhs_occurs) = map.get(&rhs) else {
        return false;
    };
    !lhs_occurs.is_empty() && lhs_occurs == rhs_occurs
}

fn exact_occurrences(analysis: &CoOccurrences, positive: bool, tv: TypeVar) -> HashSet<ExactKey> {
    let occurs = if positive {
        analysis.positive.get(&tv)
    } else {
        analysis.negative.get(&tv)
    };
    let Some(occurs) = occurs else {
        return HashSet::new();
    };
    occurs
        .iter()
        .filter_map(|item| match item {
            AlongItem::Exact(exact) => Some(*exact),
            AlongItem::Var(_) => None,
        })
        .collect()
}

impl ExactInfo {
    fn from_analysis(analysis: &CoOccurrences) -> Self {
        let mut info = Self::default();
        let all_vars = analysis
            .positive
            .keys()
            .chain(analysis.negative.keys())
            .copied()
            .collect::<HashSet<_>>();
        for tv in all_vars {
            let positive = exact_occurrences(analysis, true, tv);
            let negative = exact_occurrences(analysis, false, tv);
            if positive
                .iter()
                .chain(negative.iter())
                .any(|exact| exact.kind == ExactKeyKind::ConcreteRow)
            {
                info.has_concrete_row.insert(tv);
            }
            let mut positive_key = positive.iter().cloned().collect::<Vec<_>>();
            positive_key.sort();
            let mut negative_key = negative.iter().cloned().collect::<Vec<_>>();
            negative_key.sort();
            info.signatures.insert(
                tv,
                ExactSignature {
                    positive: positive_key,
                    negative: negative_key,
                },
            );
            info.positive.insert(tv, positive);
            info.negative.insert(tv, negative);
        }
        info
    }

    pub(super) fn signature(&self, tv: TypeVar) -> ExactSignature {
        self.signatures.get(&tv).cloned().unwrap_or_default()
    }

    pub(super) fn exact_occurrences(
        &self,
        positive: bool,
        tv: TypeVar,
    ) -> Option<&HashSet<ExactKey>> {
        let map = if positive {
            &self.positive
        } else {
            &self.negative
        };
        map.get(&tv)
    }

    pub(super) fn has_concrete_row(&self, tv: TypeVar) -> bool {
        self.has_concrete_row.contains(&tv)
    }
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

    use super::{
        AlongItem, ExactKeyKind, analyze_co_occurrences,
        analyze_group_co_occurrences_with_role_constraints, coalesce_by_co_occurrence,
        coalesce_by_co_occurrence_with_role_constraints_report,
        coalesce_by_co_occurrence_with_role_constraints_report_inner, exact_occurrences,
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
            None,
            true,
            &HashSet::new(),
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
        assert!(exact_occurrences(&analysis, false, a).is_empty());
    }

    #[test]
    fn analyze_group_co_occurrences_ignores_root_upper_direct_vars() {
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

        let analysis = analyze_group_co_occurrences_with_role_constraints(&scheme, &[]);
        assert!(!analysis.types.contains_key(&a));
        assert!(!analysis.effect_types.contains_key(&a));
        assert!(!analysis.effects.contains_key(&a));
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
    fn coalesce_by_co_occurrence_shares_open_row_residuals_across_polarities() {
        let negative_residual = fresh_type_var();
        let positive_residual = fresh_type_var();
        let io_path = Path {
            segments: vec![Name("io".to_string())],
        };
        let effect_item = CompactType {
            prims: HashSet::from([io_path]),
            ..CompactType::default()
        };
        let effect_row = |tail| CompactType {
            rows: vec![CompactRow {
                items: vec![effect_item.clone()],
                tail: Box::new(CompactType {
                    vars: HashSet::from([tail]),
                    ..CompactType::default()
                }),
            }],
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType {
                            funs: vec![crate::simplify::compact::CompactFun {
                                arg: CompactType::default(),
                                arg_eff: CompactType::default(),
                                ret_eff: effect_row(negative_residual),
                                ret: CompactType::default(),
                            }],
                            ..CompactType::default()
                        },
                        arg_eff: CompactType::default(),
                        ret_eff: effect_row(positive_residual),
                        ret: CompactType::default(),
                    }],
                    ..CompactType::default()
                },
                upper: CompactType::default(),
            },
            rec_vars: Default::default(),
        };

        let coalesced = coalesce_by_co_occurrence(&scheme);
        let outer = &coalesced.cty.lower.funs[0];
        let arg_fun = &outer.arg.funs[0];
        let arg_residual = single_var(&arg_fun.ret_eff.rows[0].tail.vars);
        assert_eq!(
            arg_fun.ret_eff.rows[0].tail.vars,
            HashSet::from([arg_residual])
        );
        assert_eq!(outer.ret_eff.vars, HashSet::from([arg_residual]));
        assert!(outer.ret_eff.rows[0].tail.vars.is_empty());
        assert!(outer.ret_eff.rows[0].tail.rows.is_empty());
    }

    #[test]
    fn coalesce_by_co_occurrence_merges_indistinguishable_effect_arg_vars() {
        let a = fresh_type_var();
        let b = fresh_type_var();
        let eff_path = Path {
            segments: vec![Name("eff".to_string())],
        };
        let effect_item = |tv| CompactType {
            cons: vec![CompactCon {
                path: eff_path.clone(),
                args: vec![CompactBounds {
                    self_var: None,
                    lower: CompactType {
                        vars: HashSet::from([tv]),
                        ..CompactType::default()
                    },
                    upper: CompactType {
                        vars: HashSet::from([tv]),
                        ..CompactType::default()
                    },
                }],
            }],
            ..CompactType::default()
        };
        let scheme = CompactTypeScheme {
            cty: CompactBounds {
                self_var: None,
                lower: CompactType {
                    funs: vec![crate::simplify::compact::CompactFun {
                        arg: CompactType::default(),
                        arg_eff: CompactType {
                            rows: vec![CompactRow {
                                items: vec![effect_item(a), effect_item(b)],
                                tail: Box::new(CompactType::default()),
                            }],
                            ..CompactType::default()
                        },
                        ret_eff: CompactType {
                            rows: vec![CompactRow {
                                items: vec![effect_item(a), effect_item(b)],
                                tail: Box::new(CompactType::default()),
                            }],
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
        let arg_items = &fun.arg_eff.rows[0].items;
        let ret_items = &fun.ret_eff.rows[0].items;
        for item in arg_items.iter().chain(ret_items.iter()) {
            let vars = &item.cons[0].args[0].lower.vars;
            assert_eq!(vars.len(), 1);
            assert_eq!(*vars.iter().next().unwrap(), a);
            let upper_vars = &item.cons[0].args[0].upper.vars;
            assert_eq!(upper_vars.len(), 1);
            assert_eq!(*upper_vars.iter().next().unwrap(), a);
        }
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
}
