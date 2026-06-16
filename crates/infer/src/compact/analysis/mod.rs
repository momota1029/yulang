use std::mem;

use rustc_hash::{FxHashMap, FxHashSet};

use super::*;
use crate::constraints::{ConstraintMachine, TypeLevel};
use crate::roles::{RoleInputVariance, RoleInputVarianceTable};

mod floor;
mod occurrence;
mod sandwich;

pub(crate) use floor::{
    coalesce_floor_interval_equalities, coalesce_floor_variable_sandwiches,
    collect_interval_dominance_constraints, eliminate_floor_redundant_variables,
};
pub(crate) use occurrence::normalize_var_substitutions;
use occurrence::*;
use sandwich::*;
#[cfg(test)]
pub(crate) use sandwich::{sandwich_compact_root, sandwich_compact_root_with_roles};

#[cfg(test)]
pub(crate) fn eliminate_polar_variables(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
) -> Vec<CompactVarSubstitution> {
    eliminate_polar_variables_with_roles_and_non_generic(
        machine,
        boundary,
        root,
        &mut [],
        &FxHashSet::default(),
    )
}

fn eliminate_polar_variables_with_roles_and_non_generic(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> Vec<CompactVarSubstitution> {
    let polarity = collect_var_polarities(root, roles);
    rewrite_root_and_role_vars(root, roles, |var| {
        if !is_simplification_candidate(machine, boundary, var, non_generic)
            || polarity.is_bipolar(var)
        {
            Some(var)
        } else {
            None
        }
    })
}

#[cfg(test)]
pub(crate) fn coalesce_by_co_occurrence(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
) -> Vec<CompactVarSubstitution> {
    coalesce_by_co_occurrence_with_roles_and_non_generic(
        machine,
        boundary,
        root,
        &mut [],
        &FxHashSet::default(),
    )
}

fn coalesce_by_co_occurrence_with_roles_and_non_generic(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> Vec<CompactVarSubstitution> {
    let co_occurrences = collect_co_occurrences(root, roles);
    let subst = co_occurrences.substitution(machine, boundary, non_generic);
    if subst.is_empty() {
        return Vec::new();
    }
    rewrite_root_and_role_vars(root, roles, |var| subst.rewrite(var))
}

#[cfg(test)]
pub(crate) fn simplify_compact_root(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
) -> CompactSimplification {
    simplify_compact_root_with_roles_and_non_generic(
        machine,
        boundary,
        root,
        &mut [],
        &FxHashSet::default(),
    )
}

pub(crate) fn simplify_compact_root_with_roles_and_non_generic(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> CompactSimplification {
    simplify_compact_root_with_role_arg_polarities_and_non_generic(
        machine,
        boundary,
        root,
        roles,
        non_generic,
    )
}

pub(crate) fn simplify_compact_root_with_role_variance_table_and_non_generic(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    role_variances: &RoleInputVarianceTable,
    non_generic: &FxHashSet<TypeVar>,
) -> CompactSimplification {
    apply_role_input_variances_to_roles(roles, role_variances);
    simplify_compact_root_with_role_arg_polarities_and_non_generic(
        machine,
        boundary,
        root,
        roles,
        non_generic,
    )
}

fn apply_role_input_variances_to_roles(
    roles: &mut [CompactRoleConstraint],
    role_variances: &RoleInputVarianceTable,
) {
    for role in roles {
        for (index, input) in role.inputs.iter_mut().enumerate() {
            let variance = role_variances
                .input_or_invariant(&role.role, index)
                .flipped_for_where();
            input.polarity = compact_role_arg_polarity_from_variance(variance);
        }
    }
}

fn compact_role_arg_polarity_from_variance(variance: RoleInputVariance) -> CompactRoleArgPolarity {
    match variance {
        RoleInputVariance::Covariant => CompactRoleArgPolarity::Covariant,
        RoleInputVariance::Contravariant => CompactRoleArgPolarity::Contravariant,
        RoleInputVariance::Unused | RoleInputVariance::Invariant => {
            CompactRoleArgPolarity::Invariant
        }
    }
}

fn simplify_compact_root_with_role_arg_polarities_and_non_generic(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> CompactSimplification {
    collapse_pinned_intervals_with_roles_and_non_generic(
        machine,
        boundary,
        root,
        roles,
        non_generic,
    );
    let mut substitutions = Vec::new();
    substitutions.extend(simplify_polar_and_co_occurrence_to_fixed_point(
        machine,
        boundary,
        root,
        roles,
        non_generic,
    ));
    let sandwiches = sandwich_compact_root_with_roles_and_non_generic(
        machine,
        boundary,
        root,
        roles,
        non_generic,
    );
    substitutions.extend(simplify_polar_and_co_occurrence_to_fixed_point(
        machine,
        boundary,
        root,
        roles,
        non_generic,
    ));
    CompactSimplification {
        substitutions: normalize_var_substitutions(substitutions),
        sandwiches,
    }
}

/// 世代化で確定した def のスキームに掛ける、level 保護の床下だけの併合パス。
///
/// simplify は `boundary` 以下の変数を不可侵にするため、impl requirement などの足場が
/// 低 level に生んだ変数は、不変区間の両側出現で等値が確定していても junk として残る。
/// 区間由来の等式は demand 自体が機械側で強制する等値なので、スキームに自由変数として
/// 残る床下の変数でも併合してよい。一方、極性消去や通常の共起併合は「このスキーム内の
/// 全出現」を根拠にするため、他 def と共有されうる床下の変数には適用できない。
/// ここでは区間等式だけを使う。一回パスで、不動点反復には入れない。
fn simplify_polar_and_co_occurrence_to_fixed_point(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> Vec<CompactVarSubstitution> {
    let mut substitutions = Vec::new();
    loop {
        let eliminated = eliminate_polar_variables_with_roles_and_non_generic(
            machine,
            boundary,
            root,
            roles,
            non_generic,
        );
        let coalesced = coalesce_by_co_occurrence_with_roles_and_non_generic(
            machine,
            boundary,
            root,
            roles,
            non_generic,
        );
        let changed = !eliminated.is_empty() || !coalesced.is_empty();
        substitutions.extend(eliminated);
        substitutions.extend(coalesced);
        if !changed {
            break;
        }
    }
    substitutions
}

/// 上下界が同じ concrete 成分で釘付けされた不変 interval を、その concrete に畳む。
/// `[α∨T, β∧T]` は lower ≤ upper より中心が T に挟まれて確定する（α ≤ T ≤ …）。
/// interval の lower/upper 両側に残る変数は bipolar で polar 消去が効かないので、ここで畳む。
/// 同伴していた変数の他出現はそのまま残し、後続の polar 消去 / 共起併合に任せる。
/// bottom-up の一回パスで、不動点ループには入れない。
fn collapse_pinned_intervals_with_roles_and_non_generic(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) {
    let rec_vars = root
        .rec_vars
        .iter()
        .map(|rec| rec.var)
        .collect::<FxHashSet<_>>();
    let mut ctx = CollapseContext {
        machine,
        boundary,
        non_generic,
        rec_vars: &rec_vars,
    };
    collapse_intervals_in_type(&mut root.root, &mut ctx);
    for rec in &mut root.rec_vars {
        collapse_intervals_in_bounds(&mut rec.bounds, &mut ctx, false);
    }
    for role in roles {
        for input in &mut role.inputs {
            collapse_intervals_in_bounds(&mut input.bounds, &mut ctx, false);
        }
        for associated in &mut role.associated {
            collapse_intervals_in_bounds(&mut associated.value.bounds, &mut ctx, false);
        }
    }
}

struct CollapseContext<'a> {
    machine: &'a ConstraintMachine,
    boundary: TypeLevel,
    non_generic: &'a FxHashSet<TypeVar>,
    rec_vars: &'a FxHashSet<TypeVar>,
}

fn collapse_intervals_in_type(ty: &mut CompactType, ctx: &mut CollapseContext) {
    for (path, args) in &mut ty.cons {
        // ref の payload は `Neu::Bounds` の形そのものに意味がある（ref selection probe が
        // positional に var を読む）ので、直下の interval は畳まない。
        let keep_interval = crate::std_paths::is_control_var_ref_type(path);
        for arg in args {
            collapse_intervals_in_bounds(arg, ctx, keep_interval);
        }
    }
    for fun in &mut ty.funs {
        collapse_intervals_in_type(&mut fun.arg, ctx);
        collapse_intervals_in_type(&mut fun.arg_eff, ctx);
        collapse_intervals_in_type(&mut fun.ret_eff, ctx);
        collapse_intervals_in_type(&mut fun.ret, ctx);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            collapse_intervals_in_type(&mut field.value, ctx);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            collapse_intervals_in_type(&mut field.value, ctx);
        }
        collapse_intervals_in_type(&mut spread.tail, ctx);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                collapse_intervals_in_type(payload, ctx);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            collapse_intervals_in_type(item, ctx);
        }
    }
    for row in &mut ty.rows {
        for args in row.items.values_mut() {
            for arg in args {
                collapse_intervals_in_bounds(arg, ctx, false);
            }
        }
        collapse_intervals_in_type(&mut row.tail, ctx);
    }
}

fn collapse_intervals_in_bounds(
    bounds: &mut CompactBounds,
    ctx: &mut CollapseContext,
    keep_interval: bool,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            collapse_intervals_in_type(lower, ctx);
            collapse_intervals_in_type(upper, ctx);
            if keep_interval {
                return;
            }
            if let Some(collapsed) = try_collapse_pinned_interval(lower, upper, ctx) {
                *bounds = collapsed;
            }
        }
        CompactBounds::Con { path, args } => {
            let keep_interval = crate::std_paths::is_control_var_ref_type(path);
            for arg in args {
                collapse_intervals_in_bounds(arg, ctx, keep_interval);
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                collapse_intervals_in_bounds(item, ctx, false);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collapse_intervals_in_bounds(arg, ctx, false);
            collapse_intervals_in_bounds(arg_eff, ctx, false);
            collapse_intervals_in_bounds(ret_eff, ctx, false);
            collapse_intervals_in_bounds(ret, ctx, false);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collapse_intervals_in_bounds(&mut field.value, ctx, false);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collapse_intervals_in_bounds(payload, ctx, false);
                }
            }
        }
    }
}

fn try_collapse_pinned_interval(
    lower: &CompactType,
    upper: &CompactType,
    ctx: &CollapseContext,
) -> Option<CompactBounds> {
    for var in lower.vars.iter().chain(upper.vars.iter()) {
        if ctx.rec_vars.contains(&var.var)
            || !is_simplification_candidate(ctx.machine, ctx.boundary, var.var, ctx.non_generic)
        {
            return None;
        }
    }
    let pinned_lower = sole_concrete_component(lower)?;
    let pinned_upper = sole_concrete_component(upper)?;
    if pinned_lower != pinned_upper {
        return None;
    }
    concrete_compact_bounds(&pinned_lower)
}

/// vars を無視して concrete 成分がちょうど 1 つの時だけそれを返す。
fn sole_concrete_component(ty: &CompactType) -> Option<CompactType> {
    if ty.never {
        return None;
    }
    let mut found = Vec::new();
    found.extend(ty.builtins.iter().copied().map(CompactType::from_builtin));
    found.extend(
        compact_con_entries(&ty.cons)
            .into_iter()
            .map(CompactType::from_con),
    );
    found.extend(ty.funs.iter().cloned().map(CompactType::from_fun));
    found.extend(ty.records.iter().cloned().map(CompactType::from_record));
    found.extend(
        ty.record_spreads
            .iter()
            .cloned()
            .map(CompactType::from_record_spread),
    );
    found.extend(
        ty.poly_variants
            .iter()
            .cloned()
            .map(CompactType::from_poly_variant),
    );
    found.extend(ty.tuples.iter().cloned().map(CompactType::from_tuple));
    found.extend(ty.rows.iter().cloned().map(CompactType::from_row));
    (found.len() == 1).then(|| found.remove(0))
}

/// 単一 concrete の CompactType を CompactBounds に変換する。表現できない形は None。
fn concrete_compact_bounds(ty: &CompactType) -> Option<CompactBounds> {
    if !ty.vars.is_empty() || ty.never {
        return None;
    }
    let cons = compact_con_entries(&ty.cons);
    match (
        ty.builtins.as_slice(),
        cons.as_slice(),
        ty.tuples.as_slice(),
        ty.funs.as_slice(),
        ty.records.as_slice(),
    ) {
        ([builtin], [], [], [], [])
            if ty.record_spreads.is_empty()
                && ty.poly_variants.is_empty()
                && ty.rows.is_empty() =>
        {
            Some(CompactBounds::Con {
                path: vec![builtin.surface_name().into()],
                args: Vec::new(),
            })
        }
        ([], [con], [], [], [])
            if ty.record_spreads.is_empty()
                && ty.poly_variants.is_empty()
                && ty.rows.is_empty() =>
        {
            Some(CompactBounds::Con {
                path: con.path.clone(),
                args: con.args.clone(),
            })
        }
        ([], [], [tuple], [], [])
            if ty.record_spreads.is_empty()
                && ty.poly_variants.is_empty()
                && ty.rows.is_empty() =>
        {
            let items = tuple
                .items
                .iter()
                .map(component_compact_bounds)
                .collect::<Option<Vec<_>>>()?;
            Some(CompactBounds::Tuple { items })
        }
        _ => None,
    }
}

/// tuple 成分など、入れ子位置の CompactType を CompactBounds へ。単一 var はそのまま interval に包む。
fn component_compact_bounds(ty: &CompactType) -> Option<CompactBounds> {
    if ty.vars.len() == 1 && sole_concrete_component(ty).is_none() && !ty.never {
        let var = ty.vars[0].var;
        return Some(CompactBounds::Interval {
            lower: CompactType::from_var(CompactVar::plain(var)),
            upper: CompactType::from_var(CompactVar::plain(var)),
        });
    }
    if ty.vars.is_empty() {
        return concrete_compact_bounds(ty);
    }
    None
}

fn is_simplification_candidate(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    var: TypeVar,
    non_generic: &FxHashSet<TypeVar>,
) -> bool {
    machine.level_of(var) >= boundary && !non_generic.contains(&var)
}
