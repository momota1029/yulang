use std::mem;

use rustc_hash::{FxHashMap, FxHashSet};

use super::*;
use crate::constraints::{ConstraintMachine, TypeLevel};

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
pub(crate) fn coalesce_floor_interval_equalities(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
) -> Vec<CompactVarSubstitution> {
    let co_occurrences = collect_co_occurrences(root, roles);
    let mut union = VarUnion::default();
    for (alpha, beta) in &co_occurrences.interval_equalities {
        let alpha_floor = machine.level_of(*alpha) <= boundary;
        let beta_floor = machine.level_of(*beta) <= boundary;
        // 床上同士は通常の simplify（共起分析の区間規則）が併合する。
        if !alpha_floor && !beta_floor {
            continue;
        }
        let rep = [*alpha, *beta]
            .into_iter()
            .min_by_key(|var| (machine.level_of(*var), var.0))
            .expect("pair is non-empty");
        union.union_to(rep, *alpha);
        union.union_to(rep, *beta);
    }
    let subst = union.into_substitution(FxHashSet::default());
    if subst.is_empty() {
        return Vec::new();
    }
    rewrite_root_and_role_vars(root, roles, |var| subst.rewrite(var))
}

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
/// interval の self_var は構成上 bipolar で polar 消去が効かないので、ここで畳む。
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
            collapse_intervals_in_type(&mut input.lower, &mut ctx);
            collapse_intervals_in_type(&mut input.upper, &mut ctx);
        }
        for associated in &mut role.associated {
            collapse_intervals_in_type(&mut associated.value.lower, &mut ctx);
            collapse_intervals_in_type(&mut associated.value.upper, &mut ctx);
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
    for con in &mut ty.cons {
        // ref の payload は `Neu::Bounds` の形そのものに意味がある（ref selection probe が
        // positional に var を読む）ので、直下の interval は畳まない。
        let keep_interval = crate::std_paths::is_control_var_ref_type(&con.path);
        for arg in &mut con.args {
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
        for item in &mut row.items {
            collapse_intervals_in_type(item, ctx);
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
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            collapse_intervals_in_type(lower, ctx);
            collapse_intervals_in_type(upper, ctx);
            if keep_interval {
                return;
            }
            if let Some(collapsed) = try_collapse_pinned_interval(*self_var, lower, upper, ctx) {
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
    self_var: TypeVar,
    lower: &CompactType,
    upper: &CompactType,
    ctx: &CollapseContext,
) -> Option<CompactBounds> {
    if ctx.rec_vars.contains(&self_var)
        || !is_simplification_candidate(ctx.machine, ctx.boundary, self_var, ctx.non_generic)
    {
        return None;
    }
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
    found.extend(ty.cons.iter().cloned().map(CompactType::from_con));
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
    match (
        ty.builtins.as_slice(),
        ty.cons.as_slice(),
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
            self_var: var,
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

#[cfg(test)]
pub(crate) fn sandwich_compact_root(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
) -> Vec<CompactSandwich> {
    sandwich_compact_root_with_roles_and_non_generic(
        machine,
        boundary,
        root,
        &mut [],
        &FxHashSet::default(),
    )
}

#[cfg(test)]
pub(crate) fn sandwich_compact_root_with_roles(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
) -> Vec<CompactSandwich> {
    sandwich_compact_root_with_roles_and_non_generic(
        machine,
        boundary,
        root,
        roles,
        &FxHashSet::default(),
    )
}

fn sandwich_compact_root_with_roles_and_non_generic(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> Vec<CompactSandwich> {
    let mut fresh = FreshCompactVars::new(root);
    let mut sandwiches = FxHashMap::default();
    loop {
        let verdicts = compute_sandwich_verdicts(machine, boundary, root, roles, non_generic);
        if verdicts.lift.is_empty() {
            return sorted_sandwiches(sandwiches);
        }

        let mut changed = false;
        root.root = sandwich_type(
            machine,
            boundary,
            mem::take(&mut root.root),
            &verdicts,
            &mut fresh,
            &mut changed,
            &mut sandwiches,
        );
        for rec in &mut root.rec_vars {
            rec.bounds = sandwich_bounds(
                machine,
                boundary,
                mem::replace(&mut rec.bounds, empty_interval(rec.var)),
                &verdicts,
                &mut fresh,
                &mut changed,
                &mut sandwiches,
            );
        }
        for role in &mut *roles {
            sandwich_role(
                machine,
                boundary,
                role,
                &verdicts,
                &mut fresh,
                &mut changed,
                &mut sandwiches,
            );
        }
        if !changed {
            return sorted_sandwiches(sandwiches);
        }
    }
}

fn empty_interval(self_var: TypeVar) -> CompactBounds {
    CompactBounds::Interval {
        self_var,
        lower: CompactType::default(),
        upper: CompactType::default(),
    }
}

#[derive(Default)]
struct SandwichVerdicts {
    lift: FxHashMap<TypeVar, SandwichKind>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum SandwichVerdict {
    Single(SandwichKind),
    NoLift,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum SandwichKind {
    Con(Vec<String>, usize),
    Tuple(usize),
    Fun,
    ConcreteButNotLiftable,
}

fn compute_sandwich_verdicts(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &CompactRoot,
    roles: &[CompactRoleConstraint],
    non_generic: &FxHashSet<TypeVar>,
) -> SandwichVerdicts {
    let mut verdicts = FxHashMap::default();
    visit_type_for_sandwich_verdict(&root.root, &mut verdicts);
    for rec in &root.rec_vars {
        visit_bounds_for_sandwich_verdict(&rec.bounds, &mut verdicts);
    }
    for role in roles {
        visit_role_for_sandwich_verdict(role, &mut verdicts);
    }

    let rec_vars = root
        .rec_vars
        .iter()
        .map(|rec| rec.var)
        .collect::<FxHashSet<_>>();
    let mut lift = FxHashMap::default();
    for (var, verdict) in verdicts {
        if rec_vars.contains(&var)
            || !is_simplification_candidate(machine, boundary, var, non_generic)
        {
            continue;
        }
        match verdict {
            SandwichVerdict::Single(
                kind @ (SandwichKind::Con(..) | SandwichKind::Tuple(_) | SandwichKind::Fun),
            ) => {
                lift.insert(var, kind);
            }
            _ => {}
        }
    }
    SandwichVerdicts { lift }
}

fn visit_role_for_sandwich_verdict(
    role: &CompactRoleConstraint,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    for input in &role.inputs {
        visit_role_arg_for_sandwich_verdict(input, verdicts);
    }
    for associated in &role.associated {
        visit_role_arg_for_sandwich_verdict(&associated.value, verdicts);
    }
}

fn visit_role_arg_for_sandwich_verdict(
    arg: &CompactRoleArg,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    visit_type_for_sandwich_verdict(&arg.lower, verdicts);
    visit_type_for_sandwich_verdict(&arg.upper, verdicts);
}

fn visit_type_for_sandwich_verdict(
    ty: &CompactType,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    let kinds = sandwich_kinds(ty);
    for var in &ty.vars {
        record_sandwich_var_occurrence(verdicts, var.var, &kinds);
    }

    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds_for_sandwich_verdict(arg, verdicts);
        }
    }
    for fun in &ty.funs {
        visit_type_for_sandwich_verdict(&fun.arg, verdicts);
        visit_type_for_sandwich_verdict(&fun.arg_eff, verdicts);
        visit_type_for_sandwich_verdict(&fun.ret_eff, verdicts);
        visit_type_for_sandwich_verdict(&fun.ret, verdicts);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_for_sandwich_verdict(&field.value, verdicts);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_for_sandwich_verdict(&field.value, verdicts);
        }
        visit_type_for_sandwich_verdict(&spread.tail, verdicts);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_for_sandwich_verdict(payload, verdicts);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_for_sandwich_verdict(item, verdicts);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            visit_type_for_sandwich_verdict(item, verdicts);
        }
        visit_type_for_sandwich_verdict(&row.tail, verdicts);
    }
}

fn visit_bounds_for_sandwich_verdict(
    bounds: &CompactBounds,
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            visit_type_for_sandwich_verdict(lower, verdicts);
            visit_type_for_sandwich_verdict(upper, verdicts);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_for_sandwich_verdict(arg, verdicts);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_for_sandwich_verdict(arg, verdicts);
            visit_bounds_for_sandwich_verdict(arg_eff, verdicts);
            visit_bounds_for_sandwich_verdict(ret_eff, verdicts);
            visit_bounds_for_sandwich_verdict(ret, verdicts);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_for_sandwich_verdict(&field.value, verdicts);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_for_sandwich_verdict(payload, verdicts);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_for_sandwich_verdict(item, verdicts);
            }
        }
    }
}

fn sandwich_kinds(ty: &CompactType) -> Vec<SandwichKind> {
    let mut kinds = Vec::new();
    for con in &ty.cons {
        kinds.push(SandwichKind::Con(con.path.clone(), con.args.len()));
    }
    for tuple in &ty.tuples {
        kinds.push(SandwichKind::Tuple(tuple.items.len()));
    }
    if !ty.funs.is_empty() {
        kinds.push(SandwichKind::Fun);
    }
    if !ty.builtins.is_empty()
        || !ty.records.is_empty()
        || !ty.record_spreads.is_empty()
        || !ty.poly_variants.is_empty()
        || !ty.rows.is_empty()
    {
        kinds.push(SandwichKind::ConcreteButNotLiftable);
    }
    kinds
}

fn record_sandwich_var_occurrence(
    verdicts: &mut FxHashMap<TypeVar, SandwichVerdict>,
    var: TypeVar,
    kinds: &[SandwichKind],
) {
    let occurrence = if kinds.len() == 1 {
        SandwichVerdict::Single(kinds[0].clone())
    } else {
        SandwichVerdict::NoLift
    };
    let merged = match (verdicts.get(&var), &occurrence) {
        (None, _) => occurrence,
        (Some(SandwichVerdict::NoLift), _) | (_, SandwichVerdict::NoLift) => {
            SandwichVerdict::NoLift
        }
        (Some(SandwichVerdict::Single(lhs)), SandwichVerdict::Single(rhs)) => {
            if lhs == rhs {
                SandwichVerdict::Single(lhs.clone())
            } else {
                SandwichVerdict::NoLift
            }
        }
    };
    verdicts.insert(var, merged);
}

fn sandwich_type(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    mut ty: CompactType,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) -> CompactType {
    ty.cons = ty
        .cons
        .into_iter()
        .map(|con| CompactCon {
            path: con.path,
            args: con
                .args
                .into_iter()
                .map(|arg| {
                    sandwich_bounds(machine, boundary, arg, verdicts, fresh, changed, sandwiches)
                })
                .collect(),
        })
        .collect();
    for fun in &mut ty.funs {
        fun.arg = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.arg),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
        fun.arg_eff = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.arg_eff),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
        fun.ret_eff = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.ret_eff),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
        fun.ret = sandwich_type(
            machine,
            boundary,
            mem::take(&mut fun.ret),
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            field.value = sandwich_type(
                machine,
                boundary,
                mem::take(&mut field.value),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            field.value = sandwich_type(
                machine,
                boundary,
                mem::take(&mut field.value),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
        spread.tail = Box::new(sandwich_type(
            machine,
            boundary,
            *mem::take(&mut spread.tail),
            verdicts,
            fresh,
            changed,
            sandwiches,
        ));
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                *payload = sandwich_type(
                    machine,
                    boundary,
                    mem::take(payload),
                    verdicts,
                    fresh,
                    changed,
                    sandwiches,
                );
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            *item = sandwich_type(
                machine,
                boundary,
                mem::take(item),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            *item = sandwich_type(
                machine,
                boundary,
                mem::take(item),
                verdicts,
                fresh,
                changed,
                sandwiches,
            );
        }
        row.tail = Box::new(sandwich_type(
            machine,
            boundary,
            *mem::take(&mut row.tail),
            verdicts,
            fresh,
            changed,
            sandwiches,
        ));
    }
    ty
}

fn sandwich_bounds(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    bounds: CompactBounds,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) -> CompactBounds {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            if let Some((center, kind, lifted)) =
                try_lift_interval(machine, boundary, self_var, &lower, &upper, verdicts, fresh)
            {
                *changed = true;
                record_sandwich(sandwiches, center, &kind);
                sandwich_bounds(
                    machine, boundary, lifted, verdicts, fresh, changed, sandwiches,
                )
            } else {
                CompactBounds::Interval {
                    self_var,
                    lower: sandwich_type(
                        machine, boundary, lower, verdicts, fresh, changed, sandwiches,
                    ),
                    upper: sandwich_type(
                        machine, boundary, upper, verdicts, fresh, changed, sandwiches,
                    ),
                }
            }
        }
        CompactBounds::Con { path, args } => CompactBounds::Con {
            path,
            args: args
                .into_iter()
                .map(|arg| {
                    sandwich_bounds(machine, boundary, arg, verdicts, fresh, changed, sandwiches)
                })
                .collect(),
        },
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => CompactBounds::Fun {
            arg: Box::new(sandwich_bounds(
                machine, boundary, *arg, verdicts, fresh, changed, sandwiches,
            )),
            arg_eff: Box::new(sandwich_bounds(
                machine, boundary, *arg_eff, verdicts, fresh, changed, sandwiches,
            )),
            ret_eff: Box::new(sandwich_bounds(
                machine, boundary, *ret_eff, verdicts, fresh, changed, sandwiches,
            )),
            ret: Box::new(sandwich_bounds(
                machine, boundary, *ret, verdicts, fresh, changed, sandwiches,
            )),
        },
        CompactBounds::Record { fields } => CompactBounds::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: sandwich_bounds(
                        machine,
                        boundary,
                        field.value,
                        verdicts,
                        fresh,
                        changed,
                        sandwiches,
                    ),
                    optional: field.optional,
                })
                .collect(),
        },
        CompactBounds::PolyVariant { items } => CompactBounds::PolyVariant {
            items: items
                .into_iter()
                .map(|(name, payloads)| {
                    (
                        name,
                        payloads
                            .into_iter()
                            .map(|payload| {
                                sandwich_bounds(
                                    machine, boundary, payload, verdicts, fresh, changed,
                                    sandwiches,
                                )
                            })
                            .collect(),
                    )
                })
                .collect(),
        },
        CompactBounds::Tuple { items } => CompactBounds::Tuple {
            items: items
                .into_iter()
                .map(|item| {
                    sandwich_bounds(
                        machine, boundary, item, verdicts, fresh, changed, sandwiches,
                    )
                })
                .collect(),
        },
    }
}

fn sandwich_role(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    role: &mut CompactRoleConstraint,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) {
    for input in &mut role.inputs {
        sandwich_role_arg(
            machine, boundary, input, verdicts, fresh, changed, sandwiches,
        );
    }
    for associated in &mut role.associated {
        sandwich_role_arg(
            machine,
            boundary,
            &mut associated.value,
            verdicts,
            fresh,
            changed,
            sandwiches,
        );
    }
}

fn sandwich_role_arg(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    arg: &mut CompactRoleArg,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
    changed: &mut bool,
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
) {
    arg.lower = sandwich_type(
        machine,
        boundary,
        mem::take(&mut arg.lower),
        verdicts,
        fresh,
        changed,
        sandwiches,
    );
    arg.upper = sandwich_type(
        machine,
        boundary,
        mem::take(&mut arg.upper),
        verdicts,
        fresh,
        changed,
        sandwiches,
    );
}

fn try_lift_interval(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    self_var: TypeVar,
    lower: &CompactType,
    upper: &CompactType,
    verdicts: &SandwichVerdicts,
    fresh: &mut FreshCompactVars,
) -> Option<(TypeVar, SandwichKind, CompactBounds)> {
    let center = if verdicts.lift.contains_key(&self_var) {
        self_var
    } else {
        if machine.level_of(self_var) < boundary {
            return None;
        }
        common_var_in_types(lower, upper).filter(|var| verdicts.lift.contains_key(var))?
    };
    let kind = verdicts.lift.get(&center)?.clone();
    let lifted = match kind.clone() {
        SandwichKind::Con(path, arity) => {
            let lower_args = single_con(lower, &path, arity)?;
            let upper_args = single_con(upper, &path, arity)?;
            CompactBounds::Con {
                path,
                args: lower_args
                    .iter()
                    .zip(upper_args)
                    .map(|(lower, upper)| merge_arg_bounds(lower, upper, fresh))
                    .collect(),
            }
        }
        SandwichKind::Tuple(arity) => {
            let lower_items = single_tuple(lower, arity)?;
            let upper_items = single_tuple(upper, arity)?;
            CompactBounds::Tuple {
                items: lower_items
                    .iter()
                    .zip(upper_items)
                    .map(|(lower, upper)| interval_from_types(lower.clone(), upper.clone(), fresh))
                    .collect(),
            }
        }
        SandwichKind::Fun => {
            let lower_fun = single_fun(lower)?;
            let upper_fun = single_fun(upper)?;
            CompactBounds::Fun {
                arg: Box::new(interval_from_types(
                    upper_fun.arg.clone(),
                    lower_fun.arg.clone(),
                    fresh,
                )),
                arg_eff: Box::new(interval_from_types(
                    upper_fun.arg_eff.clone(),
                    lower_fun.arg_eff.clone(),
                    fresh,
                )),
                ret_eff: Box::new(interval_from_types(
                    lower_fun.ret_eff.clone(),
                    upper_fun.ret_eff.clone(),
                    fresh,
                )),
                ret: Box::new(interval_from_types(
                    lower_fun.ret.clone(),
                    upper_fun.ret.clone(),
                    fresh,
                )),
            }
        }
        SandwichKind::ConcreteButNotLiftable => return None,
    };
    Some((center, kind, lifted))
}

fn record_sandwich(
    sandwiches: &mut FxHashMap<TypeVar, CompactSandwichKind>,
    var: TypeVar,
    kind: &SandwichKind,
) {
    let Some(kind) = compact_sandwich_kind(kind) else {
        return;
    };
    sandwiches.insert(var, kind);
}

fn compact_sandwich_kind(kind: &SandwichKind) -> Option<CompactSandwichKind> {
    match kind {
        SandwichKind::Con(path, arity) => Some(CompactSandwichKind::Con {
            path: path.clone(),
            arity: *arity,
        }),
        SandwichKind::Tuple(arity) => Some(CompactSandwichKind::Tuple { arity: *arity }),
        SandwichKind::Fun => Some(CompactSandwichKind::Fun),
        SandwichKind::ConcreteButNotLiftable => None,
    }
}

fn sorted_sandwiches(sandwiches: FxHashMap<TypeVar, CompactSandwichKind>) -> Vec<CompactSandwich> {
    let mut sandwiches = sandwiches
        .into_iter()
        .map(|(var, kind)| CompactSandwich { var, kind })
        .collect::<Vec<_>>();
    sandwiches.sort_by_key(|sandwich| sandwich.var.0);
    sandwiches
}

fn merge_arg_bounds(
    lower_arg: &CompactBounds,
    upper_arg: &CompactBounds,
    fresh: &mut FreshCompactVars,
) -> CompactBounds {
    match (lower_arg, upper_arg) {
        (
            CompactBounds::Interval {
                lower: lower_lower,
                upper: lower_upper,
                ..
            },
            CompactBounds::Interval {
                lower: upper_lower,
                upper: upper_upper,
                ..
            },
        ) => interval_from_types(
            merge_compact_types(true, lower_lower.clone(), upper_lower.clone()),
            merge_compact_types(false, lower_upper.clone(), upper_upper.clone()),
            fresh,
        ),
        _ if lower_arg == upper_arg => lower_arg.clone(),
        _ => lower_arg.clone(),
    }
}

fn interval_from_types(
    lower: CompactType,
    upper: CompactType,
    fresh: &mut FreshCompactVars,
) -> CompactBounds {
    let self_var = common_var_in_types(&lower, &upper).unwrap_or_else(|| fresh.fresh());
    CompactBounds::Interval {
        self_var,
        lower,
        upper,
    }
}

fn common_var_in_types(lower: &CompactType, upper: &CompactType) -> Option<TypeVar> {
    lower
        .vars
        .iter()
        .map(|var| var.var)
        .filter(|lower_var| {
            upper
                .vars
                .iter()
                .any(|upper_var| upper_var.var == *lower_var)
        })
        .min_by_key(|var| var.0)
}

fn single_con<'a>(
    ty: &'a CompactType,
    path: &[String],
    arity: usize,
) -> Option<&'a [CompactBounds]> {
    if ty.cons.len() == 1
        && ty.cons[0].path == path
        && ty.cons[0].args.len() == arity
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.cons[0].args)
    } else {
        None
    }
}

fn single_tuple(ty: &CompactType, arity: usize) -> Option<&[CompactType]> {
    if ty.tuples.len() == 1
        && ty.tuples[0].items.len() == arity
        && ty.cons.is_empty()
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.tuples[0].items)
    } else {
        None
    }
}

fn single_fun(ty: &CompactType) -> Option<&CompactFun> {
    if ty.funs.len() == 1
        && ty.cons.is_empty()
        && ty.builtins.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
    {
        Some(&ty.funs[0])
    } else {
        None
    }
}

struct FreshCompactVars {
    next: u32,
}

impl FreshCompactVars {
    fn new(root: &CompactRoot) -> Self {
        Self {
            next: max_type_var_in_root(root).map_or(0, |var| var.0 + 1),
        }
    }

    fn fresh(&mut self) -> TypeVar {
        let var = TypeVar(self.next);
        self.next += 1;
        var
    }
}

fn max_type_var_in_root(root: &CompactRoot) -> Option<TypeVar> {
    let mut max = None;
    max_type_var_in_type(&root.root, &mut max);
    for rec in &root.rec_vars {
        update_max_type_var(rec.var, &mut max);
        max_type_var_in_bounds(&rec.bounds, &mut max);
    }
    max
}

fn max_type_var_in_type(ty: &CompactType, max: &mut Option<TypeVar>) {
    for var in &ty.vars {
        update_max_type_var(var.var, max);
    }
    for con in &ty.cons {
        for arg in &con.args {
            max_type_var_in_bounds(arg, max);
        }
    }
    for fun in &ty.funs {
        max_type_var_in_type(&fun.arg, max);
        max_type_var_in_type(&fun.arg_eff, max);
        max_type_var_in_type(&fun.ret_eff, max);
        max_type_var_in_type(&fun.ret, max);
    }
    for record in &ty.records {
        for field in &record.fields {
            max_type_var_in_type(&field.value, max);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            max_type_var_in_type(&field.value, max);
        }
        max_type_var_in_type(&spread.tail, max);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                max_type_var_in_type(payload, max);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            max_type_var_in_type(item, max);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            max_type_var_in_type(item, max);
        }
        max_type_var_in_type(&row.tail, max);
    }
}

fn max_type_var_in_bounds(bounds: &CompactBounds, max: &mut Option<TypeVar>) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            update_max_type_var(*self_var, max);
            max_type_var_in_type(lower, max);
            max_type_var_in_type(upper, max);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                max_type_var_in_bounds(arg, max);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            max_type_var_in_bounds(arg, max);
            max_type_var_in_bounds(arg_eff, max);
            max_type_var_in_bounds(ret_eff, max);
            max_type_var_in_bounds(ret, max);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                max_type_var_in_bounds(&field.value, max);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    max_type_var_in_bounds(payload, max);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                max_type_var_in_bounds(item, max);
            }
        }
    }
}

fn update_max_type_var(var: TypeVar, max: &mut Option<TypeVar>) {
    if max.is_none_or(|current| var.0 > current.0) {
        *max = Some(var);
    }
}

#[derive(Default)]
struct VarPolarities {
    positive: FxHashSet<TypeVar>,
    negative: FxHashSet<TypeVar>,
}

impl VarPolarities {
    fn record(&mut self, var: TypeVar, polarity: Polarity) {
        match polarity {
            Polarity::Positive => {
                self.positive.insert(var);
            }
            Polarity::Negative => {
                self.negative.insert(var);
            }
        }
    }

    fn is_bipolar(&self, var: TypeVar) -> bool {
        self.positive.contains(&var) && self.negative.contains(&var)
    }
}

fn collect_var_polarities(root: &CompactRoot, roles: &[CompactRoleConstraint]) -> VarPolarities {
    let mut out = VarPolarities::default();
    visit_type_polarity(&root.root, Polarity::Positive, &mut out);
    for rec in &root.rec_vars {
        visit_bounds_polarity(&rec.bounds, Polarity::Positive, &mut out);
    }
    for role in roles {
        visit_role_polarity(role, &mut out);
    }
    out
}

fn visit_role_polarity(role: &CompactRoleConstraint, out: &mut VarPolarities) {
    for input in &role.inputs {
        visit_role_arg_polarity(input, out);
    }
    for associated in &role.associated {
        visit_role_arg_polarity(&associated.value, out);
    }
}

fn visit_role_arg_polarity(arg: &CompactRoleArg, out: &mut VarPolarities) {
    visit_type_polarity(&arg.lower, Polarity::Positive, out);
    visit_type_polarity(&arg.upper, Polarity::Negative, out);
}

fn visit_type_polarity(ty: &CompactType, polarity: Polarity, out: &mut VarPolarities) {
    for var in &ty.vars {
        out.record(var.var, polarity);
    }
    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds_polarity(arg, polarity, out);
        }
    }
    for fun in &ty.funs {
        visit_type_polarity(&fun.arg, polarity.flipped(), out);
        visit_type_polarity(&fun.arg_eff, polarity.flipped(), out);
        visit_type_polarity(&fun.ret_eff, polarity, out);
        visit_type_polarity(&fun.ret, polarity, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_polarity(&field.value, polarity, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_polarity(&field.value, polarity, out);
        }
        visit_type_polarity(&spread.tail, polarity, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_polarity(payload, polarity, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_polarity(item, polarity, out);
        }
    }
    for row in &ty.rows {
        for item in &row.items {
            visit_type_polarity(item, polarity, out);
        }
        visit_type_polarity(&row.tail, polarity, out);
    }
}

fn visit_bounds_polarity(bounds: &CompactBounds, polarity: Polarity, out: &mut VarPolarities) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            out.record(*self_var, Polarity::Positive);
            out.record(*self_var, Polarity::Negative);
            visit_type_polarity(lower, polarity, out);
            visit_type_polarity(upper, polarity.flipped(), out);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_polarity(arg, polarity, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_polarity(arg, polarity.flipped(), out);
            visit_bounds_polarity(arg_eff, polarity.flipped(), out);
            visit_bounds_polarity(ret_eff, polarity, out);
            visit_bounds_polarity(ret, polarity, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_polarity(&field.value, polarity, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_polarity(payload, polarity, out);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_polarity(item, polarity, out);
            }
        }
    }
}

#[derive(Default)]
struct CoOccurrences {
    positive: FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    negative: FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    interval_equalities: Vec<(TypeVar, TypeVar)>,
}

impl CoOccurrences {
    /// 不変区間 `[lower, upper]` は instantiation ごとに `lower ≤ 実型 ≤ upper` を要求するので、
    /// 両側に現れる変数は実型と等しく確定する。他の出現位置での同伴に関係なく、
    /// この区間単独を根拠に互いに（中心があれば中心と）併合できる。
    /// 具体型との等値は変数の除去になり他出現を壊すため、ここでは変数同士に限る。
    fn record_interval_equalities(
        &mut self,
        lower: &CompactType,
        upper: &CompactType,
        center: Option<TypeVar>,
    ) {
        let upper_vars = upper
            .vars
            .iter()
            .map(|var| var.var)
            .collect::<FxHashSet<_>>();
        let mut both = lower
            .vars
            .iter()
            .map(|var| var.var)
            .filter(|var| upper_vars.contains(var))
            .collect::<Vec<_>>();
        both.sort_by_key(|var| var.0);
        both.dedup();
        match center {
            Some(center) => {
                for var in both {
                    if var != center {
                        self.interval_equalities.push((center, var));
                    }
                }
            }
            None => {
                for pair in both.windows(2) {
                    self.interval_equalities.push((pair[0], pair[1]));
                }
            }
        }
    }

    fn record_group(&mut self, group: FxHashSet<AlongItem>, polarity: Polarity) {
        let mut vars = group
            .iter()
            .filter_map(|item| match item {
                AlongItem::Var(var) => Some(*var),
                AlongItem::Exact(_) => None,
            })
            .collect::<Vec<_>>();
        vars.sort_by_key(|var| var.0);
        vars.dedup();
        if vars.is_empty() {
            return;
        }

        let table = match polarity {
            Polarity::Positive => &mut self.positive,
            Polarity::Negative => &mut self.negative,
        };
        for var in vars {
            match table.get_mut(&var) {
                Some(existing) => existing.retain(|item| group.contains(item)),
                None => {
                    table.insert(var, group.clone());
                }
            }
        }
    }

    fn substitution(
        &self,
        machine: &ConstraintMachine,
        boundary: TypeLevel,
        non_generic: &FxHashSet<TypeVar>,
    ) -> VarSubstitution {
        let mut union = VarUnion::default();
        let mut removals = FxHashSet::default();
        for (alpha, beta) in &self.interval_equalities {
            register_co_occurrence_pair(*alpha, *beta, machine, boundary, non_generic, &mut union);
        }
        register_co_occurrence_table(
            &self.positive,
            &self.negative,
            machine,
            boundary,
            non_generic,
            &mut union,
        );
        register_co_occurrence_table(
            &self.negative,
            &self.positive,
            machine,
            boundary,
            non_generic,
            &mut union,
        );
        register_sandwich_flattening(
            &self.positive,
            &self.negative,
            machine,
            boundary,
            non_generic,
            &mut union,
            &mut removals,
        );
        register_sandwich_flattening(
            &self.negative,
            &self.positive,
            machine,
            boundary,
            non_generic,
            &mut union,
            &mut removals,
        );
        union.into_substitution(removals)
    }
}

fn register_co_occurrence_table(
    table: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    opposite: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    non_generic: &FxHashSet<TypeVar>,
    union: &mut VarUnion,
) {
    let mut vars = table.keys().copied().collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    for alpha in vars {
        let Some(items) = table.get(&alpha) else {
            continue;
        };
        let mut items = items.iter().cloned().collect::<Vec<_>>();
        items.sort_by_key(along_item_sort_key);
        for beta in items {
            let AlongItem::Var(beta) = beta else {
                continue;
            };
            if alpha == beta {
                continue;
            }
            if !table
                .get(&beta)
                .is_some_and(|beta_items| beta_items.contains(&AlongItem::Var(alpha)))
            {
                continue;
            }
            if !opposite_co_occurrence_compatible(alpha, beta, opposite) {
                continue;
            }
            register_co_occurrence_pair(alpha, beta, machine, boundary, non_generic, union);
        }
    }
}

fn register_sandwich_flattening(
    table: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    opposite: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    non_generic: &FxHashSet<TypeVar>,
    union: &mut VarUnion,
    removals: &mut FxHashSet<TypeVar>,
) {
    let mut vars = table.keys().copied().collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    for alpha in vars {
        if !is_simplification_candidate(machine, boundary, alpha, non_generic) {
            continue;
        }
        if union.find(alpha) != alpha {
            continue;
        }
        let (Some(items), Some(opposite_items)) = (table.get(&alpha), opposite.get(&alpha)) else {
            continue;
        };
        let mut sandwiches = items
            .iter()
            .filter(|item| **item != AlongItem::Var(alpha) && opposite_items.contains(item))
            .cloned()
            .collect::<Vec<_>>();
        sandwiches.sort_by_key(along_item_sort_key);
        let Some(sandwich) = sandwiches.into_iter().next() else {
            continue;
        };
        match sandwich {
            AlongItem::Var(beta) => {
                register_co_occurrence_pair(alpha, beta, machine, boundary, non_generic, union);
            }
            AlongItem::Exact(_) => {
                removals.insert(alpha);
            }
        }
    }
}

fn opposite_co_occurrence_compatible(
    alpha: TypeVar,
    beta: TypeVar,
    opposite: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
) -> bool {
    let alpha_items = opposite.get(&alpha);
    let beta_items = opposite.get(&beta);
    if alpha_items == beta_items {
        return true;
    }
    let (Some(alpha_items), Some(beta_items)) = (alpha_items, beta_items) else {
        return false;
    };
    without_var(alpha_items, alpha) == *beta_items || without_var(beta_items, beta) == *alpha_items
}

fn without_var(items: &FxHashSet<AlongItem>, var: TypeVar) -> FxHashSet<AlongItem> {
    items
        .iter()
        .filter(|item| **item != AlongItem::Var(var))
        .cloned()
        .collect()
}

fn along_item_sort_key(item: &AlongItem) -> (u8, u32) {
    match item {
        AlongItem::Var(var) => (0, var.0),
        AlongItem::Exact(exact) => (1, exact.sort_key()),
    }
}

fn register_co_occurrence_pair(
    alpha: TypeVar,
    beta: TypeVar,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    non_generic: &FxHashSet<TypeVar>,
    union: &mut VarUnion,
) {
    let alpha_candidate = is_simplification_candidate(machine, boundary, alpha, non_generic);
    let beta_candidate = is_simplification_candidate(machine, boundary, beta, non_generic);
    if !alpha_candidate && !beta_candidate {
        return;
    }

    let rep = [alpha, beta]
        .into_iter()
        .min_by_key(|var| (machine.level_of(*var), var.0))
        .expect("pair should be non-empty");
    if alpha_candidate {
        union.union_to(rep, alpha);
    }
    if beta_candidate {
        union.union_to(rep, beta);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum AlongItem {
    Var(TypeVar),
    Exact(ExactKey),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum ExactKey {
    Builtin(BuiltinType),
    Con(Vec<String>, usize),
    Fun,
    Record(Vec<(String, bool)>),
    RecordSpread(Vec<(String, bool)>),
    PolyVariant(Vec<(String, usize)>),
    Tuple(usize),
    Row(Vec<ExactKey>),
}

impl ExactKey {
    fn sort_key(&self) -> u32 {
        match self {
            ExactKey::Builtin(_) => 0,
            ExactKey::Con(_, _) => 1,
            ExactKey::Fun => 2,
            ExactKey::Record(_) => 3,
            ExactKey::RecordSpread(_) => 4,
            ExactKey::PolyVariant(_) => 5,
            ExactKey::Tuple(_) => 6,
            ExactKey::Row(_) => 7,
        }
    }
}

fn collect_co_occurrences(root: &CompactRoot, roles: &[CompactRoleConstraint]) -> CoOccurrences {
    let mut out = CoOccurrences::default();
    let rec_vars = root.rec_vars.iter().map(|rec| rec.var).collect::<Vec<_>>();
    // Recursive center vars are counted through their Interval bounds via `extra_vars`.
    // Counting their root/role occurrences as ordinary singleton groups would prevent
    // the center from coalescing with the bounds that always sandwich it.
    visit_type_co_occurrence(&root.root, Polarity::Positive, &[], &rec_vars, &mut out);
    for rec in &root.rec_vars {
        visit_bounds_co_occurrence(&rec.bounds, Polarity::Positive, &[], &mut out);
    }
    for role in roles {
        visit_role_co_occurrence(role, &rec_vars, &mut out);
    }
    out
}

fn visit_role_co_occurrence(
    role: &CompactRoleConstraint,
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    for input in &role.inputs {
        visit_role_arg_co_occurrence(input, ignored_vars, out);
    }
    for associated in &role.associated {
        visit_role_arg_co_occurrence(&associated.value, ignored_vars, out);
    }
}

fn visit_role_arg_co_occurrence(
    arg: &CompactRoleArg,
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    out.record_interval_equalities(&arg.lower, &arg.upper, None);
    visit_type_co_occurrence(&arg.lower, Polarity::Positive, &[], ignored_vars, out);
    visit_type_co_occurrence(&arg.upper, Polarity::Negative, &[], ignored_vars, out);
}

fn visit_type_co_occurrence(
    ty: &CompactType,
    polarity: Polarity,
    extra_vars: &[TypeVar],
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    out.record_group(along_group(ty, extra_vars, ignored_vars), polarity);

    for con in &ty.cons {
        for arg in &con.args {
            visit_bounds_co_occurrence(arg, polarity, ignored_vars, out);
        }
    }
    for fun in &ty.funs {
        visit_type_co_occurrence(&fun.arg, polarity.flipped(), &[], ignored_vars, out);
        visit_type_co_occurrence(&fun.arg_eff, polarity.flipped(), &[], ignored_vars, out);
        visit_type_co_occurrence(&fun.ret_eff, polarity, &[], ignored_vars, out);
        visit_type_co_occurrence(&fun.ret, polarity, &[], ignored_vars, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_co_occurrence(&field.value, polarity, &[], ignored_vars, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_co_occurrence(&field.value, polarity, &[], ignored_vars, out);
        }
        visit_type_co_occurrence(&spread.tail, polarity, &[], ignored_vars, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_co_occurrence(payload, polarity, &[], ignored_vars, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_co_occurrence(item, polarity, &[], ignored_vars, out);
        }
    }
    for row in &ty.rows {
        let group = row_along_group(row, ignored_vars);
        visit_row_tail_vars(&row.tail, polarity, Some(&group), ignored_vars, out);
        for item in &row.items {
            visit_type_co_occurrence(item, polarity, &[], ignored_vars, out);
        }
        visit_type_co_occurrence(&row.tail, polarity, &[], ignored_vars, out);
    }
}

fn visit_row_tail_vars(
    ty: &CompactType,
    polarity: Polarity,
    group: Option<&FxHashSet<AlongItem>>,
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    if let Some(group) = group {
        out.record_group(group.clone(), polarity);
    }
    for row in &ty.rows {
        visit_row_tail_vars(&row.tail, polarity, group, ignored_vars, out);
    }
}

fn along_group(
    ty: &CompactType,
    extra_vars: &[TypeVar],
    ignored_vars: &[TypeVar],
) -> FxHashSet<AlongItem> {
    let mut group = FxHashSet::default();
    group.extend(
        ty.vars
            .iter()
            .filter(|var| !ignored_vars.contains(&var.var))
            .map(|var| AlongItem::Var(var.var)),
    );
    group.extend(extra_vars.iter().copied().map(AlongItem::Var));
    group.extend(exact_group(ty).into_iter().map(AlongItem::Exact));
    group
}

fn row_along_group(row: &CompactRow, ignored_vars: &[TypeVar]) -> FxHashSet<AlongItem> {
    let mut group = FxHashSet::default();
    collect_row_tail_vars(&row.tail, ignored_vars, &mut group);
    let mut item_keys = row.items.iter().flat_map(exact_group).collect::<Vec<_>>();
    item_keys.sort_by_key(ExactKey::sort_key);
    item_keys.dedup();
    group.extend(item_keys.into_iter().map(AlongItem::Exact));
    group
}

fn collect_row_tail_vars(
    ty: &CompactType,
    ignored_vars: &[TypeVar],
    out: &mut FxHashSet<AlongItem>,
) {
    out.extend(
        ty.vars
            .iter()
            .filter(|var| !ignored_vars.contains(&var.var))
            .map(|var| AlongItem::Var(var.var)),
    );
    for row in &ty.rows {
        collect_row_tail_vars(&row.tail, ignored_vars, out);
    }
}

fn exact_group(ty: &CompactType) -> Vec<ExactKey> {
    let mut group = Vec::new();
    group.extend(ty.builtins.iter().copied().map(ExactKey::Builtin));
    group.extend(
        ty.cons
            .iter()
            .map(|con| ExactKey::Con(con.path.clone(), con.args.len())),
    );
    if !ty.funs.is_empty() {
        group.push(ExactKey::Fun);
    }
    group.extend(ty.records.iter().map(|record| {
        ExactKey::Record(
            record
                .fields
                .iter()
                .map(|field| (field.name.clone(), field.optional))
                .collect(),
        )
    }));
    group.extend(ty.record_spreads.iter().map(|spread| {
        ExactKey::RecordSpread(
            spread
                .fields
                .iter()
                .map(|field| (field.name.clone(), field.optional))
                .collect(),
        )
    }));
    group.extend(ty.poly_variants.iter().map(|variant| {
        ExactKey::PolyVariant(
            variant
                .items
                .iter()
                .map(|(name, payloads)| (name.clone(), payloads.len()))
                .collect(),
        )
    }));
    group.extend(
        ty.tuples
            .iter()
            .map(|tuple| ExactKey::Tuple(tuple.items.len())),
    );
    group.extend(ty.rows.iter().map(|row| {
        let mut item_keys = row.items.iter().flat_map(exact_group).collect::<Vec<_>>();
        item_keys.sort_by_key(ExactKey::sort_key);
        item_keys.dedup();
        ExactKey::Row(item_keys)
    }));
    group
}

fn visit_bounds_co_occurrence(
    bounds: &CompactBounds,
    polarity: Polarity,
    ignored_vars: &[TypeVar],
    out: &mut CoOccurrences,
) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            out.record_interval_equalities(lower, upper, Some(*self_var));
            let mut body_ignored = ignored_vars.to_vec();
            if !body_ignored.contains(self_var) {
                body_ignored.push(*self_var);
            }
            if !lower.is_empty() {
                visit_type_co_occurrence(lower, polarity, &[*self_var], &body_ignored, out);
            }
            if !upper.is_empty() {
                visit_type_co_occurrence(
                    upper,
                    polarity.flipped(),
                    &[*self_var],
                    &body_ignored,
                    out,
                );
            }
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                visit_bounds_co_occurrence(arg, polarity, ignored_vars, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_co_occurrence(arg, polarity.flipped(), ignored_vars, out);
            visit_bounds_co_occurrence(arg_eff, polarity.flipped(), ignored_vars, out);
            visit_bounds_co_occurrence(ret_eff, polarity, ignored_vars, out);
            visit_bounds_co_occurrence(ret, polarity, ignored_vars, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_co_occurrence(&field.value, polarity, ignored_vars, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_co_occurrence(payload, polarity, ignored_vars, out);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                visit_bounds_co_occurrence(item, polarity, ignored_vars, out);
            }
        }
    }
}

#[derive(Default)]
struct VarUnion {
    parent: FxHashMap<TypeVar, TypeVar>,
}

impl VarUnion {
    fn union_to(&mut self, representative: TypeVar, other: TypeVar) {
        let representative = self.find(representative);
        let other = self.find(other);
        if representative == other {
            return;
        }
        self.parent.insert(other, representative);
    }

    fn find(&mut self, var: TypeVar) -> TypeVar {
        let parent = *self.parent.entry(var).or_insert(var);
        if parent == var {
            return var;
        }
        let root = self.find(parent);
        self.parent.insert(var, root);
        root
    }

    fn into_substitution(mut self, removals: FxHashSet<TypeVar>) -> VarSubstitution {
        let mut vars = self.parent.keys().copied().collect::<Vec<_>>();
        vars.extend(removals.iter().copied());
        vars.sort_by_key(|var| var.0);
        vars.dedup();
        let mut map = FxHashMap::default();
        for var in vars {
            let rep = self.find(var);
            if removals.contains(&rep) {
                map.insert(var, None);
            } else if rep != var {
                map.insert(var, Some(rep));
            }
        }
        VarSubstitution { map }
    }
}

struct VarSubstitution {
    map: FxHashMap<TypeVar, Option<TypeVar>>,
}

impl VarSubstitution {
    fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn rewrite(&self, var: TypeVar) -> Option<TypeVar> {
        self.map.get(&var).copied().unwrap_or(Some(var))
    }
}

fn rewrite_root_and_role_vars(
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
    mut rewrite: impl FnMut(TypeVar) -> Option<TypeVar>,
) -> Vec<CompactVarSubstitution> {
    let mut substitutions = FxHashMap::default();
    rewrite_type_vars(&mut root.root, &mut rewrite, &mut substitutions);
    for rec in &mut root.rec_vars {
        let source = rec.var;
        if let Some(rep) = rewrite(rec.var) {
            record_var_substitution(&mut substitutions, source, Some(rep));
            rec.var = rep;
        }
        rewrite_bounds_vars(&mut rec.bounds, &mut rewrite, &mut substitutions);
    }
    for role in roles {
        rewrite_role_vars(role, &mut rewrite, &mut substitutions);
    }
    sorted_var_substitutions(substitutions)
}

fn rewrite_role_vars(
    role: &mut CompactRoleConstraint,
    rewrite: &mut impl FnMut(TypeVar) -> Option<TypeVar>,
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
) {
    for input in &mut role.inputs {
        rewrite_role_arg_vars(input, rewrite, substitutions);
    }
    for associated in &mut role.associated {
        rewrite_role_arg_vars(&mut associated.value, rewrite, substitutions);
    }
}

fn rewrite_role_arg_vars(
    arg: &mut CompactRoleArg,
    rewrite: &mut impl FnMut(TypeVar) -> Option<TypeVar>,
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
) {
    rewrite_type_vars(&mut arg.lower, rewrite, substitutions);
    rewrite_type_vars(&mut arg.upper, rewrite, substitutions);
}

fn rewrite_type_vars(
    ty: &mut CompactType,
    rewrite: &mut impl FnMut(TypeVar) -> Option<TypeVar>,
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
) {
    let mut vars = Vec::new();
    for mut var in mem::take(&mut ty.vars) {
        let source = var.var;
        let Some(rep) = rewrite(var.var) else {
            record_var_substitution(substitutions, source, None);
            continue;
        };
        record_var_substitution(substitutions, source, Some(rep));
        var.var = rep;
        push_compact_var_with_unioned_weight(&mut vars, var);
    }
    ty.vars = vars;

    for con in &mut ty.cons {
        for arg in &mut con.args {
            rewrite_bounds_vars(arg, rewrite, substitutions);
        }
    }
    for fun in &mut ty.funs {
        rewrite_type_vars(&mut fun.arg, rewrite, substitutions);
        rewrite_type_vars(&mut fun.arg_eff, rewrite, substitutions);
        rewrite_type_vars(&mut fun.ret_eff, rewrite, substitutions);
        rewrite_type_vars(&mut fun.ret, rewrite, substitutions);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            rewrite_type_vars(&mut field.value, rewrite, substitutions);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            rewrite_type_vars(&mut field.value, rewrite, substitutions);
        }
        rewrite_type_vars(&mut spread.tail, rewrite, substitutions);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                rewrite_type_vars(payload, rewrite, substitutions);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            rewrite_type_vars(item, rewrite, substitutions);
        }
    }
    for row in &mut ty.rows {
        for item in &mut row.items {
            rewrite_type_vars(item, rewrite, substitutions);
        }
        rewrite_type_vars(&mut row.tail, rewrite, substitutions);
    }
}

fn push_compact_var_with_unioned_weight(vars: &mut Vec<CompactVar>, var: CompactVar) {
    if let Some(existing) = vars.iter_mut().find(|existing| existing.var == var.var) {
        existing.weight = existing.weight.union(&var.weight);
        existing.origin = existing.origin.merged(var.origin);
    } else {
        vars.push(var);
    }
}

fn rewrite_bounds_vars(
    bounds: &mut CompactBounds,
    rewrite: &mut impl FnMut(TypeVar) -> Option<TypeVar>,
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
) {
    match bounds {
        CompactBounds::Interval {
            self_var,
            lower,
            upper,
        } => {
            let source = *self_var;
            if let Some(rep) = rewrite(*self_var) {
                record_var_substitution(substitutions, source, Some(rep));
                *self_var = rep;
            }
            rewrite_type_vars(lower, rewrite, substitutions);
            rewrite_type_vars(upper, rewrite, substitutions);
        }
        CompactBounds::Con { args, .. } => {
            for arg in args {
                rewrite_bounds_vars(arg, rewrite, substitutions);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            rewrite_bounds_vars(arg, rewrite, substitutions);
            rewrite_bounds_vars(arg_eff, rewrite, substitutions);
            rewrite_bounds_vars(ret_eff, rewrite, substitutions);
            rewrite_bounds_vars(ret, rewrite, substitutions);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                rewrite_bounds_vars(&mut field.value, rewrite, substitutions);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    rewrite_bounds_vars(payload, rewrite, substitutions);
                }
            }
        }
        CompactBounds::Tuple { items } => {
            for item in items {
                rewrite_bounds_vars(item, rewrite, substitutions);
            }
        }
    }
}

fn record_var_substitution(
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
    source: TypeVar,
    target: Option<TypeVar>,
) {
    if target == Some(source) {
        return;
    }
    substitutions.insert(source, target);
}

fn sorted_var_substitutions(
    substitutions: FxHashMap<TypeVar, Option<TypeVar>>,
) -> Vec<CompactVarSubstitution> {
    let mut substitutions = substitutions
        .into_iter()
        .map(|(source, target)| CompactVarSubstitution { source, target })
        .collect::<Vec<_>>();
    substitutions.sort_by_key(|substitution| substitution.source.0);
    substitutions
}

pub(crate) fn normalize_var_substitutions(
    substitutions: Vec<CompactVarSubstitution>,
) -> Vec<CompactVarSubstitution> {
    let map = substitutions
        .into_iter()
        .map(|substitution| (substitution.source, substitution.target))
        .collect::<FxHashMap<_, _>>();
    let sources = map.keys().copied().collect::<Vec<_>>();
    let mut normalized = FxHashMap::default();
    for source in sources {
        let mut seen = FxHashSet::default();
        let target = resolve_substitution_target(source, &map, &mut seen);
        record_var_substitution(&mut normalized, source, target);
    }
    sorted_var_substitutions(normalized)
}

fn resolve_substitution_target(
    source: TypeVar,
    map: &FxHashMap<TypeVar, Option<TypeVar>>,
    seen: &mut FxHashSet<TypeVar>,
) -> Option<TypeVar> {
    if !seen.insert(source) {
        return Some(source);
    }
    match map.get(&source).copied() {
        None => Some(source),
        Some(None) => None,
        Some(Some(target)) => match resolve_substitution_target(target, map, seen) {
            Some(resolved) if resolved == target => Some(target),
            resolved => resolved,
        },
    }
}
