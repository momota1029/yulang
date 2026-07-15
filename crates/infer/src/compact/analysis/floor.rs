use super::*;

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

/// 不変区間そのものが要求する `lower <: upper` を machine へ戻す。
///
/// Simple-sub の constraint propagation では、変数の lower/upper bounds は常に整合している
/// 必要がある。compact の `Interval(lower, upper)` も同じく「実型を挟む bounds」なので、
/// まず `lower <: upper` を戻す。そのうえで、片側の足場変数が反対極性で観測されない場合の
/// 代表制約も追加し、再 collect 後の共起分析へ渡す。
#[cfg(test)]
pub(crate) fn collect_interval_dominance_constraints(
    root: &CompactRoot,
    roles: &[CompactRoleConstraint],
) -> Vec<CompactSubtypeConstraint> {
    collect_interval_dominance_constraints_with_metrics(root, roles).0
}

pub(crate) fn collect_interval_dominance_constraints_with_metrics(
    root: &CompactRoot,
    roles: &[CompactRoleConstraint],
) -> (Vec<CompactSubtypeConstraint>, IntervalDominanceMetrics) {
    let scan = collect_interval_dominance_scan(root, roles);
    let mut metrics = IntervalDominanceMetrics {
        interval_inputs: scan.intervals.len(),
        polarity_vars: scan.counts.polarity_var_entries(),
        polarity_occurrences: scan.counts.polarity_occurrences(),
        generated_constraints: 0,
    };
    if scan.intervals.is_empty() {
        return (Vec::new(), metrics);
    }
    let mut out = Vec::new();
    for interval in &scan.intervals {
        if !subtype_constraint_is_trivial(interval.lower, interval.upper) {
            push_subtype_constraint_unchecked(
                &mut out,
                interval.lower.clone(),
                interval.upper.clone(),
            );
        }
        collect_interval_dominance_constraint(
            interval.lower,
            interval.upper,
            interval.polarity,
            &scan.counts,
            &mut out,
        );
    }
    metrics.generated_constraints = out.len();
    (out, metrics)
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct IntervalDominanceMetrics {
    pub(crate) interval_inputs: usize,
    pub(crate) polarity_vars: usize,
    pub(crate) polarity_occurrences: usize,
    pub(crate) generated_constraints: usize,
}

#[derive(Default)]
struct IntervalDominanceScan<'a> {
    counts: VarPolarityCounts,
    intervals: Vec<IntervalDominanceInput<'a>>,
}

struct IntervalDominanceInput<'a> {
    lower: &'a CompactType,
    upper: &'a CompactType,
    polarity: Polarity,
}

fn collect_interval_dominance_scan<'a>(
    root: &'a CompactRoot,
    roles: &'a [CompactRoleConstraint],
) -> IntervalDominanceScan<'a> {
    let mut out = IntervalDominanceScan::default();
    visit_type_polarity_counts_and_intervals(&root.root, Polarity::Positive, true, &mut out);
    for rec in &root.rec_vars {
        visit_bounds_polarity_counts_and_intervals(&rec.bounds, Polarity::Positive, true, &mut out);
    }
    for role in roles {
        for input in &role.inputs {
            visit_bounds_polarity_counts_and_intervals(
                &input.bounds,
                Polarity::Positive,
                true,
                &mut out,
            );
        }
        for associated in &role.associated {
            visit_bounds_polarity_counts_and_intervals(
                &associated.value.bounds,
                Polarity::Positive,
                false,
                &mut out,
            );
        }
    }
    out
}

pub(crate) fn compact_root_has_interval_bounds(
    root: &CompactRoot,
    roles: &[CompactRoleConstraint],
) -> bool {
    has_interval_bounds_in_type(&root.root)
        || root
            .rec_vars
            .iter()
            .any(|rec| has_interval_bounds_in_bounds(&rec.bounds))
        || roles.iter().any(|role| {
            role.inputs
                .iter()
                .any(|input| has_interval_bounds_in_bounds(&input.bounds))
                || role
                    .associated
                    .iter()
                    .any(|associated| has_interval_bounds_in_bounds(&associated.value.bounds))
        })
}

fn has_interval_bounds_in_bounds(bounds: &CompactBounds) -> bool {
    match bounds {
        CompactBounds::Interval { .. } => true,
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            args.iter().any(has_interval_bounds_in_bounds)
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            has_interval_bounds_in_bounds(arg)
                || has_interval_bounds_in_bounds(arg_eff)
                || has_interval_bounds_in_bounds(ret_eff)
                || has_interval_bounds_in_bounds(ret)
        }
        CompactBounds::Record { fields } => fields
            .iter()
            .any(|field| has_interval_bounds_in_bounds(&field.value)),
        CompactBounds::PolyVariant { items } => items
            .iter()
            .any(|(_, payloads)| payloads.iter().any(has_interval_bounds_in_bounds)),
    }
}

fn has_interval_bounds_in_type(ty: &CompactType) -> bool {
    ty.cons
        .values()
        .any(|args| args.iter().any(has_interval_bounds_in_bounds))
        || ty.funs.iter().any(|fun| {
            has_interval_bounds_in_type(&fun.arg)
                || has_interval_bounds_in_type(&fun.arg_eff)
                || has_interval_bounds_in_type(&fun.ret_eff)
                || has_interval_bounds_in_type(&fun.ret)
        })
        || ty.records.iter().any(|record| {
            record
                .fields
                .iter()
                .any(|field| has_interval_bounds_in_type(&field.value))
        })
        || ty.record_spreads.iter().any(|spread| {
            spread
                .fields
                .iter()
                .any(|field| has_interval_bounds_in_type(&field.value))
                || has_interval_bounds_in_type(&spread.tail)
        })
        || ty.poly_variants.iter().any(|variant| {
            variant
                .items
                .iter()
                .any(|(_, payloads)| payloads.iter().any(has_interval_bounds_in_type))
        })
        || ty
            .tuples
            .iter()
            .any(|tuple| tuple.items.iter().any(has_interval_bounds_in_type))
        || ty.rows.iter().any(|row| {
            row.items
                .values()
                .any(|args| args.iter().any(has_interval_bounds_in_bounds))
                || has_interval_bounds_in_type(&row.tail)
        })
}

fn visit_bounds_polarity_counts_and_intervals<'a>(
    bounds: &'a CompactBounds,
    polarity: Polarity,
    record_intervals: bool,
    out: &mut IntervalDominanceScan<'a>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            if record_intervals {
                out.intervals.push(IntervalDominanceInput {
                    lower,
                    upper,
                    polarity,
                });
            }
            visit_type_polarity_counts_and_intervals(lower, polarity, record_intervals, out);
            visit_type_polarity_counts_and_intervals(
                upper,
                polarity.flipped(),
                record_intervals,
                out,
            );
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                visit_bounds_polarity_counts_and_intervals(arg, polarity, record_intervals, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            visit_bounds_polarity_counts_and_intervals(
                arg,
                polarity.flipped(),
                record_intervals,
                out,
            );
            visit_bounds_polarity_counts_and_intervals(
                arg_eff,
                polarity.flipped(),
                record_intervals,
                out,
            );
            visit_bounds_polarity_counts_and_intervals(ret_eff, polarity, record_intervals, out);
            visit_bounds_polarity_counts_and_intervals(ret, polarity, record_intervals, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                visit_bounds_polarity_counts_and_intervals(
                    &field.value,
                    polarity,
                    record_intervals,
                    out,
                );
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    visit_bounds_polarity_counts_and_intervals(
                        payload,
                        polarity,
                        record_intervals,
                        out,
                    );
                }
            }
        }
    }
}

fn visit_type_polarity_counts_and_intervals<'a>(
    ty: &'a CompactType,
    polarity: Polarity,
    record_intervals: bool,
    out: &mut IntervalDominanceScan<'a>,
) {
    for var in &ty.vars {
        out.counts.record(var.var, polarity);
    }
    for args in ty.cons.values() {
        for arg in args {
            visit_bounds_polarity_counts_and_intervals(arg, polarity, record_intervals, out);
        }
    }
    for fun in &ty.funs {
        visit_type_polarity_counts_and_intervals(
            &fun.arg,
            polarity.flipped(),
            record_intervals,
            out,
        );
        visit_type_polarity_counts_and_intervals(
            &fun.arg_eff,
            polarity.flipped(),
            record_intervals,
            out,
        );
        visit_type_polarity_counts_and_intervals(&fun.ret_eff, polarity, record_intervals, out);
        visit_type_polarity_counts_and_intervals(&fun.ret, polarity, record_intervals, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            visit_type_polarity_counts_and_intervals(&field.value, polarity, record_intervals, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            visit_type_polarity_counts_and_intervals(&field.value, polarity, record_intervals, out);
        }
        visit_type_polarity_counts_and_intervals(&spread.tail, polarity, record_intervals, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                visit_type_polarity_counts_and_intervals(payload, polarity, record_intervals, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            visit_type_polarity_counts_and_intervals(item, polarity, record_intervals, out);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                visit_bounds_polarity_counts_and_intervals(arg, polarity, record_intervals, out);
            }
        }
        visit_type_polarity_counts_and_intervals(&row.tail, polarity, record_intervals, out);
    }
}

pub(super) fn collect_interval_dominance_constraint(
    lower: &CompactType,
    upper: &CompactType,
    polarity: Polarity,
    counts: &VarPolarityCounts,
    out: &mut Vec<CompactSubtypeConstraint>,
) {
    let lower_vars = top_level_type_vars(lower);
    let upper_vars = top_level_type_vars(upper);
    collect_side_dominance_constraint(
        lower,
        upper,
        polarity,
        &lower_vars,
        &upper_vars,
        counts,
        out,
    );
    collect_side_dominance_constraint(
        upper,
        lower,
        polarity.flipped(),
        &upper_vars,
        &lower_vars,
        counts,
        out,
    );
}

pub(super) fn collect_side_dominance_constraint(
    side: &CompactType,
    opposite: &CompactType,
    side_polarity: Polarity,
    side_vars: &FxHashSet<TypeVar>,
    opposite_vars: &FxHashSet<TypeVar>,
    counts: &VarPolarityCounts,
    out: &mut Vec<CompactSubtypeConstraint>,
) {
    if side_vars.len() < 2 {
        return;
    }

    let mut candidates = side_vars
        .iter()
        .copied()
        .filter(|anchor| {
            has_outside_occurrence(*anchor, side_vars, opposite_vars, side_polarity, counts)
                && side_vars
                    .iter()
                    .copied()
                    .filter(|var| var != anchor)
                    .all(|witness| {
                        !has_outside_polarity(
                            witness,
                            side_polarity.flipped(),
                            side_vars,
                            opposite_vars,
                            side_polarity,
                            counts,
                        )
                    })
        })
        .collect::<Vec<_>>();
    candidates.sort_by_key(|var| var.0);
    candidates.dedup();
    let [anchor] = candidates.as_slice() else {
        return;
    };

    let witnesses = side_vars
        .iter()
        .copied()
        .filter(|var| var != anchor)
        .collect::<FxHashSet<_>>();
    let Some(anchor_type) = top_level_var_type(side, *anchor) else {
        return;
    };
    let opposite_without_witnesses = type_without_top_level_vars(opposite, &witnesses);
    if opposite_without_witnesses.is_empty() {
        return;
    }

    if side_polarity.is_positive() {
        push_subtype_constraint(out, anchor_type, opposite_without_witnesses);
    } else {
        push_subtype_constraint(out, opposite_without_witnesses, anchor_type);
    }
}

pub(super) fn has_outside_occurrence(
    var: TypeVar,
    side_vars: &FxHashSet<TypeVar>,
    opposite_vars: &FxHashSet<TypeVar>,
    side_polarity: Polarity,
    counts: &VarPolarityCounts,
) -> bool {
    has_outside_polarity(
        var,
        Polarity::Positive,
        side_vars,
        opposite_vars,
        side_polarity,
        counts,
    ) || has_outside_polarity(
        var,
        Polarity::Negative,
        side_vars,
        opposite_vars,
        side_polarity,
        counts,
    )
}

pub(super) fn has_outside_polarity(
    var: TypeVar,
    polarity: Polarity,
    side_vars: &FxHashSet<TypeVar>,
    opposite_vars: &FxHashSet<TypeVar>,
    side_polarity: Polarity,
    counts: &VarPolarityCounts,
) -> bool {
    let mut local = 0usize;
    if polarity == side_polarity && side_vars.contains(&var) {
        local += 1;
    }
    if polarity == side_polarity.flipped() && opposite_vars.contains(&var) {
        local += 1;
    }
    counts.count(var, polarity) > local
}

pub(super) fn top_level_var_type(ty: &CompactType, var: TypeVar) -> Option<CompactType> {
    ty.vars
        .iter()
        .find(|candidate| candidate.var == var)
        .cloned()
        .map(CompactType::from_var)
}

pub(super) fn type_without_top_level_vars(
    ty: &CompactType,
    removals: &FxHashSet<TypeVar>,
) -> CompactType {
    let mut ty = ty.clone();
    ty.vars.retain(|var| !removals.contains(&var.var));
    ty
}

pub(super) fn push_subtype_constraint(
    out: &mut Vec<CompactSubtypeConstraint>,
    lower: CompactType,
    upper: CompactType,
) {
    if subtype_constraint_is_trivial(&lower, &upper) {
        return;
    }
    push_subtype_constraint_unchecked(out, lower, upper);
}

fn subtype_constraint_is_trivial(lower: &CompactType, upper: &CompactType) -> bool {
    lower.is_empty() || upper.is_empty() || lower == upper
}

fn push_subtype_constraint_unchecked(
    out: &mut Vec<CompactSubtypeConstraint>,
    lower: CompactType,
    upper: CompactType,
) {
    out.push(CompactSubtypeConstraint {
        key: CompactSubtypeConstraintKey {
            lower: lower.clone(),
            upper: upper.clone(),
        },
        lower,
        upper,
    });
}

/// scheme に量化できない床変数のうち、surface に残す根拠を持たないものを落とす。
///
/// 片側極性だけなら通常の極性消去、両極性に出ても同じ concrete に挟まっているなら
/// sandwich flattening と同じ根拠で消せる。裸の床変数まで消すと未確定の root を
/// `never` 相当に潰すので、polar-only は deeper birth か concrete 同伴がある場合に限る。
pub(crate) fn eliminate_floor_redundant_variables(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
) -> Vec<CompactVarSubstitution> {
    let polarity = collect_var_polarities(root, roles);
    let co_occurrences = collect_co_occurrences(root, roles);
    let removals = floor_redundant_vars(machine, boundary, &polarity, &co_occurrences);
    if removals.is_empty() {
        return Vec::new();
    }
    rewrite_root_and_role_vars(root, roles, |var| {
        if removals.contains(&var) {
            None
        } else {
            Some(var)
        }
    })
}

/// 確定直前の scheme だけに掛ける床下 variable sandwich。
///
/// 通常 simplify の level 保護が触れない床下変数でも、Simple-sub 4.3.1 の
/// indistinguishable variables / variable sandwich として、同じ変数に正負両方で
/// 挟まっているなら併合できる。role 引数に残った 2 変数区間も、main-polarity から
/// 片方が反対位置に出ないと分かるなら同じ根拠で畳む。
pub(crate) fn coalesce_floor_variable_sandwiches(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    root: &mut CompactRoot,
    roles: &mut [CompactRoleConstraint],
) -> Vec<CompactVarSubstitution> {
    let mut substitutions = Vec::new();
    let co_occurrences = collect_co_occurrences(root, roles);
    let mut union = VarUnion::default();
    register_floor_variable_sandwiches(
        &co_occurrences.positive,
        &co_occurrences.negative,
        machine,
        boundary,
        &mut union,
    );
    register_floor_variable_sandwiches(
        &co_occurrences.negative,
        &co_occurrences.positive,
        machine,
        boundary,
        &mut union,
    );
    let subst = union.into_substitution(FxHashSet::default());
    if !subst.is_empty() {
        substitutions.extend(rewrite_root_and_role_vars(root, roles, |var| {
            subst.rewrite(var)
        }));
    }

    let main_polarity = collect_main_var_polarities(root);
    let mut union = VarUnion::default();
    register_role_main_polarity_sandwiches(roles, &main_polarity, machine, boundary, &mut union);
    let subst = union.into_substitution(FxHashSet::default());
    if !subst.is_empty() {
        substitutions.extend(rewrite_root_and_role_vars(root, roles, |var| {
            subst.rewrite(var)
        }));
    }
    substitutions
}

pub(super) fn register_floor_variable_sandwiches(
    table: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    opposite: &FxHashMap<TypeVar, FxHashSet<AlongItem>>,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    union: &mut VarUnion,
) {
    let mut vars = table.keys().copied().collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    for alpha in vars {
        if machine.level_of(alpha) > boundary {
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
            .filter_map(|item| match item {
                AlongItem::Var(beta)
                    if *beta != alpha && opposite_items.contains(&AlongItem::Var(*beta)) =>
                {
                    Some(*beta)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        sandwiches.sort_by_key(|var| (machine.level_of(*var), var.0));
        let Some(beta) = sandwiches.into_iter().next() else {
            continue;
        };
        let beta_floor = machine.level_of(beta) <= boundary;
        let rep = if beta_floor {
            [alpha, beta]
                .into_iter()
                .min_by_key(|var| var.0)
                .expect("pair should be non-empty")
        } else {
            beta
        };
        union.union_to(rep, alpha);
        if beta_floor {
            union.union_to(rep, beta);
        }
    }
}

pub(super) fn register_role_main_polarity_sandwiches(
    roles: &[CompactRoleConstraint],
    main_polarity: &VarPolarities,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    union: &mut VarUnion,
) {
    for role in roles {
        for input in &role.inputs {
            register_role_arg_main_polarity_sandwich(
                &input.bounds,
                main_polarity,
                machine,
                boundary,
                union,
            );
        }
    }
}

pub(super) fn register_role_arg_main_polarity_sandwich(
    bounds: &CompactBounds,
    main_polarity: &VarPolarities,
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    union: &mut VarUnion,
) {
    let CompactBounds::Interval { lower, upper } = bounds else {
        return;
    };
    let lower_vars = top_level_type_vars(lower);
    let upper_vars = top_level_type_vars(upper);
    let mut vars = lower_vars.union(&upper_vars).copied().collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    vars.dedup();
    if vars.len() != 2 {
        return;
    }
    for alpha in vars.iter().copied() {
        if machine.level_of(alpha) > boundary {
            continue;
        }
        let appears_lower = lower_vars.contains(&alpha);
        let appears_upper = upper_vars.contains(&alpha);
        let opposite_main_absent = (appears_lower && !main_polarity.negative.contains(&alpha))
            || (appears_upper && !main_polarity.positive.contains(&alpha));
        if !opposite_main_absent {
            continue;
        }
        let beta = vars
            .iter()
            .copied()
            .find(|var| *var != alpha)
            .expect("two vars");
        if !main_polarity.positive.contains(&beta) && !main_polarity.negative.contains(&beta) {
            continue;
        }
        union.union_to(beta, alpha);
        break;
    }
}

pub(super) fn top_level_type_vars(ty: &CompactType) -> FxHashSet<TypeVar> {
    ty.vars.iter().map(|var| var.var).collect()
}

pub(super) fn floor_redundant_vars(
    machine: &ConstraintMachine,
    boundary: TypeLevel,
    polarity: &VarPolarities,
    co_occurrences: &CoOccurrences,
) -> FxHashSet<TypeVar> {
    let mut vars = polarity
        .positive
        .iter()
        .chain(&polarity.negative)
        .copied()
        .collect::<Vec<_>>();
    vars.sort_by_key(|var| var.0);
    vars.dedup();

    let mut removals = FxHashSet::default();
    for var in vars {
        if machine.level_of(var) > boundary {
            continue;
        }
        if !polarity.is_bipolar(var) {
            if machine.birth_level_of(var) > boundary || has_exact_companion(var, co_occurrences) {
                removals.insert(var);
            }
            continue;
        }
        if has_exact_sandwich(var, co_occurrences) {
            removals.insert(var);
        }
    }
    removals
}

pub(super) fn has_exact_companion(var: TypeVar, co_occurrences: &CoOccurrences) -> bool {
    co_occurrences
        .positive
        .get(&var)
        .is_some_and(has_exact_item)
        || co_occurrences
            .negative
            .get(&var)
            .is_some_and(has_exact_item)
}

pub(super) fn has_exact_sandwich(var: TypeVar, co_occurrences: &CoOccurrences) -> bool {
    let (Some(positive), Some(negative)) = (
        co_occurrences.positive.get(&var),
        co_occurrences.negative.get(&var),
    ) else {
        return false;
    };
    positive
        .iter()
        .any(|item| matches!(item, AlongItem::Exact(_)) && negative.contains(item))
}

pub(super) fn has_exact_item(items: &FxHashSet<AlongItem>) -> bool {
    items.iter().any(|item| matches!(item, AlongItem::Exact(_)))
}
