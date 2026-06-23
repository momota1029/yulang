use super::*;

pub(in crate::generalize) fn quantified_subtracts(
    machine: &ConstraintMachine,
    quantifiers: &[TypeVar],
    substitutions: &[CompactVarSubstitution],
) -> Vec<(TypeVar, SubtractId)> {
    let quantifier_set = quantifiers.iter().copied().collect::<FxHashSet<_>>();
    let mut subtracts = Vec::new();
    for var in quantifiers {
        subtracts.extend(
            machine
                .subtracts()
                .facts(*var)
                .iter()
                .map(|fact| (*var, fact.id)),
        );
    }
    for substitution in substitutions {
        let Some(target) = substitution.target else {
            continue;
        };
        if !quantifier_set.contains(&target) {
            continue;
        }
        subtracts.extend(
            machine
                .subtracts()
                .facts(substitution.source)
                .iter()
                .map(|fact| (target, fact.id)),
        );
    }
    subtracts.sort_by_key(|(var, subtract)| (var.0, subtract.0));
    subtracts.dedup();
    subtracts
}

pub(in crate::generalize) fn prune_dead_quantified_subtract_weights(
    machine: &ConstraintMachine,
    quantifiers: &[TypeVar],
    substitutions: &[CompactVarSubstitution],
    non_generic: &FxHashSet<TypeVar>,
    root: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
) {
    let mut candidates = quantified_subtracts(machine, quantifiers, substitutions);
    // 注釈・データ宣言が直接導入した id だけを、stack weight の pruning 入力に使う。
    // instantiate の clone で再登録された fact（推論残差）はこの境界で消える。
    candidates.retain(|(_, id)| machine.subtract_declared(*id));
    if candidates.is_empty() {
        return;
    }

    let candidate_ids = candidates
        .iter()
        .map(|(_, subtract)| *subtract)
        .collect::<FxHashSet<_>>();
    // A subtract id stays useful if at least one covariant occurrence is not
    // protected by the corresponding non-subtract weight.
    let live_subtracts = live_subtracts(root, role_predicates, &candidates);
    let live_ids = live_subtracts
        .iter()
        .map(|(_, subtract)| *subtract)
        .collect::<FxHashSet<_>>();
    let live_stack_ids = live_covariant_stack_ids_in_root_and_roles(root, role_predicates);
    let non_generic_subtract_ids = non_generic_subtract_ids(machine, non_generic);
    let dead_ids = candidate_ids
        .difference(&live_ids)
        .copied()
        .filter(|id| !live_stack_ids.contains(id))
        .filter(|id| !declared_all_stack_id(machine, *id))
        .filter(|id| !non_generic_subtract_ids.contains(id))
        .collect::<FxHashSet<_>>();
    if !dead_ids.is_empty() {
        prune_dead_subtract_weights_in_root_and_roles(root, role_predicates, &dead_ids);
    }
}

pub(in crate::generalize) fn non_generic_subtract_ids(
    machine: &ConstraintMachine,
    non_generic: &FxHashSet<TypeVar>,
) -> FxHashSet<SubtractId> {
    non_generic
        .iter()
        .flat_map(|var| machine.subtracts().facts(*var).iter().map(|fact| fact.id))
        .collect()
}

pub(in crate::generalize) fn prune_unreachable_recursive_bounds(
    root: &mut CompactRoot,
    role_predicates: &[CompactRoleConstraint],
) -> bool {
    if root.rec_vars.is_empty() {
        return false;
    }

    let mut reachable = FxHashSet::default();
    collect_type_free_vars_into_set(&root.root, &mut reachable);
    for role in role_predicates {
        collect_role_free_vars_into_set(role, &mut reachable);
    }

    let mut keep = FxHashSet::default();
    loop {
        let mut changed = false;
        for rec in &root.rec_vars {
            if keep.contains(&rec.var) || !reachable.contains(&rec.var) {
                continue;
            }
            keep.insert(rec.var);
            collect_bounds_free_vars_into_set(&rec.bounds, &mut reachable);
            changed = true;
        }
        if !changed {
            break;
        }
    }

    let before = root.rec_vars.len();
    root.rec_vars.retain(|rec| keep.contains(&rec.var));
    before != root.rec_vars.len()
}

pub(in crate::generalize) fn collect_role_free_vars_into_set(
    role: &CompactRoleConstraint,
    out: &mut FxHashSet<TypeVar>,
) {
    for input in &role.inputs {
        collect_bounds_free_vars_into_set(&input.bounds, out);
    }
    for associated in &role.associated {
        collect_bounds_free_vars_into_set(&associated.value.bounds, out);
    }
}

pub(in crate::generalize) fn collect_type_free_vars_into_set(
    ty: &CompactType,
    out: &mut FxHashSet<TypeVar>,
) {
    let mut vars = Vec::new();
    collect_type_free_vars(ty, &mut vars);
    out.extend(vars);
}

pub(in crate::generalize) fn collect_bounds_free_vars_into_set(
    bounds: &CompactBounds,
    out: &mut FxHashSet<TypeVar>,
) {
    let mut vars = Vec::new();
    collect_bounds_free_vars(bounds, &mut vars);
    out.extend(vars);
}

pub(in crate::generalize) fn prune_dead_quantifiers(root: &mut GeneralizedCompactRoot) {
    let mut free = Vec::new();
    collect_root_free_vars(&root.compact, &mut free);
    for role in &root.role_predicates {
        collect_role_free_vars(role, &mut free);
    }
    let free = free.into_iter().collect::<FxHashSet<_>>();
    root.quantifiers.retain(|var| free.contains(var));
}

pub(in crate::generalize) fn prune_unquantified_stack_weights(root: &mut GeneralizedCompactRoot) {
    let scheme_ids = root
        .stack_quantifiers
        .iter()
        .copied()
        .collect::<FxHashSet<_>>();
    let stray_ids = all_stack_ids_in_root_and_roles(&root.compact, &root.role_predicates)
        .difference(&scheme_ids)
        .copied()
        .collect::<FxHashSet<_>>();
    if stray_ids.is_empty() {
        return;
    }

    prune_dead_subtract_weights_in_root_and_roles(
        &mut root.compact,
        &mut root.role_predicates,
        &stray_ids,
    );
    prune_unreachable_recursive_bounds(&mut root.compact, &root.role_predicates);
    prune_dead_quantifiers(root);
    let quantifier_set = root.quantifiers.iter().copied().collect::<FxHashSet<_>>();
    root.stack_quantifiers =
        sorted_stack_quantifiers(&root.compact, &root.role_predicates, &quantifier_set);
}

pub(in crate::generalize) fn merge_arg_bounds(
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

pub(in crate::generalize) fn interval_from_types(
    lower: CompactType,
    upper: CompactType,
    fresh: &mut FreshCompactVars,
) -> CompactBounds {
    let _ = fresh;
    CompactBounds::Interval { lower, upper }
}

pub(in crate::generalize) fn common_var_in_types(
    lower: &CompactType,
    upper: &CompactType,
) -> Option<TypeVar> {
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

pub(in crate::generalize) fn single_con<'a>(
    ty: &'a CompactType,
    path: &[String],
    arity: usize,
) -> Option<&'a [CompactBounds]> {
    if ty.cons.len() == 1
        && ty.builtins.is_empty()
        && ty.funs.is_empty()
        && ty.records.is_empty()
        && ty.record_spreads.is_empty()
        && ty.poly_variants.is_empty()
        && ty.tuples.is_empty()
        && ty.rows.is_empty()
        && let Some(args) = ty.cons.get(path)
        && args.len() == arity
    {
        Some(args)
    } else {
        None
    }
}

pub(in crate::generalize) fn single_tuple(
    ty: &CompactType,
    arity: usize,
) -> Option<&[CompactType]> {
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

pub(in crate::generalize) fn single_fun(ty: &CompactType) -> Option<&CompactFun> {
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

pub(in crate::generalize) fn empty_interval(_var: TypeVar) -> CompactBounds {
    CompactBounds::Interval {
        lower: CompactType::default(),
        upper: CompactType::default(),
    }
}

pub(in crate::generalize) struct FreshCompactVars;

impl FreshCompactVars {
    pub(in crate::generalize) fn new(_root: &CompactRoot) -> Self {
        Self
    }
}

pub(in crate::generalize) fn live_subtracts(
    root: &CompactRoot,
    role_predicates: &[CompactRoleConstraint],
    candidates: &[(TypeVar, SubtractId)],
) -> FxHashSet<(TypeVar, SubtractId)> {
    let mut candidate_map = FxHashMap::<TypeVar, Vec<SubtractId>>::default();
    for (var, id) in candidates {
        candidate_map.entry(*var).or_default().push(*id);
    }
    let mut live = FxHashSet::default();
    collect_live_subtracts_in_type(&root.root, true, &candidate_map, &mut live);
    for rec in &root.rec_vars {
        collect_live_subtracts_in_bounds(&rec.bounds, true, &candidate_map, &mut live);
    }
    for role in role_predicates {
        collect_live_subtracts_in_role(role, &candidate_map, &mut live);
    }
    live
}

pub(in crate::generalize) fn collect_live_subtracts_in_role(
    role: &CompactRoleConstraint,
    candidate_map: &FxHashMap<TypeVar, Vec<SubtractId>>,
    live: &mut FxHashSet<(TypeVar, SubtractId)>,
) {
    for input in &role.inputs {
        collect_live_subtracts_in_role_arg(input, candidate_map, live);
    }
    for associated in &role.associated {
        collect_live_subtracts_in_role_arg(&associated.value, candidate_map, live);
    }
}

pub(in crate::generalize) fn collect_live_subtracts_in_role_arg(
    arg: &CompactRoleArg,
    candidate_map: &FxHashMap<TypeVar, Vec<SubtractId>>,
    live: &mut FxHashSet<(TypeVar, SubtractId)>,
) {
    collect_live_subtracts_in_bounds(&arg.bounds, true, candidate_map, live);
}

pub(in crate::generalize) fn collect_live_subtracts_in_type(
    ty: &CompactType,
    covariant: bool,
    candidate_map: &FxHashMap<TypeVar, Vec<SubtractId>>,
    live: &mut FxHashSet<(TypeVar, SubtractId)>,
) {
    if covariant {
        for var in &ty.vars {
            let Some(ids) = candidate_map.get(&var.var) else {
                continue;
            };
            for id in ids {
                // 保護されていない共変出現が一つでも残っているなら、その id の
                // subtract fact は use-site でまだ意味を持つ（旧 non-subtract と同じ規則）。
                if !var.weight.contains(*id) {
                    live.insert((var.var, *id));
                }
            }
        }
    }

    for args in ty.cons.values() {
        for arg in args {
            collect_live_subtracts_in_bounds(arg, covariant, candidate_map, live);
        }
    }
    for fun in &ty.funs {
        collect_live_subtracts_in_type(&fun.arg, !covariant, candidate_map, live);
        collect_live_subtracts_in_type(&fun.arg_eff, !covariant, candidate_map, live);
        collect_live_subtracts_in_type(&fun.ret_eff, covariant, candidate_map, live);
        collect_live_subtracts_in_type(&fun.ret, covariant, candidate_map, live);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_live_subtracts_in_type(&field.value, covariant, candidate_map, live);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_live_subtracts_in_type(&field.value, covariant, candidate_map, live);
        }
        collect_live_subtracts_in_type(&spread.tail, covariant, candidate_map, live);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_live_subtracts_in_type(payload, covariant, candidate_map, live);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_live_subtracts_in_type(item, covariant, candidate_map, live);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                collect_live_subtracts_in_bounds(arg, covariant, candidate_map, live);
            }
        }
        collect_live_subtracts_in_type(&row.tail, covariant, candidate_map, live);
    }
}

pub(in crate::generalize) fn collect_live_subtracts_in_bounds(
    bounds: &CompactBounds,
    covariant: bool,
    candidate_map: &FxHashMap<TypeVar, Vec<SubtractId>>,
    live: &mut FxHashSet<(TypeVar, SubtractId)>,
) {
    if !covariant {
        return;
    }
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            collect_live_subtracts_in_type(lower, true, candidate_map, live);
            collect_live_subtracts_in_type(upper, true, candidate_map, live);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_live_subtracts_in_bounds(arg, covariant, candidate_map, live);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_live_subtracts_in_bounds(arg, !covariant, candidate_map, live);
            collect_live_subtracts_in_bounds(arg_eff, !covariant, candidate_map, live);
            collect_live_subtracts_in_bounds(ret_eff, covariant, candidate_map, live);
            collect_live_subtracts_in_bounds(ret, covariant, candidate_map, live);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_live_subtracts_in_bounds(&field.value, covariant, candidate_map, live);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_live_subtracts_in_bounds(payload, covariant, candidate_map, live);
                }
            }
        }
    }
}

pub(in crate::generalize) fn prune_dead_subtract_weights_in_root_and_roles(
    root: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    let mut changed = prune_dead_subtract_weights_in_type(&mut root.root, dead_ids);
    for rec in &mut root.rec_vars {
        changed |= prune_dead_subtract_weights_in_bounds(&mut rec.bounds, dead_ids);
    }
    for role in role_predicates {
        changed |= prune_dead_subtract_weights_in_role(role, dead_ids);
    }
    changed
}

pub(in crate::generalize) fn prune_dead_subtract_weights_in_role(
    role: &mut CompactRoleConstraint,
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    let mut changed = false;
    for input in &mut role.inputs {
        changed |= prune_dead_subtract_weights_in_role_arg(input, dead_ids);
    }
    for associated in &mut role.associated {
        changed |= prune_dead_subtract_weights_in_role_arg(&mut associated.value, dead_ids);
    }
    changed
}

pub(in crate::generalize) fn prune_dead_subtract_weights_in_role_arg(
    arg: &mut CompactRoleArg,
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    prune_dead_subtract_weights_in_bounds(&mut arg.bounds, dead_ids)
}

pub(in crate::generalize) fn prune_dead_subtract_weights_in_type(
    ty: &mut CompactType,
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    let mut changed = false;
    for var in &mut ty.vars {
        let before = var.weight.clone();
        var.weight = var.weight.without_ids(|id| dead_ids.contains(&id));
        changed |= var.weight != before;
    }
    for args in ty.cons.values_mut() {
        for arg in args {
            changed |= prune_dead_subtract_weights_in_bounds(arg, dead_ids);
        }
    }
    for fun in &mut ty.funs {
        changed |= prune_dead_subtract_weights_in_type(&mut fun.arg, dead_ids);
        changed |= prune_dead_subtract_weights_in_type(&mut fun.arg_eff, dead_ids);
        changed |= prune_dead_subtract_weights_in_type(&mut fun.ret_eff, dead_ids);
        changed |= prune_dead_subtract_weights_in_type(&mut fun.ret, dead_ids);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            changed |= prune_dead_subtract_weights_in_type(&mut field.value, dead_ids);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            changed |= prune_dead_subtract_weights_in_type(&mut field.value, dead_ids);
        }
        changed |= prune_dead_subtract_weights_in_type(&mut spread.tail, dead_ids);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                changed |= prune_dead_subtract_weights_in_type(payload, dead_ids);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            changed |= prune_dead_subtract_weights_in_type(item, dead_ids);
        }
    }
    for row in &mut ty.rows {
        for args in row.items.values_mut() {
            for arg in args {
                changed |= prune_dead_subtract_weights_in_bounds(arg, dead_ids);
            }
        }
        changed |= prune_dead_subtract_weights_in_type(&mut row.tail, dead_ids);
    }
    changed
}

pub(in crate::generalize) fn prune_dead_subtract_weights_in_bounds(
    bounds: &mut CompactBounds,
    dead_ids: &FxHashSet<SubtractId>,
) -> bool {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            prune_dead_subtract_weights_in_type(lower, dead_ids)
                | prune_dead_subtract_weights_in_type(upper, dead_ids)
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            let mut changed = false;
            for arg in args {
                changed |= prune_dead_subtract_weights_in_bounds(arg, dead_ids);
            }
            changed
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            prune_dead_subtract_weights_in_bounds(arg, dead_ids)
                | prune_dead_subtract_weights_in_bounds(arg_eff, dead_ids)
                | prune_dead_subtract_weights_in_bounds(ret_eff, dead_ids)
                | prune_dead_subtract_weights_in_bounds(ret, dead_ids)
        }
        CompactBounds::Record { fields } => {
            let mut changed = false;
            for field in fields {
                changed |= prune_dead_subtract_weights_in_bounds(&mut field.value, dead_ids);
            }
            changed
        }
        CompactBounds::PolyVariant { items } => {
            let mut changed = false;
            for (_, payloads) in items {
                for payload in payloads {
                    changed |= prune_dead_subtract_weights_in_bounds(payload, dead_ids);
                }
            }
            changed
        }
    }
}

pub(in crate::generalize) fn cleanup_stack_weights_in_root_and_roles(
    machine: &ConstraintMachine,
    root: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
) -> bool {
    let live_ids = live_covariant_stack_ids_in_root_and_roles(root, role_predicates);
    let all_ids = all_stack_ids_in_root_and_roles(root, role_predicates);
    let dead_ids = all_ids
        .difference(&live_ids)
        .copied()
        .filter(|id| !declared_all_stack_id(machine, *id))
        .collect::<FxHashSet<_>>();
    if dead_ids.is_empty() {
        return false;
    }
    prune_dead_subtract_weights_in_root_and_roles(root, role_predicates, &dead_ids)
}

fn declared_all_stack_id(machine: &ConstraintMachine, id: SubtractId) -> bool {
    machine
        .subtracts()
        .fact_by_id(id)
        .is_some_and(|fact| matches!(fact.subtractability, Subtractability::All))
}

pub(in crate::generalize) fn cleanup_empty_stack_entries_with_plain_negative_occurrence(
    root: &mut CompactRoot,
    role_predicates: &mut [CompactRoleConstraint],
) -> bool {
    let mut occurrences = EmptyStackOccurrences::default();
    collect_empty_stack_occurrences_in_type(&root.root, true, &mut occurrences);
    for rec in &root.rec_vars {
        collect_empty_stack_occurrences_in_bounds(&rec.bounds, true, &mut occurrences);
    }
    for role in role_predicates.iter() {
        collect_empty_stack_occurrences_in_role(role, &mut occurrences);
    }

    let redundant = occurrences.redundant_positive_entries();
    if redundant.is_empty() {
        return false;
    }

    let mut changed = prune_redundant_empty_stack_entries_in_type(&mut root.root, true, &redundant);
    for rec in &mut root.rec_vars {
        changed |= prune_redundant_empty_stack_entries_in_bounds(&mut rec.bounds, true, &redundant);
    }
    for role in role_predicates {
        changed |= prune_redundant_empty_stack_entries_in_role(role, &redundant);
    }
    changed
}

#[derive(Default)]
pub(in crate::generalize) struct EmptyStackOccurrences {
    positive_internal_entries: FxHashMap<TypeVar, FxHashSet<SubtractId>>,
    plain_negative_vars: FxHashSet<TypeVar>,
}

impl EmptyStackOccurrences {
    fn record_type(&mut self, var: &CompactVar, covariant: bool) {
        if covariant {
            for entry in var.weight.entries() {
                if internal_stack_entry_with_plain_negative_counterpart(entry) {
                    self.positive_internal_entries
                        .entry(var.var)
                        .or_default()
                        .insert(entry.id);
                }
            }
        } else if var.weight.is_empty() {
            self.plain_negative_vars.insert(var.var);
        }
    }

    fn redundant_positive_entries(self) -> FxHashMap<TypeVar, FxHashSet<SubtractId>> {
        self.positive_internal_entries
            .into_iter()
            .filter(|(var, _)| self.plain_negative_vars.contains(var))
            .collect()
    }
}

pub(in crate::generalize) fn internal_stack_entry_with_plain_negative_counterpart(
    entry: &poly::types::StackWeightEntry,
) -> bool {
    empty_stack_entry_only(entry)
        || spent_residual_stack_entry(entry)
        || instantiated_stack_entry(entry)
}

pub(in crate::generalize) fn empty_stack_entry_only(entry: &poly::types::StackWeightEntry) -> bool {
    entry.pops == 0
        && entry.floor.is_empty()
        && !entry.stack.is_empty()
        && entry
            .stack
            .iter()
            .all(|item| matches!(item, Subtractability::Empty))
}

pub(in crate::generalize) fn spent_residual_stack_entry(
    entry: &poly::types::StackWeightEntry,
) -> bool {
    let [floor] = entry.floor.as_slice() else {
        return false;
    };
    if entry.stack.is_empty() {
        return false;
    }
    let common = entry
        .stack
        .iter()
        .cloned()
        .fold(floor.clone(), Subtractability::intersect);
    common == *floor
}

pub(in crate::generalize) fn instantiated_stack_entry(
    entry: &poly::types::StackWeightEntry,
) -> bool {
    entry.pops == u32::MAX && !entry.stack.is_empty()
}

pub(in crate::generalize) fn collect_empty_stack_occurrences_in_role(
    role: &CompactRoleConstraint,
    out: &mut EmptyStackOccurrences,
) {
    for input in &role.inputs {
        collect_empty_stack_occurrences_in_role_arg(input, out);
    }
    for associated in &role.associated {
        collect_empty_stack_occurrences_in_role_arg(&associated.value, out);
    }
}

pub(in crate::generalize) fn collect_empty_stack_occurrences_in_role_arg(
    arg: &CompactRoleArg,
    out: &mut EmptyStackOccurrences,
) {
    collect_empty_stack_occurrences_in_bounds(&arg.bounds, true, out);
}

pub(in crate::generalize) fn collect_empty_stack_occurrences_in_type(
    ty: &CompactType,
    covariant: bool,
    out: &mut EmptyStackOccurrences,
) {
    for var in &ty.vars {
        out.record_type(var, covariant);
    }
    for args in ty.cons.values() {
        for arg in args {
            collect_empty_stack_occurrences_in_bounds(arg, covariant, out);
        }
    }
    for fun in &ty.funs {
        collect_empty_stack_occurrences_in_type(&fun.arg, !covariant, out);
        collect_empty_stack_occurrences_in_type(&fun.arg_eff, !covariant, out);
        collect_empty_stack_occurrences_in_type(&fun.ret_eff, covariant, out);
        collect_empty_stack_occurrences_in_type(&fun.ret, covariant, out);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_empty_stack_occurrences_in_type(&field.value, covariant, out);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_empty_stack_occurrences_in_type(&field.value, covariant, out);
        }
        collect_empty_stack_occurrences_in_type(&spread.tail, covariant, out);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_empty_stack_occurrences_in_type(payload, covariant, out);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_empty_stack_occurrences_in_type(item, covariant, out);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                collect_empty_stack_occurrences_in_bounds(arg, covariant, out);
            }
        }
        collect_empty_stack_occurrences_in_type(&row.tail, covariant, out);
    }
}

pub(in crate::generalize) fn collect_empty_stack_occurrences_in_bounds(
    bounds: &CompactBounds,
    covariant: bool,
    out: &mut EmptyStackOccurrences,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
            collect_empty_stack_occurrences_in_type(lower, covariant, out);
            collect_empty_stack_occurrences_in_type(upper, !covariant, out);
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_empty_stack_occurrences_in_bounds(arg, covariant, out);
            }
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_empty_stack_occurrences_in_bounds(arg, !covariant, out);
            collect_empty_stack_occurrences_in_bounds(arg_eff, !covariant, out);
            collect_empty_stack_occurrences_in_bounds(ret_eff, covariant, out);
            collect_empty_stack_occurrences_in_bounds(ret, covariant, out);
        }
        CompactBounds::Record { fields } => {
            for field in fields {
                collect_empty_stack_occurrences_in_bounds(&field.value, covariant, out);
            }
        }
        CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_empty_stack_occurrences_in_bounds(payload, covariant, out);
                }
            }
        }
    }
}

pub(in crate::generalize) fn prune_redundant_empty_stack_entries_in_role(
    role: &mut CompactRoleConstraint,
    redundant: &FxHashMap<TypeVar, FxHashSet<SubtractId>>,
) -> bool {
    let mut changed = false;
    for input in &mut role.inputs {
        changed |= prune_redundant_empty_stack_entries_in_role_arg(input, redundant);
    }
    for associated in &mut role.associated {
        changed |=
            prune_redundant_empty_stack_entries_in_role_arg(&mut associated.value, redundant);
    }
    changed
}

pub(in crate::generalize) fn prune_redundant_empty_stack_entries_in_role_arg(
    arg: &mut CompactRoleArg,
    redundant: &FxHashMap<TypeVar, FxHashSet<SubtractId>>,
) -> bool {
    prune_redundant_empty_stack_entries_in_bounds(&mut arg.bounds, true, redundant)
}

pub(in crate::generalize) fn prune_redundant_empty_stack_entries_in_type(
    ty: &mut CompactType,
    covariant: bool,
    redundant: &FxHashMap<TypeVar, FxHashSet<SubtractId>>,
) -> bool {
    let mut changed = false;
    if covariant {
        for var in &mut ty.vars {
            let Some(ids) = redundant.get(&var.var) else {
                continue;
            };
            let before = var.weight.clone();
            var.weight = var.weight.without_ids(|id| ids.contains(&id));
            changed |= var.weight != before;
        }
    }
    for args in ty.cons.values_mut() {
        for arg in args {
            changed |= prune_redundant_empty_stack_entries_in_bounds(arg, covariant, redundant);
        }
    }
    for fun in &mut ty.funs {
        changed |= prune_redundant_empty_stack_entries_in_type(&mut fun.arg, !covariant, redundant);
        changed |=
            prune_redundant_empty_stack_entries_in_type(&mut fun.arg_eff, !covariant, redundant);
        changed |=
            prune_redundant_empty_stack_entries_in_type(&mut fun.ret_eff, covariant, redundant);
        changed |= prune_redundant_empty_stack_entries_in_type(&mut fun.ret, covariant, redundant);
    }
    for record in &mut ty.records {
        for field in &mut record.fields {
            changed |=
                prune_redundant_empty_stack_entries_in_type(&mut field.value, covariant, redundant);
        }
    }
    for spread in &mut ty.record_spreads {
        for field in &mut spread.fields {
            changed |=
                prune_redundant_empty_stack_entries_in_type(&mut field.value, covariant, redundant);
        }
        changed |=
            prune_redundant_empty_stack_entries_in_type(&mut spread.tail, covariant, redundant);
    }
    for variant in &mut ty.poly_variants {
        for (_, payloads) in &mut variant.items {
            for payload in payloads {
                changed |=
                    prune_redundant_empty_stack_entries_in_type(payload, covariant, redundant);
            }
        }
    }
    for tuple in &mut ty.tuples {
        for item in &mut tuple.items {
            changed |= prune_redundant_empty_stack_entries_in_type(item, covariant, redundant);
        }
    }
    for row in &mut ty.rows {
        for args in row.items.values_mut() {
            for arg in args {
                changed |= prune_redundant_empty_stack_entries_in_bounds(arg, covariant, redundant);
            }
        }
        changed |= prune_redundant_empty_stack_entries_in_type(&mut row.tail, covariant, redundant);
    }
    changed
}

pub(in crate::generalize) fn prune_redundant_empty_stack_entries_in_bounds(
    bounds: &mut CompactBounds,
    covariant: bool,
    redundant: &FxHashMap<TypeVar, FxHashSet<SubtractId>>,
) -> bool {
    match bounds {
        CompactBounds::Interval { lower, upper, .. } => {
            prune_redundant_empty_stack_entries_in_type(lower, covariant, redundant)
                | prune_redundant_empty_stack_entries_in_type(upper, !covariant, redundant)
        }
        CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
            let mut changed = false;
            for arg in args {
                changed |= prune_redundant_empty_stack_entries_in_bounds(arg, covariant, redundant);
            }
            changed
        }
        CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            prune_redundant_empty_stack_entries_in_bounds(arg, !covariant, redundant)
                | prune_redundant_empty_stack_entries_in_bounds(arg_eff, !covariant, redundant)
                | prune_redundant_empty_stack_entries_in_bounds(ret_eff, covariant, redundant)
                | prune_redundant_empty_stack_entries_in_bounds(ret, covariant, redundant)
        }
        CompactBounds::Record { fields } => {
            let mut changed = false;
            for field in fields {
                changed |= prune_redundant_empty_stack_entries_in_bounds(
                    &mut field.value,
                    covariant,
                    redundant,
                );
            }
            changed
        }
        CompactBounds::PolyVariant { items } => {
            let mut changed = false;
            for (_, payloads) in items {
                for payload in payloads {
                    changed |= prune_redundant_empty_stack_entries_in_bounds(
                        payload, covariant, redundant,
                    );
                }
            }
            changed
        }
    }
}
