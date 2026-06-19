use super::*;

#[derive(Default)]
pub(in crate::compact::analysis) struct VarUnion {
    parent: FxHashMap<TypeVar, TypeVar>,
}

impl VarUnion {
    pub(in crate::compact::analysis) fn union_to(
        &mut self,
        representative: TypeVar,
        other: TypeVar,
    ) {
        let representative = self.find(representative);
        let other = self.find(other);
        if representative == other {
            return;
        }
        self.parent.insert(other, representative);
    }

    pub(in crate::compact::analysis) fn find(&mut self, var: TypeVar) -> TypeVar {
        let parent = *self.parent.entry(var).or_insert(var);
        if parent == var {
            return var;
        }
        let root = self.find(parent);
        self.parent.insert(var, root);
        root
    }

    pub(in crate::compact::analysis) fn into_substitution(
        mut self,
        removals: FxHashSet<TypeVar>,
    ) -> VarSubstitution {
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

pub(in crate::compact::analysis) struct VarSubstitution {
    map: FxHashMap<TypeVar, Option<TypeVar>>,
}

impl VarSubstitution {
    pub(in crate::compact::analysis) fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub(in crate::compact::analysis) fn rewrite(&self, var: TypeVar) -> Option<TypeVar> {
        self.map.get(&var).copied().unwrap_or(Some(var))
    }
}

pub(in crate::compact::analysis) fn rewrite_root_and_role_vars(
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

pub(in crate::compact::analysis) fn rewrite_role_vars(
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

pub(in crate::compact::analysis) fn rewrite_role_arg_vars(
    arg: &mut CompactRoleArg,
    rewrite: &mut impl FnMut(TypeVar) -> Option<TypeVar>,
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
) {
    rewrite_bounds_vars(&mut arg.bounds, rewrite, substitutions);
}

pub(in crate::compact::analysis) fn rewrite_type_vars(
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

    for args in ty.cons.values_mut() {
        for arg in args {
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
        for args in row.items.values_mut() {
            for arg in args {
                rewrite_bounds_vars(arg, rewrite, substitutions);
            }
        }
        rewrite_type_vars(&mut row.tail, rewrite, substitutions);
    }
}

pub(in crate::compact::analysis) fn push_compact_var_with_unioned_weight(
    vars: &mut Vec<CompactVar>,
    var: CompactVar,
) {
    if let Some(existing) = vars.iter_mut().find(|existing| existing.var == var.var) {
        existing.weight = existing.weight.parallel_union(&var.weight);
        existing.origin = existing.origin.merged(var.origin);
    } else {
        vars.push(var);
    }
}

pub(in crate::compact::analysis) fn rewrite_bounds_vars(
    bounds: &mut CompactBounds,
    rewrite: &mut impl FnMut(TypeVar) -> Option<TypeVar>,
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
) {
    match bounds {
        CompactBounds::Interval { lower, upper } => {
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

pub(in crate::compact::analysis) fn record_var_substitution(
    substitutions: &mut FxHashMap<TypeVar, Option<TypeVar>>,
    source: TypeVar,
    target: Option<TypeVar>,
) {
    if target == Some(source) {
        return;
    }
    substitutions.insert(source, target);
}

pub(in crate::compact::analysis) fn sorted_var_substitutions(
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

pub(in crate::compact::analysis) fn resolve_substitution_target(
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
