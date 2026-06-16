use super::*;

pub(super) fn role_arg_top_level_vars(arg: &CompactRoleArg) -> FxHashSet<TypeVar> {
    let mut vars = FxHashSet::default();
    if let CompactBounds::Interval { lower, upper } = &arg.bounds {
        vars.extend(lower.vars.iter().map(|var| var.var));
        vars.extend(upper.vars.iter().map(|var| var.var));
    }
    vars
}

#[derive(Default)]
pub(super) struct MainPolarity {
    pub(super) positive: FxHashSet<TypeVar>,
    pub(super) negative: FxHashSet<TypeVar>,
    negative_cooccur: FxHashMap<TypeVar, Vec<CompactType>>,
}

impl MainPolarity {
    pub(super) fn collect(root: &CompactRoot) -> Self {
        let mut polarity = Self::default();
        polarity.collect_type(&root.root, true);
        for rec in &root.rec_vars {
            polarity.collect_bounds(&rec.bounds, true);
        }
        polarity
    }

    fn insert(&mut self, var: TypeVar, positive: bool) {
        if positive {
            self.positive.insert(var);
        } else {
            self.negative.insert(var);
        }
    }

    pub(super) fn negative_occurrences_pinned_to(
        &self,
        var: TypeVar,
        target: &CompactType,
    ) -> bool {
        self.negative_cooccur.get(&var).is_some_and(|occurrences| {
            occurrences
                .iter()
                .all(|occurrence| single_concrete_type(occurrence).as_ref() == Some(target))
        })
    }

    fn collect_type(&mut self, ty: &CompactType, positive: bool) {
        for var in &ty.vars {
            self.insert(var.var, positive);
            if !positive {
                self.negative_cooccur
                    .entry(var.var)
                    .or_default()
                    .push(ty.clone());
            }
        }
        for args in ty.cons.values() {
            for arg in args {
                self.collect_bounds(arg, positive);
            }
        }
        for fun in &ty.funs {
            self.collect_type(&fun.arg, !positive);
            self.collect_type(&fun.arg_eff, !positive);
            self.collect_type(&fun.ret_eff, positive);
            self.collect_type(&fun.ret, positive);
        }
        for record in &ty.records {
            for field in &record.fields {
                self.collect_type(&field.value, positive);
            }
        }
        for spread in &ty.record_spreads {
            for field in &spread.fields {
                self.collect_type(&field.value, positive);
            }
            self.collect_type(&spread.tail, positive);
        }
        for variant in &ty.poly_variants {
            for (_, payloads) in &variant.items {
                for payload in payloads {
                    self.collect_type(payload, positive);
                }
            }
        }
        for tuple in &ty.tuples {
            for item in &tuple.items {
                self.collect_type(item, positive);
            }
        }
        for row in &ty.rows {
            for args in row.items.values() {
                for arg in args {
                    self.collect_bounds(arg, positive);
                }
            }
            self.collect_type(&row.tail, positive);
        }
    }

    fn collect_bounds(&mut self, bounds: &CompactBounds, positive: bool) {
        match bounds {
            CompactBounds::Interval { lower, upper } => {
                self.collect_type(lower, positive);
                self.collect_type(upper, !positive);
            }
            CompactBounds::Con { args, .. } | CompactBounds::Tuple { items: args } => {
                for arg in args {
                    self.collect_bounds(arg, positive);
                }
            }
            CompactBounds::Fun {
                arg,
                arg_eff,
                ret_eff,
                ret,
            } => {
                self.collect_bounds(arg, !positive);
                self.collect_bounds(arg_eff, !positive);
                self.collect_bounds(ret_eff, positive);
                self.collect_bounds(ret, positive);
            }
            CompactBounds::Record { fields } => {
                for field in fields {
                    self.collect_bounds(&field.value, positive);
                }
            }
            CompactBounds::PolyVariant { items } => {
                for (_, payloads) in items {
                    for payload in payloads {
                        self.collect_bounds(payload, positive);
                    }
                }
            }
        }
    }
}

pub(super) fn role_arg_vars(arg: &CompactRoleArg) -> FxHashSet<TypeVar> {
    let mut vars = FxHashSet::default();
    collect_bounds_vars(&arg.bounds, &mut vars);
    vars
}

pub(super) fn collect_type_vars(ty: &CompactType, vars: &mut FxHashSet<TypeVar>) {
    vars.extend(ty.vars.iter().map(|var| var.var));
    for args in ty.cons.values() {
        for arg in args {
            collect_bounds_vars(arg, vars);
        }
    }
    for fun in &ty.funs {
        collect_type_vars(&fun.arg, vars);
        collect_type_vars(&fun.arg_eff, vars);
        collect_type_vars(&fun.ret_eff, vars);
        collect_type_vars(&fun.ret, vars);
    }
    for record in &ty.records {
        for field in &record.fields {
            collect_type_vars(&field.value, vars);
        }
    }
    for spread in &ty.record_spreads {
        for field in &spread.fields {
            collect_type_vars(&field.value, vars);
        }
        collect_type_vars(&spread.tail, vars);
    }
    for variant in &ty.poly_variants {
        for (_, payloads) in &variant.items {
            for payload in payloads {
                collect_type_vars(payload, vars);
            }
        }
    }
    for tuple in &ty.tuples {
        for item in &tuple.items {
            collect_type_vars(item, vars);
        }
    }
    for row in &ty.rows {
        for args in row.items.values() {
            for arg in args {
                collect_bounds_vars(arg, vars);
            }
        }
        collect_type_vars(&row.tail, vars);
    }
}

pub(super) fn collect_bounds_vars(
    bounds: &crate::compact::CompactBounds,
    vars: &mut FxHashSet<TypeVar>,
) {
    match bounds {
        crate::compact::CompactBounds::Interval { lower, upper } => {
            collect_type_vars(lower, vars);
            collect_type_vars(upper, vars);
        }
        crate::compact::CompactBounds::Con { args, .. }
        | crate::compact::CompactBounds::Tuple { items: args } => {
            for arg in args {
                collect_bounds_vars(arg, vars);
            }
        }
        crate::compact::CompactBounds::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_bounds_vars(arg, vars);
            collect_bounds_vars(arg_eff, vars);
            collect_bounds_vars(ret_eff, vars);
            collect_bounds_vars(ret, vars);
        }
        crate::compact::CompactBounds::Record { fields } => {
            for field in fields {
                collect_bounds_vars(&field.value, vars);
            }
        }
        crate::compact::CompactBounds::PolyVariant { items } => {
            for (_, payloads) in items {
                for payload in payloads {
                    collect_bounds_vars(payload, vars);
                }
            }
        }
    }
}
