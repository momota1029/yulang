use super::*;

#[cfg(test)]
pub(super) fn project_runtime_type(ty: &core_ir::Type) -> core_ir::Type {
    RuntimeTypeProjector::new(&BTreeSet::new()).project(ty)
}

pub(crate) fn project_runtime_effect(ty: &core_ir::Type) -> core_ir::Type {
    RuntimeTypeProjector::new(&BTreeSet::new()).project_effect(ty)
}

pub(crate) fn project_runtime_bounds(bounds: &core_ir::TypeBounds) -> Option<core_ir::Type> {
    RuntimeTypeProjector::new(&BTreeSet::new()).project_bounds(bounds)
}

pub(crate) fn project_runtime_type_with_vars(
    ty: &core_ir::Type,
    allowed_vars: &BTreeSet<core_ir::TypeVar>,
) -> core_ir::Type {
    RuntimeTypeProjector::new(allowed_vars).project(ty)
}

pub(crate) fn project_runtime_hir_type_with_vars(
    ty: &core_ir::Type,
    allowed_vars: &BTreeSet<core_ir::TypeVar>,
) -> RuntimeType {
    RuntimeTypeProjector::new(allowed_vars).project_hir(ty)
}

pub(super) struct RuntimeTypeProjector<'a> {
    pub(super) allowed_vars: &'a BTreeSet<core_ir::TypeVar>,
    pub(super) stack: HashSet<core_ir::TypeVar>,
}

impl<'a> RuntimeTypeProjector<'a> {
    pub(super) fn new(allowed_vars: &'a BTreeSet<core_ir::TypeVar>) -> Self {
        Self {
            allowed_vars,
            stack: HashSet::new(),
        }
    }

    pub(super) fn project(&mut self, ty: &core_ir::Type) -> core_ir::Type {
        match ty {
            core_ir::Type::Unknown => runtime_projection_fallback_type(),
            core_ir::Type::Never => core_ir::Type::Never,
            core_ir::Type::Any => core_ir::Type::Any,
            core_ir::Type::Var(var) if self.allowed_vars.contains(var) => {
                core_ir::Type::Var(var.clone())
            }
            core_ir::Type::Var(_) => runtime_projection_fallback_type(),
            core_ir::Type::Named { path, args } if is_never_path(path) && args.is_empty() => {
                core_ir::Type::Never
            }
            core_ir::Type::Named { path, args } => core_ir::Type::Named {
                path: path.clone(),
                args: if is_synthetic_var_effect_path(path) {
                    Vec::new()
                } else {
                    args.iter().map(|arg| self.project_arg(arg)).collect()
                },
            },
            core_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => core_ir::Type::Fun {
                param: Box::new(self.project(param)),
                param_effect: Box::new(self.project_effect(param_effect)),
                ret_effect: Box::new(self.project_effect(ret_effect)),
                ret: Box::new(self.project(ret)),
            },
            core_ir::Type::Tuple(items) => {
                core_ir::Type::Tuple(items.iter().map(|item| self.project(item)).collect())
            }
            core_ir::Type::Record(record) => core_ir::Type::Record(core_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| core_ir::RecordField {
                        name: field.name.clone(),
                        value: self.project(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
                spread: record.spread.as_ref().map(|spread| match spread {
                    core_ir::RecordSpread::Head(ty) => {
                        core_ir::RecordSpread::Head(Box::new(self.project(ty)))
                    }
                    core_ir::RecordSpread::Tail(ty) => {
                        core_ir::RecordSpread::Tail(Box::new(self.project(ty)))
                    }
                }),
            }),
            core_ir::Type::Variant(variant) => core_ir::Type::Variant(core_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .map(|case| core_ir::VariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .map(|payload| self.project(payload))
                            .collect(),
                    })
                    .collect(),
                tail: variant
                    .tail
                    .as_ref()
                    .map(|tail| Box::new(self.project(tail))),
            }),
            core_ir::Type::Union(items) => self
                .project_choice(items)
                .unwrap_or_else(runtime_projection_fallback_type),
            core_ir::Type::Inter(items) => self
                .project_choice(items)
                .unwrap_or_else(runtime_projection_fallback_type),
            core_ir::Type::Row { .. } => runtime_projection_fallback_type(),
            core_ir::Type::Recursive { var, body } => {
                if !self.stack.insert(var.clone()) {
                    return runtime_projection_fallback_type();
                }
                let body = self.project(body);
                self.stack.remove(var);
                core_ir::Type::Recursive {
                    var: var.clone(),
                    body: Box::new(body),
                }
            }
        }
    }

    pub(super) fn project_hir(&mut self, ty: &core_ir::Type) -> RuntimeType {
        match ty {
            core_ir::Type::Unknown => RuntimeType::unknown(),
            core_ir::Type::Var(var) if self.allowed_vars.contains(var) => {
                RuntimeType::core(core_ir::Type::Var(var.clone()))
            }
            core_ir::Type::Var(_) => RuntimeType::unknown(),
            core_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                let param = self.project_hir_effected_value(param, param_effect);
                let ret = self.project_hir_effected_value(ret, ret_effect);
                RuntimeType::fun(param, ret)
            }
            core_ir::Type::Union(items) | core_ir::Type::Inter(items) => self
                .project_hir_choice(items)
                .unwrap_or_else(RuntimeType::unknown),
            core_ir::Type::Row { .. } => RuntimeType::unknown(),
            other => RuntimeType::core(self.project(other)),
        }
    }

    pub(super) fn project_hir_effected_value(
        &mut self,
        value: &core_ir::Type,
        effect: &core_ir::Type,
    ) -> RuntimeType {
        let value = self.project_hir(value);
        let effect = self.project_effect(effect);
        if should_thunk_effect(&effect) {
            RuntimeType::thunk(effect, value)
        } else {
            value
        }
    }

    pub(super) fn project_arg(&mut self, arg: &core_ir::TypeArg) -> core_ir::TypeArg {
        match arg {
            core_ir::TypeArg::Type(ty) => core_ir::TypeArg::Type(self.project_type_arg_type(ty)),
            core_ir::TypeArg::Bounds(bounds) => core_ir::TypeArg::Type(
                self.project_arg_bounds(bounds)
                    .unwrap_or_else(runtime_projection_fallback_type),
            ),
        }
    }

    pub(super) fn project_type_arg_type(&mut self, ty: &core_ir::Type) -> core_ir::Type {
        if type_arg_type_is_effect_like(ty) {
            self.project_effect(ty)
        } else {
            self.project(ty)
        }
    }

    pub(super) fn project_arg_bounds(
        &mut self,
        bounds: &core_ir::TypeBounds,
    ) -> Option<core_ir::Type> {
        if bounds_type_arg_is_effect_like(bounds) {
            return self.project_effect_bounds(bounds);
        }
        self.project_bounds(bounds)
    }

    pub(super) fn project_bounds(&mut self, bounds: &core_ir::TypeBounds) -> Option<core_ir::Type> {
        match (&bounds.lower, &bounds.upper) {
            (Some(lower), Some(upper)) if lower == upper => return Some(self.project(lower)),
            _ => {}
        }

        let lower = bounds
            .lower
            .as_deref()
            .map(|ty| self.project(ty))
            .filter(|ty| !is_runtime_hole(ty));
        let upper = bounds
            .upper
            .as_deref()
            .map(|ty| self.project(ty))
            .filter(|ty| !is_runtime_hole(ty));

        choose_bounds_pair(lower, upper, BoundsChoice::RuntimeValue)
    }

    pub(super) fn project_effect_bounds(
        &mut self,
        bounds: &core_ir::TypeBounds,
    ) -> Option<core_ir::Type> {
        match (&bounds.lower, &bounds.upper) {
            (Some(lower), Some(upper)) if lower == upper => {
                return Some(self.project_effect(lower));
            }
            _ => {}
        }

        let lower = bounds
            .lower
            .as_deref()
            .map(|ty| self.project_effect(ty))
            .filter(|ty| !is_runtime_hole(ty));
        let upper = bounds
            .upper
            .as_deref()
            .map(|ty| self.project_effect(ty))
            .filter(|ty| !is_runtime_hole(ty));

        choose_bounds_pair(lower, upper, BoundsChoice::RuntimeValue)
    }

    pub(super) fn project_effect(&mut self, ty: &core_ir::Type) -> core_ir::Type {
        match ty {
            core_ir::Type::Never => core_ir::Type::Never,
            core_ir::Type::Any => core_ir::Type::Any,
            core_ir::Type::Var(var) if self.allowed_vars.contains(var) => {
                core_ir::Type::Var(var.clone())
            }
            core_ir::Type::Var(_) => runtime_projection_fallback_type(),
            core_ir::Type::Named { path, args } if is_never_path(path) && args.is_empty() => {
                core_ir::Type::Never
            }
            core_ir::Type::Named { path, args } => core_ir::Type::Named {
                path: path.clone(),
                args: if is_synthetic_var_effect_path(path) {
                    Vec::new()
                } else {
                    args.iter().map(|arg| self.project_arg(arg)).collect()
                },
            },
            core_ir::Type::Row { items, tail } => self.project_effect_row(items, tail),
            core_ir::Type::Union(items) => self.project_effect_choice(items),
            core_ir::Type::Inter(items) => self.project_effect_intersection(items),
            core_ir::Type::Recursive { var, body } => {
                if !self.stack.insert(var.clone()) {
                    return runtime_projection_fallback_type();
                }
                let body = self.project_effect(body);
                self.stack.remove(var);
                core_ir::Type::Recursive {
                    var: var.clone(),
                    body: Box::new(body),
                }
            }
            other => self.project(other),
        }
    }

    pub(super) fn project_effect_row(
        &mut self,
        items: &[core_ir::Type],
        tail: &core_ir::Type,
    ) -> core_ir::Type {
        let mut projected = Vec::new();
        for item in items {
            self.push_projected_effect(item, &mut projected);
        }
        match self.project_effect(tail) {
            effect if effect_is_empty(&effect) => {}
            core_ir::Type::Any if projected.is_empty() => return core_ir::Type::Any,
            core_ir::Type::Any => {}
            core_ir::Type::Var(var) if projected.is_empty() => return core_ir::Type::Var(var),
            core_ir::Type::Var(var) => push_unique_effect(&mut projected, core_ir::Type::Var(var)),
            core_ir::Type::Row { items, .. } => {
                for item in items {
                    push_unique_effect(&mut projected, item);
                }
            }
            effect => push_unique_effect(&mut projected, effect),
        }
        runtime_effect_row_from_items(projected)
    }

    pub(super) fn project_effect_choice(&mut self, items: &[core_ir::Type]) -> core_ir::Type {
        let mut projected = Vec::new();
        for item in items {
            self.push_projected_effect(item, &mut projected);
        }
        runtime_effect_row_from_items(projected)
    }

    pub(super) fn project_effect_intersection(&mut self, items: &[core_ir::Type]) -> core_ir::Type {
        let mut projected = Vec::new();
        let mut fallback_var = None;
        for item in items {
            match self.project_effect(item) {
                effect if effect_is_empty(&effect) => return core_ir::Type::Never,
                core_ir::Type::Any => {}
                core_ir::Type::Var(var) => {
                    fallback_var.get_or_insert(core_ir::Type::Var(var));
                }
                core_ir::Type::Row { items, .. } => {
                    for item in items {
                        push_unique_effect(&mut projected, item);
                    }
                }
                effect => push_unique_effect(&mut projected, effect),
            }
        }
        if projected.is_empty() {
            fallback_var.unwrap_or(core_ir::Type::Never)
        } else {
            runtime_effect_row_from_items(projected)
        }
    }

    pub(super) fn push_projected_effect(
        &mut self,
        ty: &core_ir::Type,
        out: &mut Vec<core_ir::Type>,
    ) {
        match self.project_effect(ty) {
            effect if effect_is_empty(&effect) => {}
            core_ir::Type::Any | core_ir::Type::Var(_) => {}
            core_ir::Type::Row { items, .. } => {
                for item in items {
                    push_unique_effect(out, item);
                }
            }
            effect => push_unique_effect(out, effect),
        }
    }

    pub(super) fn project_choice(&mut self, items: &[core_ir::Type]) -> Option<core_ir::Type> {
        let mut best = None;
        for item in items {
            let projected = self.project(item);
            if is_runtime_hole(&projected) {
                continue;
            }
            best = choose_core_type_candidate(best, projected, TypeChoice::RuntimeValue);
        }
        best
    }

    pub(super) fn project_hir_choice(&mut self, items: &[core_ir::Type]) -> Option<RuntimeType> {
        let mut best = None;
        for item in items {
            let projected = self.project_hir(item);
            if runtime_type_is_imprecise_runtime_slot(&projected) {
                continue;
            }
            best = match best {
                Some(current) => Some(choose_hir_projection_type(current, projected)),
                None => Some(projected),
            };
        }
        best
    }
}

fn choose_hir_projection_type(left: RuntimeType, right: RuntimeType) -> RuntimeType {
    if hir_type_imprecision_count(&right) < hir_type_imprecision_count(&left) {
        right
    } else {
        left
    }
}

fn bounds_type_arg_is_effect_like(bounds: &core_ir::TypeBounds) -> bool {
    bounds
        .lower
        .as_deref()
        .is_some_and(type_arg_type_is_effect_like)
        || bounds
            .upper
            .as_deref()
            .is_some_and(type_arg_type_is_effect_like)
}

fn type_arg_type_is_effect_like(ty: &core_ir::Type) -> bool {
    match ty {
        core_ir::Type::Row { .. } => true,
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => {
            !items.is_empty() && items.iter().all(type_arg_type_is_effect_like)
        }
        core_ir::Type::Recursive { body, .. } => type_arg_type_is_effect_like(body),
        _ => false,
    }
}

pub(super) fn is_synthetic_var_effect_path(path: &core_ir::Path) -> bool {
    path.segments
        .first()
        .is_some_and(|segment| segment.0.starts_with('&') && segment.0.contains('#'))
}
