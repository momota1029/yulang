use super::*;

#[cfg(test)]
pub(super) fn project_runtime_type(ty: &typed_ir::Type) -> typed_ir::Type {
    RuntimeTypeProjector::new(&BTreeSet::new()).project(ty)
}

pub fn project_runtime_effect(ty: &typed_ir::Type) -> typed_ir::Type {
    RuntimeTypeProjector::new(&BTreeSet::new()).project_effect(ty)
}

pub fn project_runtime_effect_with_vars(
    ty: &typed_ir::Type,
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::Type {
    RuntimeTypeProjector::new(allowed_vars).project_effect(ty)
}

pub fn project_runtime_bounds(bounds: &typed_ir::TypeBounds) -> Option<typed_ir::Type> {
    RuntimeTypeProjector::new(&BTreeSet::new()).project_bounds(bounds)
}

pub fn project_runtime_type_with_vars(
    ty: &typed_ir::Type,
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::Type {
    RuntimeTypeProjector::new(allowed_vars).project(ty)
}

pub fn project_runtime_hint_type_with_vars(
    ty: &typed_ir::Type,
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
) -> typed_ir::Type {
    RuntimeTypeProjector::new(allowed_vars).project_hint(ty)
}

pub fn project_runtime_hir_type_with_vars(
    ty: &typed_ir::Type,
    allowed_vars: &BTreeSet<typed_ir::TypeVar>,
) -> RuntimeType {
    RuntimeTypeProjector::new(allowed_vars).project_hir(ty)
}

pub(super) struct RuntimeTypeProjector<'a> {
    pub(super) allowed_vars: &'a BTreeSet<typed_ir::TypeVar>,
    pub(super) stack: HashSet<typed_ir::TypeVar>,
}

impl<'a> RuntimeTypeProjector<'a> {
    pub(super) fn new(allowed_vars: &'a BTreeSet<typed_ir::TypeVar>) -> Self {
        Self {
            allowed_vars,
            stack: HashSet::new(),
        }
    }

    pub(super) fn project(&mut self, ty: &typed_ir::Type) -> typed_ir::Type {
        match ty {
            typed_ir::Type::Unknown => runtime_projection_fallback_type(),
            typed_ir::Type::Never => typed_ir::Type::Never,
            typed_ir::Type::Any => typed_ir::Type::Any,
            typed_ir::Type::Var(var) if self.allowed_vars.contains(var) => {
                typed_ir::Type::Var(var.clone())
            }
            typed_ir::Type::Var(_) => runtime_projection_fallback_type(),
            typed_ir::Type::Named { path, args } if is_never_path(path) && args.is_empty() => {
                typed_ir::Type::Never
            }
            typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
                path: path.clone(),
                args: if is_synthetic_var_effect_path(path) {
                    Vec::new()
                } else {
                    args.iter().map(|arg| self.project_arg(arg)).collect()
                },
            },
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => typed_ir::Type::Fun {
                param: Box::new(self.project(param)),
                param_effect: Box::new(self.project_effect(param_effect)),
                ret_effect: Box::new(self.project_effect(ret_effect)),
                ret: Box::new(self.project(ret)),
            },
            typed_ir::Type::Tuple(items) => {
                typed_ir::Type::Tuple(items.iter().map(|item| self.project(item)).collect())
            }
            typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| typed_ir::RecordField {
                        name: field.name.clone(),
                        value: self.project(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
                spread: record.spread.as_ref().map(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) => {
                        typed_ir::RecordSpread::Head(Box::new(self.project(ty)))
                    }
                    typed_ir::RecordSpread::Tail(ty) => {
                        typed_ir::RecordSpread::Tail(Box::new(self.project(ty)))
                    }
                }),
            }),
            typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .map(|case| typed_ir::VariantCase {
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
            typed_ir::Type::Union(items) => self
                .project_choice(items)
                .unwrap_or_else(runtime_projection_fallback_type),
            typed_ir::Type::Inter(items) => self
                .project_choice(items)
                .unwrap_or_else(runtime_projection_fallback_type),
            typed_ir::Type::Row { .. } => runtime_projection_fallback_type(),
            typed_ir::Type::Recursive { var, body } => {
                if !self.stack.insert(var.clone()) {
                    return runtime_projection_fallback_type();
                }
                let body = self.project(body);
                self.stack.remove(var);
                typed_ir::Type::Recursive {
                    var: var.clone(),
                    body: Box::new(body),
                }
            }
        }
    }

    pub(super) fn project_hint(&mut self, ty: &typed_ir::Type) -> typed_ir::Type {
        match ty {
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => typed_ir::Type::Fun {
                param: Box::new(self.project_hint(param)),
                param_effect: Box::new(self.project_effect(param_effect)),
                ret_effect: Box::new(self.project_effect(ret_effect)),
                ret: Box::new(self.project_hint(ret)),
            },
            typed_ir::Type::Tuple(items) => {
                typed_ir::Type::Tuple(items.iter().map(|item| self.project_hint(item)).collect())
            }
            typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .map(|field| typed_ir::RecordField {
                        name: field.name.clone(),
                        value: self.project_hint(&field.value),
                        optional: field.optional,
                    })
                    .collect(),
                spread: record.spread.as_ref().map(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) => {
                        typed_ir::RecordSpread::Head(Box::new(self.project_hint(ty)))
                    }
                    typed_ir::RecordSpread::Tail(ty) => {
                        typed_ir::RecordSpread::Tail(Box::new(self.project_hint(ty)))
                    }
                }),
            }),
            typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .map(|case| typed_ir::VariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .map(|payload| self.project_hint(payload))
                            .collect(),
                    })
                    .collect(),
                tail: variant
                    .tail
                    .as_ref()
                    .map(|tail| Box::new(self.project_hint(tail))),
            }),
            typed_ir::Type::Union(items) => self
                .project_hint_choice(items, true)
                .unwrap_or_else(runtime_projection_fallback_type),
            typed_ir::Type::Inter(items) => self
                .project_hint_choice(items, false)
                .unwrap_or_else(runtime_projection_fallback_type),
            other => self.project(other),
        }
    }

    pub(super) fn project_hir(&mut self, ty: &typed_ir::Type) -> RuntimeType {
        match ty {
            typed_ir::Type::Unknown => RuntimeType::unknown(),
            typed_ir::Type::Var(var) if self.allowed_vars.contains(var) => {
                RuntimeType::value(typed_ir::Type::Var(var.clone()))
            }
            typed_ir::Type::Var(_) => RuntimeType::unknown(),
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                let param = self.project_hir_effected_value(param, param_effect);
                let ret = self.project_hir_effected_value(ret, ret_effect);
                RuntimeType::fun(param, ret)
            }
            typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => self
                .project_hir_choice(items)
                .unwrap_or_else(RuntimeType::unknown),
            typed_ir::Type::Row { .. } => RuntimeType::unknown(),
            other => RuntimeType::value(self.project(other)),
        }
    }

    pub(super) fn project_hir_effected_value(
        &mut self,
        value: &typed_ir::Type,
        effect: &typed_ir::Type,
    ) -> RuntimeType {
        let value = self.project_hir(value);
        let effect = self.project_effect(effect);
        if should_thunk_effect(&effect) {
            RuntimeType::thunk(effect, value)
        } else {
            value
        }
    }

    pub(super) fn project_arg(&mut self, arg: &typed_ir::TypeArg) -> typed_ir::TypeArg {
        match arg {
            typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(self.project_type_arg_type(ty)),
            typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Type(
                self.project_arg_bounds(bounds)
                    .unwrap_or_else(runtime_projection_fallback_type),
            ),
        }
    }

    pub(super) fn project_type_arg_type(&mut self, ty: &typed_ir::Type) -> typed_ir::Type {
        if type_is_effect_like(ty) {
            self.project_effect(ty)
        } else {
            self.project(ty)
        }
    }

    pub(super) fn project_arg_bounds(
        &mut self,
        bounds: &typed_ir::TypeBounds,
    ) -> Option<typed_ir::Type> {
        if bounds_type_arg_is_effect_like(bounds) {
            return self.project_effect_bounds(bounds);
        }
        self.project_bounds(bounds)
    }

    pub(super) fn project_bounds(
        &mut self,
        bounds: &typed_ir::TypeBounds,
    ) -> Option<typed_ir::Type> {
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
        bounds: &typed_ir::TypeBounds,
    ) -> Option<typed_ir::Type> {
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

    pub(super) fn project_effect(&mut self, ty: &typed_ir::Type) -> typed_ir::Type {
        match ty {
            typed_ir::Type::Unknown => typed_ir::Type::Never,
            typed_ir::Type::Never => typed_ir::Type::Never,
            typed_ir::Type::Any => typed_ir::Type::Any,
            typed_ir::Type::Var(var) if self.allowed_vars.contains(var) => {
                typed_ir::Type::Var(var.clone())
            }
            typed_ir::Type::Var(_) => typed_ir::Type::Never,
            typed_ir::Type::Named { path, args } if is_never_path(path) && args.is_empty() => {
                typed_ir::Type::Never
            }
            typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
                path: path.clone(),
                args: self.project_effect_atom_args(path, args),
            },
            typed_ir::Type::Row { items, tail } => self.project_effect_row(items, tail),
            typed_ir::Type::Union(items) => self.project_effect_choice(items),
            typed_ir::Type::Inter(items) => self.project_effect_intersection(items),
            typed_ir::Type::Recursive { var, body } => {
                if !self.stack.insert(var.clone()) {
                    return runtime_projection_fallback_type();
                }
                let body = self.project_effect(body);
                self.stack.remove(var);
                typed_ir::Type::Recursive {
                    var: var.clone(),
                    body: Box::new(body),
                }
            }
            other => self.project(other),
        }
    }

    pub(super) fn project_effect_row(
        &mut self,
        items: &[typed_ir::Type],
        tail: &typed_ir::Type,
    ) -> typed_ir::Type {
        let mut projected = Vec::new();
        for item in items {
            self.push_projected_effect(item, &mut projected);
        }
        match self.project_effect(tail) {
            effect if effect_is_empty(&effect) => {}
            typed_ir::Type::Any if projected.is_empty() => return typed_ir::Type::Any,
            typed_ir::Type::Any => {}
            typed_ir::Type::Var(var) if projected.is_empty() => return typed_ir::Type::Var(var),
            typed_ir::Type::Var(var) => {
                push_unique_effect(&mut projected, typed_ir::Type::Var(var))
            }
            typed_ir::Type::Row { items, .. } => {
                for item in items {
                    push_unique_effect(&mut projected, item);
                }
            }
            effect => push_unique_effect(&mut projected, effect),
        }
        runtime_effect_row_from_items(projected)
    }

    fn project_effect_atom_args(
        &mut self,
        path: &typed_ir::Path,
        args: &[typed_ir::TypeArg],
    ) -> Vec<typed_ir::TypeArg> {
        if is_synthetic_var_effect_path(path) {
            return Vec::new();
        }
        let projected = args
            .iter()
            .map(|arg| self.project_arg(arg))
            .collect::<Vec<_>>();
        if projected.iter().any(type_arg_contains_runtime_hole) {
            return Vec::new();
        }
        projected
    }

    pub(super) fn project_effect_choice(&mut self, items: &[typed_ir::Type]) -> typed_ir::Type {
        let mut projected = Vec::new();
        for item in items {
            self.push_projected_effect(item, &mut projected);
        }
        runtime_effect_row_from_items(projected)
    }

    pub(super) fn project_effect_intersection(
        &mut self,
        items: &[typed_ir::Type],
    ) -> typed_ir::Type {
        let mut projected = Vec::new();
        let mut fallback_var = None;
        for item in items {
            match self.project_effect(item) {
                effect if effect_is_empty(&effect) => return typed_ir::Type::Never,
                typed_ir::Type::Any => {}
                typed_ir::Type::Var(var) => {
                    fallback_var.get_or_insert(typed_ir::Type::Var(var));
                }
                typed_ir::Type::Row { items, .. } => {
                    for item in items {
                        push_unique_effect(&mut projected, item);
                    }
                }
                effect => push_unique_effect(&mut projected, effect),
            }
        }
        if projected.is_empty() {
            fallback_var.unwrap_or(typed_ir::Type::Never)
        } else {
            runtime_effect_row_from_items(projected)
        }
    }

    pub(super) fn push_projected_effect(
        &mut self,
        ty: &typed_ir::Type,
        out: &mut Vec<typed_ir::Type>,
    ) {
        match self.project_effect(ty) {
            effect if effect_is_empty(&effect) => {}
            typed_ir::Type::Unknown | typed_ir::Type::Any => {}
            typed_ir::Type::Var(var) => push_unique_effect(out, typed_ir::Type::Var(var)),
            typed_ir::Type::Row { items, .. } => {
                for item in items {
                    push_unique_effect(out, item);
                }
            }
            effect => push_unique_effect(out, effect),
        }
    }

    pub(super) fn project_choice(&mut self, items: &[typed_ir::Type]) -> Option<typed_ir::Type> {
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

    pub(super) fn project_hint_choice(
        &mut self,
        items: &[typed_ir::Type],
        union: bool,
    ) -> Option<typed_ir::Type> {
        let mut projected = Vec::new();
        for item in items {
            let item = self.project_hint(item);
            if is_runtime_hole(&item) {
                continue;
            }
            if !projected.contains(&item) {
                projected.push(item);
            }
        }
        match projected.len() {
            0 => None,
            1 => projected.pop(),
            _ if union => Some(typed_ir::Type::Union(projected)),
            _ => Some(typed_ir::Type::Inter(projected)),
        }
    }

    pub(super) fn project_hir_choice(&mut self, items: &[typed_ir::Type]) -> Option<RuntimeType> {
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

fn bounds_type_arg_is_effect_like(bounds: &typed_ir::TypeBounds) -> bool {
    bounds.lower.as_deref().is_some_and(type_is_effect_like)
        || bounds.upper.as_deref().is_some_and(type_is_effect_like)
}

fn type_arg_contains_runtime_hole(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_contains_runtime_hole(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_deref()
                .is_some_and(core_type_contains_runtime_hole)
                || bounds
                    .upper
                    .as_deref()
                    .is_some_and(core_type_contains_runtime_hole)
        }
    }
}

fn core_type_contains_runtime_hole(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_runtime_hole),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_contains_runtime_hole(param)
                || core_type_contains_runtime_hole(param_effect)
                || core_type_contains_runtime_hole(ret_effect)
                || core_type_contains_runtime_hole(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(core_type_contains_runtime_hole),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_contains_runtime_hole(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_contains_runtime_hole(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(core_type_contains_runtime_hole))
                || variant
                    .tail
                    .as_deref()
                    .is_some_and(core_type_contains_runtime_hole)
        }
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(core_type_contains_runtime_hole)
                || core_type_contains_runtime_hole(tail)
        }
        typed_ir::Type::Recursive { body, .. } => core_type_contains_runtime_hole(body),
        typed_ir::Type::Never | typed_ir::Type::Any | typed_ir::Type::Var(_) => false,
    }
}

pub(super) fn is_synthetic_var_effect_path(path: &typed_ir::Path) -> bool {
    path.segments
        .first()
        .is_some_and(|segment| segment.0.starts_with('&') && segment.0.contains('#'))
}
