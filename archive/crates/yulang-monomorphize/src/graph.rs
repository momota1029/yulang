use std::collections::{BTreeMap, BTreeSet, VecDeque};

use yulang_runtime_ir::{FinalizedBinding as Binding, RuntimeType};
use yulang_typed_ir as typed_ir;

use crate::{MonomorphizeDiagnostic, MonomorphizeResult};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct TypeGraph {
    next_fresh: usize,
    slots: BTreeMap<typed_ir::TypeVar, TypeVarBounds>,
    external_vars: BTreeSet<typed_ir::TypeVar>,
    constraints: Vec<SubtypeConstraint>,
    cast_order: TypeCastOrder,
}

impl TypeGraph {
    pub fn with_cast_order(cast_order: TypeCastOrder) -> Self {
        Self {
            cast_order,
            ..Self::default()
        }
    }

    pub fn instantiate_principal(&mut self, binding: &Binding) -> PrincipalInstance {
        let mut renames = BTreeMap::new();
        for param in &binding.type_params {
            let fresh = self.fresh_var(param);
            self.slots.entry(fresh.clone()).or_default();
            renames.insert(param.clone(), fresh);
        }
        PrincipalInstance {
            original_binding: binding.name.clone(),
            principal_type: rename_type(&binding.scheme.body, &renames),
            type_params: renames
                .into_iter()
                .map(|(original, fresh)| PrincipalTypeParam { original, fresh })
                .collect(),
        }
    }

    pub fn collect_runtime_bounds(
        &mut self,
        template: &typed_ir::Type,
        bounds: &RuntimeBounds,
    ) -> MonomorphizeResult<()> {
        if let Some(lower) = &bounds.lower {
            self.collect_runtime(template, lower, BoundSide::Lower)?;
        }
        if let Some(upper) = &bounds.upper {
            self.collect_runtime(template, upper, BoundSide::Upper)?;
        }
        self.propagate_constraints()
    }

    pub fn collect_runtime_lower(
        &mut self,
        template: &typed_ir::Type,
        lower: &RuntimeType,
    ) -> MonomorphizeResult<()> {
        self.collect_runtime(template, lower, BoundSide::Lower)?;
        self.propagate_constraints()
    }

    pub fn collect_runtime_upper(
        &mut self,
        template: &typed_ir::Type,
        upper: &RuntimeType,
    ) -> MonomorphizeResult<()> {
        self.collect_runtime(template, upper, BoundSide::Upper)?;
        self.propagate_constraints()
    }

    pub fn fresh_hole(&mut self, prefix: &str) -> typed_ir::Type {
        let var = self.fresh_var(&typed_ir::TypeVar(prefix.into()));
        self.slots.entry(var.clone()).or_default();
        typed_ir::Type::Var(var)
    }

    pub fn mark_external_vars(&mut self, vars: impl IntoIterator<Item = typed_ir::TypeVar>) {
        self.external_vars.extend(vars);
    }

    pub fn constrain_subtype(
        &mut self,
        lower: typed_ir::Type,
        upper: typed_ir::Type,
    ) -> MonomorphizeResult<()> {
        let constraint = SubtypeConstraint { lower, upper };
        if !self.constraints.contains(&constraint) {
            self.constraints.push(constraint);
        }
        self.propagate_constraints()
    }

    pub fn default_unbound_lower(
        &mut self,
        vars: BTreeSet<typed_ir::TypeVar>,
        lower: typed_ir::Type,
    ) -> MonomorphizeResult<()> {
        self.default_unbound_lower_inner(vars, lower)?;
        self.propagate_constraints()
    }

    fn default_unbound_lower_inner(
        &mut self,
        vars: BTreeSet<typed_ir::TypeVar>,
        lower: typed_ir::Type,
    ) -> MonomorphizeResult<bool> {
        let mut changed = false;
        for var in vars {
            if self.external_vars.contains(&var) {
                continue;
            }
            let Some(slot) = self.slots.get_mut(&var) else {
                continue;
            };
            if slot.lower.is_none() && slot.upper.is_none() {
                changed |= slot.push_lower(var, lower.clone(), &self.cast_order)?;
            }
        }
        Ok(changed)
    }

    pub fn solve(self) -> GraphSolution {
        let type_vars = self
            .slots
            .into_iter()
            .map(|(var, bounds)| {
                let solution = bounds.solution_ref().cloned();
                ResolvedTypeVar {
                    var,
                    bounds,
                    solution,
                }
            })
            .collect();
        GraphSolution { type_vars }
    }

    pub fn slot(&self, var: &typed_ir::TypeVar) -> Option<&TypeVarBounds> {
        self.slots.get(var)
    }

    fn fresh_var(&mut self, source: &typed_ir::TypeVar) -> typed_ir::TypeVar {
        loop {
            let fresh = typed_ir::TypeVar(format!("{}#{}", source.0, self.next_fresh));
            self.next_fresh += 1;
            if !self.slots.contains_key(&fresh) && !self.external_vars.contains(&fresh) {
                return fresh;
            }
        }
    }

    fn collect_runtime(
        &mut self,
        template: &typed_ir::Type,
        actual: &RuntimeType,
        side: BoundSide,
    ) -> MonomorphizeResult<()> {
        match actual {
            RuntimeType::Value(actual) => self.collect_core(template, actual, side),
            RuntimeType::Fun { param, ret } => {
                let typed_ir::Type::Fun {
                    param: template_param,
                    param_effect: template_param_effect,
                    ret_effect: template_ret_effect,
                    ret: template_ret,
                } = template
                else {
                    return Ok(());
                };
                let RuntimeEffectedType {
                    value: actual_param,
                    effect: actual_param_effect,
                } = split_runtime_effected_type(param);
                let RuntimeEffectedType {
                    value: actual_ret,
                    effect: actual_ret_effect,
                } = split_runtime_effected_type(ret);
                let param_side = side.flip();
                if !(param_side == BoundSide::Lower && runtime_value_is_top(actual_param)) {
                    self.collect_runtime(template_param, actual_param, param_side)?;
                }
                self.collect_runtime_effect(template_param_effect, actual_param_effect, side)?;
                self.collect_runtime_effect(template_ret_effect, actual_ret_effect, side)?;
                self.collect_runtime(template_ret, actual_ret, side)
            }
            RuntimeType::Thunk { value, .. } => self.collect_runtime(template, value, side),
            RuntimeType::Unknown => Ok(()),
        }
    }

    fn collect_core(
        &mut self,
        template: &typed_ir::Type,
        actual: &typed_ir::Type,
        side: BoundSide,
    ) -> MonomorphizeResult<()> {
        match template {
            typed_ir::Type::Var(var) => self.record(var.clone(), actual.clone(), side).map(|_| ()),
            typed_ir::Type::Named { path, args } => {
                let typed_ir::Type::Named {
                    path: actual_path,
                    args: actual_args,
                } = actual
                else {
                    return Ok(());
                };
                if path != actual_path || args.len() != actual_args.len() {
                    return Ok(());
                }
                for (template, actual) in args.iter().zip(actual_args) {
                    self.collect_type_arg(template, actual, side)?;
                }
                Ok(())
            }
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                let typed_ir::Type::Fun {
                    param: actual_param,
                    param_effect: actual_param_effect,
                    ret_effect: actual_ret_effect,
                    ret: actual_ret,
                } = actual
                else {
                    return Ok(());
                };
                let param_side = side.flip();
                if !(param_side == BoundSide::Lower
                    && matches!(actual_param.as_ref(), typed_ir::Type::Any))
                {
                    self.collect_core(param, actual_param, param_side)?;
                }
                self.collect_core(param_effect, actual_param_effect, side)?;
                self.collect_core(ret_effect, actual_ret_effect, side)?;
                self.collect_core(ret, actual_ret, side)
            }
            typed_ir::Type::Tuple(items) => {
                let typed_ir::Type::Tuple(actual_items) = actual else {
                    return Ok(());
                };
                if items.len() != actual_items.len() {
                    return Ok(());
                }
                for (template, actual) in items.iter().zip(actual_items) {
                    self.collect_core(template, actual, side)?;
                }
                Ok(())
            }
            typed_ir::Type::Row { items, tail } => {
                let typed_ir::Type::Row {
                    items: actual_items,
                    tail: actual_tail,
                } = actual
                else {
                    return Ok(());
                };
                self.collect_row(items, tail, actual_items, actual_tail, side)
            }
            typed_ir::Type::Variant(template) => {
                let typed_ir::Type::Variant(actual) = actual else {
                    return Ok(());
                };
                self.collect_variant(template, actual, side)
            }
            typed_ir::Type::Record(template) => {
                let typed_ir::Type::Record(actual) = actual else {
                    return Ok(());
                };
                self.collect_record(template, actual, side)
            }
            typed_ir::Type::Unknown
            | typed_ir::Type::Never
            | typed_ir::Type::Any
            | typed_ir::Type::Union(_)
            | typed_ir::Type::Inter(_)
            | typed_ir::Type::Recursive { .. } => Ok(()),
        }
    }

    fn collect_runtime_effect(
        &mut self,
        template: &typed_ir::Type,
        actual: RuntimeEffectRef<'_>,
        side: BoundSide,
    ) -> MonomorphizeResult<()> {
        match actual {
            RuntimeEffectRef::Known(actual) => self.collect_core(template, actual, side),
            RuntimeEffectRef::Pure | RuntimeEffectRef::Unknown => Ok(()),
        }
    }

    fn propagate_constraints(&mut self) -> MonomorphizeResult<()> {
        loop {
            let mut changed = false;
            for constraint in self.constraints.clone() {
                changed |= self.apply_subtype_constraint(constraint.lower, constraint.upper)?;
            }
            if !changed {
                return Ok(());
            }
        }
    }

    fn apply_subtype_constraint(
        &mut self,
        lower: typed_ir::Type,
        upper: typed_ir::Type,
    ) -> MonomorphizeResult<bool> {
        self.apply_subtype_constraint_inner(lower, upper, &mut Vec::new())
    }

    fn apply_subtype_constraint_inner(
        &mut self,
        lower: typed_ir::Type,
        upper: typed_ir::Type,
        seen: &mut Vec<SubtypeConstraint>,
    ) -> MonomorphizeResult<bool> {
        let constraint = SubtypeConstraint {
            lower: lower.clone(),
            upper: upper.clone(),
        };
        if seen.contains(&constraint) {
            return Ok(false);
        }
        seen.push(constraint);
        if lower == upper || matches!(upper, typed_ir::Type::Any) {
            return Ok(false);
        }
        match (lower, upper) {
            (typed_ir::Type::Unknown, _) | (_, typed_ir::Type::Unknown) => Ok(false),
            (typed_ir::Type::Var(lower), typed_ir::Type::Var(upper))
                if self.external_vars.contains(&lower) && !self.external_vars.contains(&upper) =>
            {
                let mut changed = false;
                let lower = typed_ir::Type::Var(lower);
                if let Some(bound) = self
                    .slots
                    .get(&upper)
                    .and_then(|slot| slot.upper.as_ref())
                    .cloned()
                    .filter(|bound| !self.upper_bound_chain_reaches(bound, &upper))
                {
                    changed |= self.apply_subtype_constraint_inner(lower.clone(), bound, seen)?;
                }
                changed |= self.record(upper, lower, BoundSide::Lower)?;
                Ok(changed)
            }
            (typed_ir::Type::Var(lower), upper) => {
                if self.external_vars.contains(&lower) {
                    return Ok(false);
                }
                let mut changed = false;
                if let Some(bound) = self
                    .slots
                    .get(&lower)
                    .and_then(|slot| slot.lower.as_ref())
                    .cloned()
                    .filter(|bound| !self.lower_bound_chain_reaches(bound, &lower))
                {
                    changed |= self.apply_subtype_constraint_inner(bound, upper.clone(), seen)?;
                }
                if let typed_ir::Type::Var(upper_var) = &upper
                    && let Some(bound) = self
                        .slots
                        .get(upper_var)
                        .and_then(|slot| slot.upper.as_ref())
                        .cloned()
                        .filter(|bound| !self.upper_bound_chain_reaches(bound, &lower))
                {
                    changed |= self.apply_subtype_constraint_inner(
                        typed_ir::Type::Var(lower.clone()),
                        bound,
                        seen,
                    )?;
                }
                changed |= self.record(lower, upper, BoundSide::Upper)?;
                Ok(changed)
            }
            (lower, typed_ir::Type::Var(upper)) => {
                if self.external_vars.contains(&upper) {
                    return Ok(false);
                }
                let mut changed = false;
                let lower = self.known_lower_or_self(lower);
                if let Some(bound) = self
                    .slots
                    .get(&upper)
                    .and_then(|slot| slot.upper.as_ref())
                    .cloned()
                    .filter(|bound| !self.upper_bound_chain_reaches(bound, &upper))
                {
                    changed |= self.apply_subtype_constraint_inner(lower.clone(), bound, seen)?;
                }
                changed |= self.record(upper, lower, BoundSide::Lower)?;
                Ok(changed)
            }
            (
                typed_ir::Type::Fun {
                    param: lower_param,
                    param_effect: lower_param_effect,
                    ret_effect: lower_ret_effect,
                    ret: lower_ret,
                },
                typed_ir::Type::Fun {
                    param: upper_param,
                    param_effect: upper_param_effect,
                    ret_effect: upper_ret_effect,
                    ret: upper_ret,
                },
            ) => {
                let mut changed = false;
                changed |= self.apply_subtype_constraint_inner(*upper_param, *lower_param, seen)?;
                changed |= self.apply_subtype_constraint_inner(
                    *lower_param_effect,
                    *upper_param_effect,
                    seen,
                )?;
                changed |= self.apply_subtype_constraint_inner(
                    *lower_ret_effect,
                    *upper_ret_effect,
                    seen,
                )?;
                changed |= self.apply_subtype_constraint_inner(*lower_ret, *upper_ret, seen)?;
                Ok(changed)
            }
            (
                typed_ir::Type::Named {
                    path: lower_path,
                    args: lower_args,
                },
                typed_ir::Type::Named {
                    path: upper_path,
                    args: upper_args,
                },
            ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
                let mut changed = false;
                for (lower, upper) in lower_args.into_iter().zip(upper_args) {
                    changed |= self.constrain_type_arg(lower, upper, seen)?;
                }
                Ok(changed)
            }
            (typed_ir::Type::Tuple(lower), typed_ir::Type::Tuple(upper))
                if lower.len() == upper.len() =>
            {
                let mut changed = false;
                for (lower, upper) in lower.into_iter().zip(upper) {
                    changed |= self.apply_subtype_constraint_inner(lower, upper, seen)?;
                }
                Ok(changed)
            }
            (typed_ir::Type::Union(items), upper) => {
                let mut changed = false;
                for item in items {
                    changed |= self.apply_subtype_constraint_inner(item, upper.clone(), seen)?;
                }
                Ok(changed)
            }
            (lower, typed_ir::Type::Inter(items)) => {
                let mut changed = false;
                for item in items {
                    changed |= self.apply_subtype_constraint_inner(lower.clone(), item, seen)?;
                }
                Ok(changed)
            }
            (
                typed_ir::Type::Row {
                    items: lower_items,
                    tail: lower_tail,
                },
                typed_ir::Type::Row {
                    items: upper_items,
                    tail: upper_tail,
                },
            ) => self.constrain_row(lower_items, *lower_tail, upper_items, *upper_tail, seen),
            (typed_ir::Type::Variant(lower), typed_ir::Type::Variant(upper)) => {
                self.constrain_variant(lower, upper, seen)
            }
            (typed_ir::Type::Record(lower), typed_ir::Type::Record(upper)) => {
                self.constrain_record(lower, upper, seen)
            }
            _ => Ok(false),
        }
    }

    fn constrain_type_arg(
        &mut self,
        lower: typed_ir::TypeArg,
        upper: typed_ir::TypeArg,
        seen: &mut Vec<SubtypeConstraint>,
    ) -> MonomorphizeResult<bool> {
        match (lower, upper) {
            (typed_ir::TypeArg::Type(lower), typed_ir::TypeArg::Type(upper)) => {
                self.apply_subtype_constraint_inner(lower, upper, seen)
            }
            // `Type(t) <: Bounds(L, U)` is conservatively reduced to
            // `t <: U`. The dual constraint `L <: t` is correct in theory but
            // currently triggers spurious ConflictingBounds when L and U
            // describe the same effect row at different precisions (closed
            // Row vs Inter of open rows). Re-enable both directions once
            // push_bound can merge those forms.
            (typed_ir::TypeArg::Type(lower), typed_ir::TypeArg::Bounds(upper)) => {
                if let Some(upper_upper) = upper.upper {
                    self.apply_subtype_constraint_inner(lower, *upper_upper, seen)
                } else {
                    Ok(false)
                }
            }
            // `Bounds(L, U) <: Type(t)` is conservatively reduced to
            // `L <: t`. The dual direction is omitted for the same reason as
            // the Type-vs-Bounds case above.
            (typed_ir::TypeArg::Bounds(lower), typed_ir::TypeArg::Type(upper)) => {
                if let Some(lower_lower) = lower.lower {
                    self.apply_subtype_constraint_inner(*lower_lower, upper, seen)
                } else {
                    Ok(false)
                }
            }
            (typed_ir::TypeArg::Bounds(lower), typed_ir::TypeArg::Bounds(upper)) => {
                let mut changed = false;
                if let (Some(lower), Some(upper)) = (lower.lower, upper.lower) {
                    changed |= self.apply_subtype_constraint_inner(*lower, *upper, seen)?;
                }
                if let (Some(lower), Some(upper)) = (lower.upper, upper.upper) {
                    changed |= self.apply_subtype_constraint_inner(*lower, *upper, seen)?;
                }
                Ok(changed)
            }
        }
    }

    fn known_lower_or_self(&self, ty: typed_ir::Type) -> typed_ir::Type {
        let typed_ir::Type::Var(var) = &ty else {
            return ty;
        };
        self.slots
            .get(var)
            .and_then(|slot| slot.lower.as_ref())
            .cloned()
            .unwrap_or(ty)
    }

    fn known_upper_or_self(&self, ty: typed_ir::Type) -> typed_ir::Type {
        let typed_ir::Type::Var(var) = &ty else {
            return ty;
        };
        self.slots
            .get(var)
            .and_then(|slot| slot.upper.as_ref())
            .cloned()
            .unwrap_or(ty)
    }

    fn collect_type_arg(
        &mut self,
        template: &typed_ir::TypeArg,
        actual: &typed_ir::TypeArg,
        side: BoundSide,
    ) -> MonomorphizeResult<()> {
        match (template, actual) {
            (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Type(actual)) => {
                self.collect_core(template, actual, side)
            }
            (typed_ir::TypeArg::Type(template), typed_ir::TypeArg::Bounds(actual)) => {
                if let Some(lower) = actual.lower.as_deref() {
                    self.collect_core(template, lower, BoundSide::Lower)?;
                }
                if let Some(upper) = actual.upper.as_deref() {
                    self.collect_core(template, upper, BoundSide::Upper)?;
                }
                Ok(())
            }
            (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Type(actual)) => {
                if let Some(lower) = template.lower.as_deref() {
                    self.collect_core(lower, actual, side)?;
                }
                if let Some(upper) = template.upper.as_deref() {
                    self.collect_core(upper, actual, BoundSide::Upper)?;
                }
                Ok(())
            }
            (typed_ir::TypeArg::Bounds(template), typed_ir::TypeArg::Bounds(actual)) => {
                if let (Some(template), Some(actual)) = (&template.lower, &actual.lower) {
                    self.collect_core(template, actual, BoundSide::Lower)?;
                }
                if let (Some(template), Some(actual)) = (&template.upper, &actual.upper) {
                    self.collect_core(template, actual, BoundSide::Upper)?;
                }
                Ok(())
            }
        }
    }

    fn collect_row(
        &mut self,
        template_items: &[typed_ir::Type],
        template_tail: &typed_ir::Type,
        actual_items: &[typed_ir::Type],
        actual_tail: &typed_ir::Type,
        side: BoundSide,
    ) -> MonomorphizeResult<()> {
        let RowResidual {
            matched,
            unmatched_left,
            unmatched_right,
        } = split_row_items(template_items, actual_items);
        if matched.is_empty() && !template_items.is_empty() && !actual_items.is_empty() {
            return Ok(());
        }
        for (template, actual) in matched {
            self.collect_core(template, actual, side)?;
        }
        if !unmatched_left.is_empty() {
            return Ok(());
        }
        let residual = effect_row_from_items_and_tail(unmatched_right, actual_tail.clone());
        self.collect_core(template_tail, &residual, side)
    }

    fn constrain_row(
        &mut self,
        lower_items: Vec<typed_ir::Type>,
        lower_tail: typed_ir::Type,
        upper_items: Vec<typed_ir::Type>,
        upper_tail: typed_ir::Type,
        seen: &mut Vec<SubtypeConstraint>,
    ) -> MonomorphizeResult<bool> {
        let RowResidual {
            matched,
            unmatched_left,
            unmatched_right,
        } = split_row_items(&lower_items, &upper_items);
        if matched.is_empty() && !lower_items.is_empty() && !upper_items.is_empty() {
            return Ok(false);
        }
        let mut changed = false;
        for (lower, upper) in matched {
            changed |= self.apply_subtype_constraint_inner(lower.clone(), upper.clone(), seen)?;
        }
        let lower_residual = effect_row_from_items_and_tail(unmatched_left, lower_tail);
        let upper_residual = effect_row_from_items_and_tail(unmatched_right, upper_tail);
        changed |= self.apply_subtype_constraint_inner(lower_residual, upper_residual, seen)?;
        Ok(changed)
    }

    fn collect_variant(
        &mut self,
        template: &typed_ir::VariantType,
        actual: &typed_ir::VariantType,
        side: BoundSide,
    ) -> MonomorphizeResult<()> {
        for template_case in &template.cases {
            let Some(actual_case) = find_variant_case(actual, &template_case.name) else {
                if actual.tail.is_none() && side == BoundSide::Lower {
                    for payload in &template_case.payloads {
                        self.collect_core(payload, &typed_ir::Type::Never, BoundSide::Lower)?;
                        self.collect_core(payload, &typed_ir::Type::Never, BoundSide::Upper)?;
                    }
                }
                continue;
            };
            if template_case.payloads.len() != actual_case.payloads.len() {
                continue;
            }
            for (template, actual) in template_case.payloads.iter().zip(&actual_case.payloads) {
                self.collect_core(template, actual, side)?;
            }
        }
        Ok(())
    }

    fn collect_record(
        &mut self,
        template: &typed_ir::RecordType,
        actual: &typed_ir::RecordType,
        side: BoundSide,
    ) -> MonomorphizeResult<()> {
        for template_field in &template.fields {
            let Some(actual_field) = actual
                .fields
                .iter()
                .find(|actual| actual.name == template_field.name)
            else {
                continue;
            };
            self.collect_core(&template_field.value, &actual_field.value, side)?;
        }
        Ok(())
    }

    fn constrain_variant(
        &mut self,
        lower: typed_ir::VariantType,
        upper: typed_ir::VariantType,
        seen: &mut Vec<SubtypeConstraint>,
    ) -> MonomorphizeResult<bool> {
        let mut changed = false;
        for lower_case in &lower.cases {
            let Some(upper_case) = find_variant_case(&upper, &lower_case.name) else {
                continue;
            };
            if lower_case.payloads.len() != upper_case.payloads.len() {
                continue;
            }
            for (lower, upper) in lower_case.payloads.iter().zip(&upper_case.payloads) {
                changed |=
                    self.apply_subtype_constraint_inner(lower.clone(), upper.clone(), seen)?;
            }
        }
        if lower.tail.is_none() {
            for upper_case in &upper.cases {
                if find_variant_case(&lower, &upper_case.name).is_some() {
                    continue;
                }
                for payload in &upper_case.payloads {
                    changed |= self.constrain_absent_structural_payload(payload, seen)?;
                }
            }
        }
        Ok(changed)
    }

    fn constrain_absent_structural_payload(
        &mut self,
        payload: &typed_ir::Type,
        seen: &mut Vec<SubtypeConstraint>,
    ) -> MonomorphizeResult<bool> {
        let mut changed = false;
        changed |=
            self.apply_subtype_constraint_inner(typed_ir::Type::Never, payload.clone(), seen)?;
        changed |=
            self.apply_subtype_constraint_inner(payload.clone(), typed_ir::Type::Never, seen)?;
        let mut vars = BTreeSet::new();
        collect_type_vars(payload, &mut vars);
        changed |= self.default_unbound_lower_inner(vars, typed_ir::Type::Never)?;
        Ok(changed)
    }

    fn constrain_record(
        &mut self,
        lower: typed_ir::RecordType,
        upper: typed_ir::RecordType,
        seen: &mut Vec<SubtypeConstraint>,
    ) -> MonomorphizeResult<bool> {
        let mut changed = false;
        for lower_field in &lower.fields {
            let Some(upper_field) = upper
                .fields
                .iter()
                .find(|upper| upper.name == lower_field.name)
            else {
                continue;
            };
            changed |= self.apply_subtype_constraint_inner(
                lower_field.value.clone(),
                upper_field.value.clone(),
                seen,
            )?;
        }
        if lower.spread.is_none() {
            for upper_field in &upper.fields {
                if lower
                    .fields
                    .iter()
                    .any(|lower| lower.name == upper_field.name)
                {
                    continue;
                }
                if upper_field.optional {
                    changed |=
                        self.constrain_absent_structural_payload(&upper_field.value, seen)?;
                }
            }
        }
        Ok(changed)
    }

    fn record(
        &mut self,
        var: typed_ir::TypeVar,
        mut ty: typed_ir::Type,
        side: BoundSide,
    ) -> MonomorphizeResult<bool> {
        if self.external_vars.contains(&var) {
            return Ok(false);
        }
        ty = match side {
            BoundSide::Lower => self.known_lower_or_self(ty),
            BoundSide::Upper => self.known_upper_or_self(ty),
        };
        ty = normalize_bound_form(&ty);
        if matches!(ty, typed_ir::Type::Unknown) || is_vacuous_bound(&ty, side) {
            return Ok(false);
        }
        // Reject self-bounds: chasing `known_*_or_self` can resolve a Var to a
        // chain that lands back on `var`. Recording `Var(var)` as a bound on
        // `var` creates a self-loop in the slot graph, and the next constraint
        // that walks `slot[var].upper` (or `.lower`) recurses forever and
        // overflows the stack.
        if let typed_ir::Type::Var(other) = &ty
            && *other == var
        {
            return Ok(false);
        }
        if let typed_ir::Type::Var(other) = &ty {
            let cyclic = match side {
                BoundSide::Lower => self.var_lower_bound_chain_reaches(other, &var),
                BoundSide::Upper => self.var_upper_bound_chain_reaches(other, &var),
            };
            if cyclic {
                return Ok(false);
            }
        }
        if std::env::var_os("YULANG_TRACE_ANY_BOUNDS").is_some()
            && side == BoundSide::Lower
            && matches!(ty, typed_ir::Type::Any)
        {
            eprintln!(
                "TRACE Any lower bound var={var:?}\n{}",
                std::backtrace::Backtrace::force_capture()
            );
        }
        let slot = self.slots.entry(var.clone()).or_default();
        let changed = match side {
            BoundSide::Lower => slot.push_lower(var.clone(), ty, &self.cast_order),
            BoundSide::Upper => slot.push_upper(var.clone(), ty, &self.cast_order),
        }?;
        reject_invalid_top_bottom_bounds(&var, slot)?;
        Ok(changed)
    }

    fn lower_bound_chain_reaches(&self, ty: &typed_ir::Type, target: &typed_ir::TypeVar) -> bool {
        let typed_ir::Type::Var(var) = ty else {
            return false;
        };
        self.var_lower_bound_chain_reaches(var, target)
    }

    fn upper_bound_chain_reaches(&self, ty: &typed_ir::Type, target: &typed_ir::TypeVar) -> bool {
        let typed_ir::Type::Var(var) = ty else {
            return false;
        };
        self.var_upper_bound_chain_reaches(var, target)
    }

    fn var_lower_bound_chain_reaches(
        &self,
        start: &typed_ir::TypeVar,
        target: &typed_ir::TypeVar,
    ) -> bool {
        self.var_bound_chain_reaches(start, target, BoundSide::Lower)
    }

    fn var_upper_bound_chain_reaches(
        &self,
        start: &typed_ir::TypeVar,
        target: &typed_ir::TypeVar,
    ) -> bool {
        self.var_bound_chain_reaches(start, target, BoundSide::Upper)
    }

    fn var_bound_chain_reaches(
        &self,
        start: &typed_ir::TypeVar,
        target: &typed_ir::TypeVar,
        side: BoundSide,
    ) -> bool {
        let mut current = start;
        let mut seen = Vec::new();
        loop {
            if current == target {
                return true;
            }
            if seen.iter().any(|seen| seen == current) {
                return false;
            }
            seen.push(current.clone());
            let Some(typed_ir::Type::Var(next)) =
                self.slots.get(current).and_then(|slot| match side {
                    BoundSide::Lower => slot.lower.as_ref(),
                    BoundSide::Upper => slot.upper.as_ref(),
                })
            else {
                return false;
            };
            current = next;
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct TypeCastOrder {
    edges: Vec<TypeCastEdge>,
}

impl TypeCastOrder {
    pub fn from_edges(edges: Vec<(typed_ir::Type, typed_ir::Type)>) -> Self {
        Self {
            edges: edges
                .into_iter()
                .map(|(from, to)| TypeCastEdge { from, to })
                .collect(),
        }
    }

    fn join_lower(&self, left: &typed_ir::Type, right: &typed_ir::Type) -> Option<typed_ir::Type> {
        let left_to_right = self.can_cast(left, right);
        let right_to_left = self.can_cast(right, left);
        match (left_to_right, right_to_left) {
            (true, false) => Some(right.clone()),
            (false, true) => Some(left.clone()),
            _ => None,
        }
    }

    fn meet_upper(&self, left: &typed_ir::Type, right: &typed_ir::Type) -> Option<typed_ir::Type> {
        let left_to_right = self.can_cast(left, right);
        let right_to_left = self.can_cast(right, left);
        match (left_to_right, right_to_left) {
            (true, false) => Some(left.clone()),
            (false, true) => Some(right.clone()),
            _ => None,
        }
    }

    fn can_cast(&self, from: &typed_ir::Type, to: &typed_ir::Type) -> bool {
        if lightweight_bounds_equivalent(from, to) {
            return true;
        }
        let mut seen = Vec::new();
        let mut queue = VecDeque::from([from.clone()]);
        while let Some(current) = queue.pop_front() {
            if seen
                .iter()
                .any(|seen| lightweight_bounds_equivalent(seen, &current))
            {
                continue;
            }
            seen.push(current.clone());
            for edge in &self.edges {
                if !lightweight_bounds_equivalent(&edge.from, &current) {
                    continue;
                }
                if lightweight_bounds_equivalent(&edge.to, to) {
                    return true;
                }
                queue.push_back(edge.to.clone());
            }
        }
        false
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TypeCastEdge {
    from: typed_ir::Type,
    to: typed_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SubtypeConstraint {
    lower: typed_ir::Type,
    upper: typed_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalInstance {
    pub original_binding: typed_ir::Path,
    pub principal_type: typed_ir::Type,
    pub type_params: Vec<PrincipalTypeParam>,
}

impl PrincipalInstance {
    pub fn original_substitutions(
        &self,
        solution: &GraphSolution,
    ) -> Vec<typed_ir::TypeSubstitution> {
        let substitutions = solution.substitutions();
        self.type_params
            .iter()
            .filter_map(|param| {
                solution
                    .solution_for(&param.fresh)
                    .cloned()
                    .map(|ty| typed_ir::TypeSubstitution {
                        var: param.original.clone(),
                        ty: materialize_core_type(ty, &substitutions),
                    })
            })
            .collect()
    }

    pub fn effect_only_type_params(&self) -> BTreeSet<typed_ir::TypeVar> {
        let params = self
            .type_params
            .iter()
            .map(|param| param.fresh.clone())
            .collect::<BTreeSet<_>>();
        let mut vars = TypePositionVars::default();
        collect_type_position_vars(
            &self.principal_type,
            TypePosition::Value,
            &params,
            &mut vars,
        );
        vars.effect
            .difference(&vars.value)
            .cloned()
            .collect::<BTreeSet<_>>()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalTypeParam {
    pub original: typed_ir::TypeVar,
    pub fresh: typed_ir::TypeVar,
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct RuntimeBounds {
    pub lower: Option<RuntimeType>,
    pub upper: Option<RuntimeType>,
}

impl RuntimeBounds {
    pub fn lower(ty: RuntimeType) -> Self {
        Self {
            lower: Some(ty),
            upper: None,
        }
    }

    pub fn upper(ty: RuntimeType) -> Self {
        Self {
            lower: None,
            upper: Some(ty),
        }
    }

    pub fn exact(ty: RuntimeType) -> Self {
        Self {
            lower: Some(ty.clone()),
            upper: Some(ty),
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct TypeVarBounds {
    pub lower: Option<typed_ir::Type>,
    pub upper: Option<typed_ir::Type>,
}

impl TypeVarBounds {
    pub fn solution(self) -> Option<typed_ir::Type> {
        self.lower.or(self.upper)
    }

    pub fn solution_ref(&self) -> Option<&typed_ir::Type> {
        self.lower.as_ref().or(self.upper.as_ref())
    }

    fn push_lower(
        &mut self,
        var: typed_ir::TypeVar,
        ty: typed_ir::Type,
        cast_order: &TypeCastOrder,
    ) -> MonomorphizeResult<bool> {
        push_bound(&mut self.lower, var, ty, BoundSide::Lower, cast_order)
    }

    fn push_upper(
        &mut self,
        var: typed_ir::TypeVar,
        ty: typed_ir::Type,
        cast_order: &TypeCastOrder,
    ) -> MonomorphizeResult<bool> {
        push_bound(&mut self.upper, var, ty, BoundSide::Upper, cast_order)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GraphSolution {
    pub type_vars: Vec<ResolvedTypeVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedTypeVar {
    pub var: typed_ir::TypeVar,
    pub bounds: TypeVarBounds,
    pub solution: Option<typed_ir::Type>,
}

impl GraphSolution {
    pub fn is_complete(&self) -> bool {
        self.type_vars.iter().all(|var| var.solution.is_some())
    }

    pub fn substitutions(&self) -> Vec<typed_ir::TypeSubstitution> {
        self.type_vars
            .iter()
            .filter_map(|var| {
                var.solution.clone().map(|ty| typed_ir::TypeSubstitution {
                    var: var.var.clone(),
                    ty,
                })
            })
            .collect()
    }

    pub fn solution_for(&self, var: &typed_ir::TypeVar) -> Option<&typed_ir::Type> {
        self.type_vars
            .iter()
            .find(|resolved| &resolved.var == var)
            .and_then(|resolved| resolved.solution.as_ref())
    }

    pub fn materialize_core(&self, ty: typed_ir::Type) -> typed_ir::Type {
        materialize_type(ty, &self.substitutions())
    }
}

pub fn materialize_core_type(
    ty: typed_ir::Type,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::Type {
    normalize_bound_form(&materialize_type(ty, substitutions))
}

pub fn materialize_runtime_type(
    ty: RuntimeType,
    substitutions: &[typed_ir::TypeSubstitution],
) -> RuntimeType {
    match ty {
        RuntimeType::Unknown => RuntimeType::Unknown,
        RuntimeType::Value(ty) => {
            runtime_type_from_core_value(normalize_bound_form(&materialize_type(ty, substitutions)))
        }
        RuntimeType::Fun { param, ret } => RuntimeType::Fun {
            param: Box::new(materialize_runtime_type(*param, substitutions)),
            ret: Box::new(materialize_runtime_type(*ret, substitutions)),
        },
        RuntimeType::Thunk { effect, value } => RuntimeType::Thunk {
            effect: normalize_bound_form(&materialize_type(effect, substitutions)),
            value: Box::new(materialize_runtime_type(*value, substitutions)),
        },
    }
}

pub(crate) fn normalize_runtime_type(ty: RuntimeType) -> RuntimeType {
    match ty {
        RuntimeType::Unknown => RuntimeType::Unknown,
        RuntimeType::Value(ty) => runtime_type_from_core_value(normalize_bound_form(&ty)),
        RuntimeType::Fun { param, ret } => RuntimeType::Fun {
            param: Box::new(normalize_runtime_type(*param)),
            ret: Box::new(normalize_runtime_type(*ret)),
        },
        RuntimeType::Thunk { effect, value } => RuntimeType::Thunk {
            effect: normalize_bound_form(&effect),
            value: Box::new(normalize_runtime_type(*value)),
        },
    }
}

/// Convert a fully materialized typed_ir value type into a VM-shaped runtime
/// type. Functions become `RuntimeType::Fun` with each side wrapped in
/// `Thunk` when its effect row is non-empty, so the VM's `expects_thunk_arg`
/// check sees the right shape on every callee position.
pub(crate) fn runtime_type_from_core_value(ty: typed_ir::Type) -> RuntimeType {
    match ty {
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => RuntimeType::Fun {
            param: Box::new(runtime_type_from_core_value_and_effect(
                *param,
                *param_effect,
            )),
            ret: Box::new(runtime_type_from_core_value_and_effect(*ret, *ret_effect)),
        },
        ty => RuntimeType::Value(ty),
    }
}

pub(crate) fn runtime_type_from_core_value_and_effect(
    value: typed_ir::Type,
    effect: typed_ir::Type,
) -> RuntimeType {
    let value = runtime_type_from_core_value(value);
    if should_thunk_effect(&effect) {
        RuntimeType::Thunk {
            effect,
            value: Box::new(value),
        }
    } else {
        value
    }
}

pub(crate) fn should_thunk_effect(effect: &typed_ir::Type) -> bool {
    !effect_is_empty(effect) && !matches!(effect, typed_ir::Type::Unknown)
}

pub(crate) fn effect_is_empty(effect: &typed_ir::Type) -> bool {
    match effect {
        typed_ir::Type::Never => true,
        typed_ir::Type::Row { items, tail } => items.is_empty() && effect_is_empty(tail),
        typed_ir::Type::Recursive { body, .. } => effect_is_empty(body),
        _ => false,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundSide {
    Lower,
    Upper,
}

impl BoundSide {
    fn flip(self) -> Self {
        match self {
            Self::Lower => Self::Upper,
            Self::Upper => Self::Lower,
        }
    }
}

struct RuntimeEffectedType<'a> {
    value: &'a RuntimeType,
    effect: RuntimeEffectRef<'a>,
}

#[derive(Clone, Copy)]
enum RuntimeEffectRef<'a> {
    Known(&'a typed_ir::Type),
    Pure,
    Unknown,
}

fn runtime_value_is_top(ty: &RuntimeType) -> bool {
    matches!(ty, RuntimeType::Value(typed_ir::Type::Any))
}

fn split_runtime_effected_type(ty: &RuntimeType) -> RuntimeEffectedType<'_> {
    match ty {
        RuntimeType::Thunk { effect, value } => RuntimeEffectedType {
            value,
            effect: RuntimeEffectRef::Known(effect),
        },
        RuntimeType::Unknown => RuntimeEffectedType {
            value: ty,
            effect: RuntimeEffectRef::Unknown,
        },
        RuntimeType::Value(_) | RuntimeType::Fun { .. } => RuntimeEffectedType {
            value: ty,
            effect: RuntimeEffectRef::Pure,
        },
    }
}

/// Effect-row lattice merge for type-var bounds.
///
/// Both inputs must be closed-tail row-shaped types (Row with Never tail, or
/// `Never`, or a single effect Named — which is treated as a one-item row).
/// `Lower` bounds get item **union** (a var observed with two lower bounds
/// must allow at least both rows' items). `Upper` bounds get item
/// **intersection** (a var bounded above by two rows can use at most what
/// both rows allow).
///
/// Returns `None` when the types are not row-shaped, when either tail is
/// open (a `Var` or other unsolved tail), or when intersection on an upper
/// would yield an empty row that disagrees with prior structure.
///
/// We intentionally do not flatten `Inter` tails or recurse through unbounded
/// row-of-row structures — that was the stack-overflow path in the previous
/// experimental layer.
fn merge_row_bounds(
    previous: &typed_ir::Type,
    ty: &typed_ir::Type,
    side: BoundSide,
) -> Option<typed_ir::Type> {
    // Require at least one side to be a genuine row-shaped type (Row / Never)
    // so we don't accidentally treat two value-type Named bounds as a row
    // union just because the bare Named could *look* like a one-item row.
    if !is_row_shaped(previous) && !is_row_shaped(ty) {
        return None;
    }
    let (mut prev_items, prev_tail) = flatten_closed_row_or_atom(previous)?;
    let (ty_items, ty_tail) = flatten_closed_row_or_atom(ty)?;
    let merged_tail = merge_row_tails(&prev_tail, &ty_tail, side)?;
    let merged_items = match side {
        BoundSide::Lower => {
            for item in ty_items {
                push_unique_effect_item(&mut prev_items, item);
            }
            prev_items
        }
        BoundSide::Upper => {
            let mut out = Vec::new();
            for item in &prev_items {
                if ty_items.iter().any(|other| effect_items_match(item, other)) {
                    push_unique_effect_item(&mut out, item.clone());
                }
            }
            out
        }
    };
    Some(typed_ir::Type::Row {
        items: merged_items,
        tail: Box::new(merged_tail),
    })
}

fn merge_row_tails(
    previous: &typed_ir::Type,
    ty: &typed_ir::Type,
    side: BoundSide,
) -> Option<typed_ir::Type> {
    match (side, previous, ty) {
        (_, typed_ir::Type::Never, typed_ir::Type::Never) => Some(typed_ir::Type::Never),
        (_, typed_ir::Type::Any, typed_ir::Type::Any) => Some(typed_ir::Type::Any),
        (BoundSide::Lower, typed_ir::Type::Any, typed_ir::Type::Never)
        | (BoundSide::Lower, typed_ir::Type::Never, typed_ir::Type::Any) => {
            Some(typed_ir::Type::Any)
        }
        (BoundSide::Upper, typed_ir::Type::Any, typed_ir::Type::Never)
        | (BoundSide::Upper, typed_ir::Type::Never, typed_ir::Type::Any) => {
            Some(typed_ir::Type::Never)
        }
        _ => None,
    }
}

fn is_row_shaped(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Row { .. } | typed_ir::Type::Never)
}

/// Like `flatten_closed_row` but additionally promotes a bare `Type::Named`
/// to a singleton row. Only safe to call from `merge_row_bounds`, which
/// gates the promotion behind the requirement that *at least one* of the
/// two bounds being merged is genuinely row-shaped — otherwise we would
/// risk treating a pair of value-type Named bounds as rows.
fn flatten_closed_row_or_atom(
    ty: &typed_ir::Type,
) -> Option<(Vec<typed_ir::Type>, typed_ir::Type)> {
    match ty {
        typed_ir::Type::Named { .. } => Some((vec![ty.clone()], typed_ir::Type::Never)),
        _ => flatten_closed_row(ty),
    }
}

/// Flatten a row-shaped type into `(items, tail)`. Descends through nested
/// `Row` tails linearly. Also collapses an `Inter` tail when every branch
/// flattens to the same `(items, tail)`, which is the degenerate case the
/// constraint solver leaves behind when an intersection target turns out to
/// be redundant. Returns `None` for genuinely open tails (`Var`, `Any`,
/// non-degenerate `Inter`).
///
/// IMPORTANT: only `Type::Row` and `Type::Never` are recognized as rows here.
/// A bare `Type::Named` is *not* treated as a degenerate one-item row,
/// because the same shape is also used in value position (e.g.
/// `std::var::ref<..>`) and treating those as rows would let `push_bound`
/// silently fold value types into row unions and explode the constraint
/// loop.
fn flatten_closed_row(ty: &typed_ir::Type) -> Option<(Vec<typed_ir::Type>, typed_ir::Type)> {
    match ty {
        typed_ir::Type::Never => Some((Vec::new(), typed_ir::Type::Never)),
        typed_ir::Type::Row { items, tail } => {
            let mut out: Vec<typed_ir::Type> = Vec::new();
            for item in items {
                push_unique_effect_item(&mut out, item.clone());
            }
            let mut current_tail: typed_ir::Type = (**tail).clone();
            let mut depth = 0usize;
            loop {
                if depth >= 64 {
                    return None;
                }
                depth += 1;
                match current_tail {
                    typed_ir::Type::Row {
                        items: tail_items,
                        tail: next_tail,
                    } => {
                        for item in tail_items {
                            push_unique_effect_item(&mut out, item);
                        }
                        current_tail = *next_tail;
                    }
                    typed_ir::Type::Inter(branches) => {
                        let collapsed = collapse_equivalent_inter(&branches)?;
                        current_tail = collapsed;
                    }
                    typed_ir::Type::Never => return Some((out, typed_ir::Type::Never)),
                    other => return Some((out, other)),
                }
            }
        }
        _ => None,
    }
}

/// If every branch of an `Inter` flattens to the same closed row, return
/// that single row. Otherwise return `None`. This catches the redundant
/// `Inter([Row[..], Row[..]])` shapes that fall out of subtype propagation
/// without committing us to a full intersection lattice.
fn collapse_equivalent_inter(branches: &[typed_ir::Type]) -> Option<typed_ir::Type> {
    let (first, rest) = branches.split_first()?;
    let (first_items, first_tail) = flatten_closed_row(first)?;
    for branch in rest {
        let (branch_items, branch_tail) = flatten_closed_row(branch)?;
        if !rows_equivalent(&first_items, &first_tail, &branch_items, &branch_tail) {
            return None;
        }
    }
    Some(typed_ir::Type::Row {
        items: first_items,
        tail: Box::new(first_tail),
    })
}

fn intersect_closed_rows(branches: &[typed_ir::Type]) -> Option<typed_ir::Type> {
    let (first, rest) = branches.split_first()?;
    let (mut items, mut tail) = flatten_closed_row(first)?;
    for branch in rest {
        let (branch_items, branch_tail) = flatten_closed_row(branch)?;
        let mut intersection = Vec::new();
        for item in &items {
            if branch_items
                .iter()
                .any(|other| effect_items_match(item, other))
            {
                push_unique_effect_item(&mut intersection, item.clone());
            }
        }
        items = intersection;
        tail = merge_row_tails(&tail, &branch_tail, BoundSide::Upper)?;
    }
    Some(typed_ir::Type::Row {
        items,
        tail: Box::new(tail),
    })
}

fn rows_equivalent(
    a_items: &[typed_ir::Type],
    a_tail: &typed_ir::Type,
    b_items: &[typed_ir::Type],
    b_tail: &typed_ir::Type,
) -> bool {
    if a_items.len() != b_items.len() {
        return false;
    }
    if !a_items
        .iter()
        .all(|item| b_items.iter().any(|other| effect_items_match(item, other)))
    {
        return false;
    }
    a_tail == b_tail
        || normalize_bound_form_inner(a_tail, true) == normalize_bound_form_inner(b_tail, true)
}

fn push_unique_effect_item(items: &mut Vec<typed_ir::Type>, item: typed_ir::Type) {
    if let typed_ir::Type::Row {
        items: row_items,
        tail,
    } = item
    {
        if matches!(tail.as_ref(), typed_ir::Type::Never) {
            for item in row_items {
                push_unique_effect_item(items, item);
            }
            return;
        }
        let item = typed_ir::Type::Row {
            items: row_items,
            tail,
        };
        push_unique_non_row_effect_item(items, item);
        return;
    }
    push_unique_non_row_effect_item(items, item);
}

fn push_unique_non_row_effect_item(items: &mut Vec<typed_ir::Type>, item: typed_ir::Type) {
    if matches!(item, typed_ir::Type::Never) {
        return;
    }
    if items
        .iter()
        .any(|existing| effect_items_match(existing, &item))
    {
        return;
    }
    items.push(item);
}

fn effect_items_match(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    left == right
        || normalize_bound_form_inner(left, true) == normalize_bound_form_inner(right, true)
}

fn push_bound(
    slot: &mut Option<typed_ir::Type>,
    var: typed_ir::TypeVar,
    ty: typed_ir::Type,
    side: BoundSide,
    cast_order: &TypeCastOrder,
) -> MonomorphizeResult<bool> {
    if let Some(previous) = slot {
        if bounds_are_equivalent(previous, &ty) {
            return Ok(false);
        }
        if let Some(merged) = merge_unknown_bounds(previous, &ty) {
            if bounds_are_equivalent(previous, &merged) {
                return Ok(false);
            }
            *previous = merged;
            return Ok(true);
        }
        if let Some(merged) = merge_row_bounds(previous, &ty, side) {
            if bounds_are_equivalent(previous, &merged) {
                return Ok(false);
            }
            *previous = merged;
            return Ok(true);
        }
        if let Some(merged) = merge_ordered_bounds(previous, &ty, side, cast_order) {
            if bounds_are_equivalent(previous, &merged) {
                return Ok(false);
            }
            *previous = merged;
            return Ok(true);
        }
        if matches!(
            (&*previous, &ty),
            (typed_ir::Type::Var(_), typed_ir::Type::Var(_))
        ) {
            return Ok(false);
        }
        if matches!(ty, typed_ir::Type::Var(_)) && !matches!(previous, typed_ir::Type::Var(_)) {
            return Ok(false);
        }
        if matches!(previous, typed_ir::Type::Var(_)) && !matches!(ty, typed_ir::Type::Var(_)) {
            *previous = ty;
            return Ok(true);
        }
        if type_contains_var(previous) || type_contains_var(&ty) {
            return Ok(false);
        }
        return Err(MonomorphizeDiagnostic::ConflictingBounds {
            var,
            previous: previous.clone(),
            next: ty,
        });
    }
    *slot = Some(ty);
    Ok(true)
}

fn reject_invalid_top_bottom_bounds(
    var: &typed_ir::TypeVar,
    bounds: &TypeVarBounds,
) -> MonomorphizeResult<()> {
    let (Some(lower), Some(upper)) = (&bounds.lower, &bounds.upper) else {
        return Ok(());
    };
    if matches!(lower, typed_ir::Type::Any)
        && !matches!(upper, typed_ir::Type::Any | typed_ir::Type::Never)
    {
        return Err(MonomorphizeDiagnostic::ConflictingBounds {
            var: var.clone(),
            previous: lower.clone(),
            next: upper.clone(),
        });
    }
    Ok(())
}

fn merge_ordered_bounds(
    previous: &typed_ir::Type,
    ty: &typed_ir::Type,
    side: BoundSide,
    cast_order: &TypeCastOrder,
) -> Option<typed_ir::Type> {
    match side {
        BoundSide::Lower
            if matches!(previous, typed_ir::Type::Any) || matches!(ty, typed_ir::Type::Any) =>
        {
            Some(typed_ir::Type::Any)
        }
        BoundSide::Lower if bound_subtype(previous, ty) => Some(ty.clone()),
        BoundSide::Lower if bound_subtype(ty, previous) => Some(previous.clone()),
        BoundSide::Lower if union_supertype_contains(previous, ty) => Some(previous.clone()),
        BoundSide::Lower if union_supertype_contains(ty, previous) => Some(ty.clone()),
        BoundSide::Lower => {
            merge_lower_union_bound(previous, ty).or_else(|| cast_order.join_lower(previous, ty))
        }
        BoundSide::Upper
            if matches!(previous, typed_ir::Type::Never) || matches!(ty, typed_ir::Type::Never) =>
        {
            Some(typed_ir::Type::Never)
        }
        BoundSide::Upper if bound_subtype(previous, ty) => Some(previous.clone()),
        BoundSide::Upper if bound_subtype(ty, previous) => Some(ty.clone()),
        BoundSide::Upper => cast_order.meet_upper(previous, ty),
    }
}

fn merge_lower_union_bound(
    previous: &typed_ir::Type,
    ty: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    if !matches!(previous, typed_ir::Type::Union(_)) && !matches!(ty, typed_ir::Type::Union(_)) {
        return None;
    }
    let mut items = Vec::new();
    append_lower_union_items(&mut items, previous);
    append_lower_union_items(&mut items, ty);
    Some(normalize_bound_form(&typed_ir::Type::Union(items)))
}

fn append_lower_union_items(items: &mut Vec<typed_ir::Type>, ty: &typed_ir::Type) {
    match ty {
        typed_ir::Type::Union(branches) => {
            for branch in branches {
                push_lower_union_item(items, branch.clone());
            }
        }
        ty => push_lower_union_item(items, ty.clone()),
    }
}

fn push_lower_union_item(items: &mut Vec<typed_ir::Type>, item: typed_ir::Type) {
    if items
        .iter()
        .any(|existing| bounds_are_equivalent(existing, &item))
    {
        return;
    }
    items.push(item);
}

fn bound_subtype(sub: &typed_ir::Type, sup: &typed_ir::Type) -> bool {
    if lightweight_bounds_equivalent(sub, sup)
        || matches!(sub, typed_ir::Type::Never)
        || matches!(sup, typed_ir::Type::Any)
        || closed_singleton_row_item(sub).is_some_and(|item| bound_subtype(item, sup))
        || closed_singleton_row_item(sup).is_some_and(|item| bound_subtype(sub, item))
        || function_bound_subtype(sub, sup)
        || row_bound_subtype(sub, sup)
        || union_supertype_contains(sup, sub)
    {
        return true;
    }
    match (sub, sup) {
        (typed_ir::Type::Union(items), _) => items.iter().all(|item| bound_subtype(item, sup)),
        (_, typed_ir::Type::Union(items)) => items.iter().any(|item| bound_subtype(sub, item)),
        (typed_ir::Type::Inter(items), _) => items.iter().any(|item| bound_subtype(item, sup)),
        (_, typed_ir::Type::Inter(items)) => items.iter().all(|item| bound_subtype(sub, item)),
        (
            typed_ir::Type::Named { path: sub_path, .. },
            typed_ir::Type::Named {
                path: sup_path,
                args: sup_args,
            },
        ) if same_erased_synthetic_effect_atom_path(sub_path, sup_path) && sup_args.is_empty() => {
            true
        }
        (
            typed_ir::Type::Named {
                path: sub_path,
                args: sub_args,
            },
            typed_ir::Type::Named {
                path: sup_path,
                args: sup_args,
            },
        ) if sub_path == sup_path && sub_args.len() == sup_args.len() => sub_args
            .iter()
            .zip(sup_args)
            .all(|(sub, sup)| type_arg_bound_subtype(sub, sup)),
        (typed_ir::Type::Recursive { var, body }, _) if !type_body_mentions_var(body, var) => {
            bound_subtype(&normalize_bound_form(body), sup)
        }
        (_, typed_ir::Type::Recursive { var, body }) if !type_body_mentions_var(body, var) => {
            bound_subtype(sub, &normalize_bound_form(body))
        }
        _ => false,
    }
}

fn type_arg_bound_subtype(sub: &typed_ir::TypeArg, sup: &typed_ir::TypeArg) -> bool {
    match (sub, sup) {
        (typed_ir::TypeArg::Type(sub), typed_ir::TypeArg::Type(sup)) => bound_subtype(sub, sup),
        (typed_ir::TypeArg::Type(sub), typed_ir::TypeArg::Bounds(sup)) => {
            lower_bound_accepts_type(sup.lower.as_deref(), sub)
                && upper_bound_accepts_type(sup.upper.as_deref(), sub)
        }
        (typed_ir::TypeArg::Bounds(sub), typed_ir::TypeArg::Type(sup)) => {
            sub.lower
                .as_deref()
                .is_some_and(|lower| bound_subtype(lower, sup))
                || sub
                    .upper
                    .as_deref()
                    .is_some_and(|upper| bound_subtype(upper, sup))
        }
        (typed_ir::TypeArg::Bounds(sub), typed_ir::TypeArg::Bounds(sup)) => {
            lower_bound_accepts_bound(sup.lower.as_deref(), sub.lower.as_deref())
                && upper_bound_accepts_bound(sup.upper.as_deref(), sub.upper.as_deref())
        }
    }
}

fn lower_bound_accepts_type(lower: Option<&typed_ir::Type>, ty: &typed_ir::Type) -> bool {
    lower.is_none_or(|lower| bound_subtype(lower, ty))
}

fn upper_bound_accepts_type(upper: Option<&typed_ir::Type>, ty: &typed_ir::Type) -> bool {
    upper.is_none_or(|upper| bound_subtype(ty, upper))
}

fn lower_bound_accepts_bound(
    sup_lower: Option<&typed_ir::Type>,
    sub_lower: Option<&typed_ir::Type>,
) -> bool {
    match (sup_lower, sub_lower) {
        (None, _) => true,
        (Some(sup), Some(sub)) => bound_subtype(sup, sub),
        (Some(_), None) => false,
    }
}

fn upper_bound_accepts_bound(
    sup_upper: Option<&typed_ir::Type>,
    sub_upper: Option<&typed_ir::Type>,
) -> bool {
    match (sup_upper, sub_upper) {
        (None, _) => true,
        (Some(sup), Some(sub)) => bound_subtype(sub, sup),
        (Some(_), None) => false,
    }
}

fn function_bound_subtype(sub: &typed_ir::Type, sup: &typed_ir::Type) -> bool {
    let (
        typed_ir::Type::Fun {
            param: sub_param,
            param_effect: sub_param_effect,
            ret_effect: sub_ret_effect,
            ret: sub_ret,
        },
        typed_ir::Type::Fun {
            param: sup_param,
            param_effect: sup_param_effect,
            ret_effect: sup_ret_effect,
            ret: sup_ret,
        },
    ) = (sub, sup)
    else {
        return false;
    };
    bound_subtype(sup_param, sub_param)
        && bound_subtype(sub_param_effect, sup_param_effect)
        && bound_subtype(sub_ret_effect, sup_ret_effect)
        && bound_subtype(sub_ret, sup_ret)
}

fn union_supertype_contains(sup: &typed_ir::Type, sub: &typed_ir::Type) -> bool {
    let typed_ir::Type::Union(items) = sup else {
        return false;
    };
    items.iter().any(|item| {
        !matches!(item, typed_ir::Type::Union(_))
            && (lightweight_bounds_equivalent(sub, item) || bound_subtype(sub, item))
    })
}

fn row_bound_subtype(sub: &typed_ir::Type, sup: &typed_ir::Type) -> bool {
    let Some((sub_items, sub_tail)) = flatten_closed_row(sub) else {
        return false;
    };
    let Some((sup_items, sup_tail)) = flatten_closed_row(sup) else {
        return false;
    };
    let residual = split_row_items(&sub_items, &sup_items);
    let items_covered =
        residual.unmatched_left.is_empty() || matches!(sup_tail, typed_ir::Type::Any);
    items_covered && row_tail_subtype(&sub_tail, &sup_tail)
}

fn row_tail_subtype(sub: &typed_ir::Type, sup: &typed_ir::Type) -> bool {
    sub == sup || matches!(sub, typed_ir::Type::Never) || matches!(sup, typed_ir::Type::Any)
}

fn lightweight_bounds_equivalent(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    left == right || core_type_is_unit_value(left) && core_type_is_unit_value(right)
}

fn merge_unknown_bounds(previous: &typed_ir::Type, ty: &typed_ir::Type) -> Option<typed_ir::Type> {
    if !type_contains_unknown(previous) && !type_contains_unknown(ty) {
        return None;
    }
    merge_unknown_bounds_inner(previous, ty)
}

fn merge_unknown_bounds_inner(
    previous: &typed_ir::Type,
    ty: &typed_ir::Type,
) -> Option<typed_ir::Type> {
    match (previous, ty) {
        (typed_ir::Type::Unknown, _) => Some(ty.clone()),
        (_, typed_ir::Type::Unknown) => Some(previous.clone()),
        (
            typed_ir::Type::Named {
                path: previous_path,
                args: previous_args,
            },
            typed_ir::Type::Named { path, args },
        ) if previous_path == path && previous_args.len() == args.len() => {
            Some(typed_ir::Type::Named {
                path: path.clone(),
                args: previous_args
                    .iter()
                    .zip(args)
                    .map(|(previous, arg)| merge_unknown_type_arg_bounds(previous, arg))
                    .collect::<Option<Vec<_>>>()?,
            })
        }
        (
            typed_ir::Type::Fun {
                param: previous_param,
                param_effect: previous_param_effect,
                ret_effect: previous_ret_effect,
                ret: previous_ret,
            },
            typed_ir::Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
        ) => Some(typed_ir::Type::Fun {
            param: Box::new(merge_unknown_bounds_inner(previous_param, param)?),
            param_effect: Box::new(merge_unknown_bounds_inner(
                previous_param_effect,
                param_effect,
            )?),
            ret_effect: Box::new(merge_unknown_bounds_inner(previous_ret_effect, ret_effect)?),
            ret: Box::new(merge_unknown_bounds_inner(previous_ret, ret)?),
        }),
        (typed_ir::Type::Tuple(previous), typed_ir::Type::Tuple(items))
            if previous.len() == items.len() =>
        {
            Some(typed_ir::Type::Tuple(
                previous
                    .iter()
                    .zip(items)
                    .map(|(previous, item)| merge_unknown_bounds_inner(previous, item))
                    .collect::<Option<Vec<_>>>()?,
            ))
        }
        (
            typed_ir::Type::Row {
                items: previous_items,
                tail: previous_tail,
            },
            typed_ir::Type::Row { items, tail },
        ) if previous_items.len() == items.len() => Some(typed_ir::Type::Row {
            items: previous_items
                .iter()
                .zip(items)
                .map(|(previous, item)| merge_unknown_bounds_inner(previous, item))
                .collect::<Option<Vec<_>>>()?,
            tail: Box::new(merge_unknown_bounds_inner(previous_tail, tail)?),
        }),
        _ if previous == ty => Some(previous.clone()),
        _ => None,
    }
}

fn merge_unknown_type_arg_bounds(
    previous: &typed_ir::TypeArg,
    arg: &typed_ir::TypeArg,
) -> Option<typed_ir::TypeArg> {
    match (previous, arg) {
        (typed_ir::TypeArg::Type(previous), typed_ir::TypeArg::Type(arg)) => Some(
            typed_ir::TypeArg::Type(merge_unknown_bounds_inner(previous, arg)?),
        ),
        (typed_ir::TypeArg::Bounds(previous), typed_ir::TypeArg::Bounds(arg)) => {
            Some(typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                lower: merge_optional_unknown_bound(
                    previous.lower.as_deref(),
                    arg.lower.as_deref(),
                )?,
                upper: merge_optional_unknown_bound(
                    previous.upper.as_deref(),
                    arg.upper.as_deref(),
                )?,
            }))
        }
        _ => None,
    }
}

fn merge_optional_unknown_bound(
    previous: Option<&typed_ir::Type>,
    ty: Option<&typed_ir::Type>,
) -> Option<Option<Box<typed_ir::Type>>> {
    match (previous, ty) {
        (Some(previous), Some(ty)) => {
            Some(Some(Box::new(merge_unknown_bounds_inner(previous, ty)?)))
        }
        (Some(previous), None) => Some(Some(Box::new(previous.clone()))),
        (None, Some(ty)) => Some(Some(Box::new(ty.clone()))),
        (None, None) => Some(None),
    }
}

fn type_contains_var(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Var(_) => true,
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_contains_var(param)
                || type_contains_var(param_effect)
                || type_contains_var(ret_effect)
                || type_contains_var(ret)
        }
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_var),
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(type_contains_var),
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_contains_var) || type_contains_var(tail)
        }
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_contains_var(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_contains_var(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_contains_var))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| type_contains_var(tail))
        }
        typed_ir::Type::Recursive { body, .. } => type_contains_var(body),
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => false,
    }
}

fn type_arg_contains_var(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_contains_var(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_some_and(|ty| type_contains_var(ty))
                || bounds
                    .upper
                    .as_ref()
                    .is_some_and(|ty| type_contains_var(ty))
        }
    }
}

fn type_body_mentions_var(ty: &typed_ir::Type, target: &typed_ir::TypeVar) -> bool {
    match ty {
        typed_ir::Type::Var(var) => var == target,
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_body_mentions_var(param, target)
                || type_body_mentions_var(param_effect, target)
                || type_body_mentions_var(ret_effect, target)
                || type_body_mentions_var(ret, target)
        }
        typed_ir::Type::Named { args, .. } => args
            .iter()
            .any(|arg| type_arg_body_mentions_var(arg, target)),
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items
            .iter()
            .any(|item| type_body_mentions_var(item, target)),
        typed_ir::Type::Row { items, tail } => {
            items
                .iter()
                .any(|item| type_body_mentions_var(item, target))
                || type_body_mentions_var(tail, target)
        }
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_body_mentions_var(&field.value, target))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_body_mentions_var(ty, target)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(|ty| type_body_mentions_var(ty, target))
            }) || variant
                .tail
                .as_ref()
                .is_some_and(|tail| type_body_mentions_var(tail, target))
        }
        typed_ir::Type::Recursive { body, .. } => type_body_mentions_var(body, target),
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => false,
    }
}

fn type_arg_body_mentions_var(arg: &typed_ir::TypeArg, target: &typed_ir::TypeVar) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_body_mentions_var(ty, target),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_some_and(|ty| type_body_mentions_var(ty, target))
                || bounds
                    .upper
                    .as_ref()
                    .is_some_and(|ty| type_body_mentions_var(ty, target))
        }
    }
}

fn bounds_are_equivalent(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    left == right
        || core_type_is_unit_value(left) && core_type_is_unit_value(right)
        || closed_singleton_row_item(left).is_some_and(|item| item == right)
        || closed_singleton_row_item(right).is_some_and(|item| item == left)
        || normalize_bound_form(left) == normalize_bound_form(right)
}

fn core_type_is_unit_value(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Tuple(items) => items.is_empty(),
        typed_ir::Type::Named { path, args } => {
            args.is_empty()
                && path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.0 == "unit")
        }
        _ => false,
    }
}

pub(crate) fn normalize_bound_form(ty: &typed_ir::Type) -> typed_ir::Type {
    normalize_bound_form_inner(ty, false)
}

fn normalize_bound_form_inner(ty: &typed_ir::Type, effect_atom: bool) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: if effect_atom && args.iter().any(type_arg_contains_unknown) {
                Vec::new()
            } else {
                args.iter()
                    .map(|arg| normalize_bound_arg_form(arg, effect_atom))
                    .collect()
            },
        },
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(normalize_bound_form_inner(param, false)),
            param_effect: Box::new(normalize_bound_form_inner(param_effect, false)),
            ret_effect: Box::new(normalize_bound_form_inner(ret_effect, false)),
            ret: Box::new(normalize_bound_form_inner(ret, false)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| normalize_bound_form_inner(item, false))
                .collect(),
        ),
        typed_ir::Type::Union(items) => {
            let mut normalized = Vec::new();
            for item in items
                .iter()
                .map(|item| normalize_bound_form_inner(item, false))
            {
                if matches!(item, typed_ir::Type::Any) {
                    return typed_ir::Type::Any;
                }
                if matches!(item, typed_ir::Type::Never) {
                    continue;
                }
                match item {
                    typed_ir::Type::Union(items) => {
                        for item in items {
                            push_normalized_union_item(&mut normalized, item);
                        }
                    }
                    item => {
                        push_normalized_union_item(&mut normalized, item);
                    }
                }
            }
            match normalized.len() {
                0 => typed_ir::Type::Never,
                1 => normalized.pop().unwrap(),
                _ => typed_ir::Type::Union(normalized),
            }
        }
        typed_ir::Type::Inter(items) => {
            let mut normalized = Vec::new();
            for item in items
                .iter()
                .map(|item| normalize_bound_form_inner(item, false))
            {
                if matches!(item, typed_ir::Type::Any) {
                    continue;
                }
                if matches!(item, typed_ir::Type::Never) {
                    return typed_ir::Type::Never;
                }
                match item {
                    typed_ir::Type::Inter(items) => {
                        for item in items {
                            push_normalized_inter_item(&mut normalized, item);
                        }
                    }
                    item => {
                        push_normalized_inter_item(&mut normalized, item);
                    }
                }
            }
            if let Some(row) = intersect_closed_rows(&normalized) {
                return row;
            }
            match normalized.len() {
                0 => typed_ir::Type::Any,
                1 => normalized.pop().unwrap(),
                _ => typed_ir::Type::Inter(normalized),
            }
        }
        typed_ir::Type::Row { items, tail } => {
            // Flatten nested rows that share a `Never` tail so that
            // `Row<[next], Row<[last]; Never>>` collapses to the flat
            // `Row<[next, last]; Never>` form before we normalize items.
            let (raw_items, raw_tail) = match flatten_closed_row(ty) {
                Some(flat) => flat,
                None => (items.clone(), (**tail).clone()),
            };
            let mut normalized_items = Vec::new();
            for item in raw_items
                .into_iter()
                .map(|item| normalize_bound_form_inner(&item, true))
            {
                push_unique_effect_item(&mut normalized_items, item);
            }
            // Effect rows are unordered sets; canonicalize item order so
            // `[next, last]` and `[last, next]` compare equal across bound merges.
            normalized_items.sort_by_key(|item| format!("{item:?}"));
            let tail = normalize_bound_form_inner(&raw_tail, false);
            if normalized_items.is_empty() {
                tail
            } else {
                typed_ir::Type::Row {
                    items: normalized_items,
                    tail: Box::new(tail),
                }
            }
        }
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name.clone(),
                    value: normalize_bound_form_inner(&field.value, false),
                    optional: field.optional,
                })
                .collect(),
            spread: record.spread.as_ref().map(|spread| match spread {
                typed_ir::RecordSpread::Head(ty) => {
                    typed_ir::RecordSpread::Head(Box::new(normalize_bound_form_inner(ty, false)))
                }
                typed_ir::RecordSpread::Tail(ty) => {
                    typed_ir::RecordSpread::Tail(Box::new(normalize_bound_form_inner(ty, false)))
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
                        .map(|payload| normalize_bound_form_inner(payload, false))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(normalize_bound_form_inner(tail, false))),
        }),
        typed_ir::Type::Recursive { var, body }
            if effect_atom && !type_body_mentions_var(body, var) =>
        {
            normalize_bound_form_inner(body, effect_atom)
        }
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(normalize_bound_form_inner(body, effect_atom)),
        },
        typed_ir::Type::Var(_)
        | typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any => ty.clone(),
    }
}

fn normalize_bound_arg_form(arg: &typed_ir::TypeArg, effect_atom: bool) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            typed_ir::TypeArg::Type(normalize_bound_form_inner(ty, effect_atom))
        }
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds
                .lower
                .as_deref()
                .filter(|lower| !matches!(lower, typed_ir::Type::Never))
            {
                return typed_ir::TypeArg::Type(normalize_bound_form_inner(lower, effect_atom));
            }
            if let Some(upper) = bounds
                .upper
                .as_deref()
                .filter(|upper| !matches!(upper, typed_ir::Type::Any))
            {
                return typed_ir::TypeArg::Type(normalize_bound_form_inner(upper, effect_atom));
            }
            typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                lower: bounds
                    .lower
                    .as_ref()
                    .map(|lower| Box::new(normalize_bound_form_inner(lower, effect_atom))),
                upper: bounds
                    .upper
                    .as_ref()
                    .map(|upper| Box::new(normalize_bound_form_inner(upper, effect_atom))),
            })
        }
    }
}

fn push_normalized_union_item(items: &mut Vec<typed_ir::Type>, item: typed_ir::Type) {
    if matches!(item, typed_ir::Type::Never) {
        return;
    }
    if matches!(item, typed_ir::Type::Any) {
        items.clear();
        items.push(item);
        return;
    }
    if items
        .iter()
        .any(|existing| absorption_subtype(&item, existing))
    {
        return;
    }
    items.retain(|existing| !absorption_subtype(existing, &item));
    items.push(item);
}

fn push_normalized_inter_item(items: &mut Vec<typed_ir::Type>, item: typed_ir::Type) {
    if matches!(item, typed_ir::Type::Any) {
        return;
    }
    if matches!(item, typed_ir::Type::Never) {
        items.clear();
        items.push(item);
        return;
    }
    if items
        .iter()
        .any(|existing| absorption_subtype(existing, &item))
    {
        return;
    }
    items.retain(|existing| !absorption_subtype(&item, existing));
    items.push(item);
}

fn absorption_subtype(sub: &typed_ir::Type, sup: &typed_ir::Type) -> bool {
    if lightweight_bounds_equivalent(sub, sup)
        || closed_singleton_row_item(sub).is_some_and(|item| item == sup)
        || closed_singleton_row_item(sup).is_some_and(|item| item == sub)
        || matches!(sub, typed_ir::Type::Never)
        || matches!(sup, typed_ir::Type::Any)
    {
        return true;
    }
    match (sub, sup) {
        (typed_ir::Type::Union(items), _) => items.iter().all(|item| absorption_subtype(item, sup)),
        (_, typed_ir::Type::Union(items)) => items.iter().any(|item| absorption_subtype(sub, item)),
        (typed_ir::Type::Inter(items), _) => items.iter().any(|item| absorption_subtype(item, sup)),
        (_, typed_ir::Type::Inter(items)) => items.iter().all(|item| absorption_subtype(sub, item)),
        (
            typed_ir::Type::Fun {
                param: sub_param,
                param_effect: sub_param_effect,
                ret_effect: sub_ret_effect,
                ret: sub_ret,
            },
            typed_ir::Type::Fun {
                param: sup_param,
                param_effect: sup_param_effect,
                ret_effect: sup_ret_effect,
                ret: sup_ret,
            },
        ) => {
            absorption_subtype(sup_param, sub_param)
                && absorption_subtype(sub_param_effect, sup_param_effect)
                && absorption_subtype(sub_ret_effect, sup_ret_effect)
                && absorption_subtype(sub_ret, sup_ret)
        }
        _ => row_bound_subtype(sub, sup),
    }
}

fn type_arg_contains_unknown(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => type_contains_unknown(ty),
        typed_ir::TypeArg::Bounds(bounds) => {
            bounds
                .lower
                .as_ref()
                .is_some_and(|ty| type_contains_unknown(ty))
                || bounds
                    .upper
                    .as_ref()
                    .is_some_and(|ty| type_contains_unknown(ty))
        }
    }
}

fn type_contains_unknown(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown => true,
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            type_contains_unknown(param)
                || type_contains_unknown(param_effect)
                || type_contains_unknown(ret_effect)
                || type_contains_unknown(ret)
        }
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_unknown),
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items.iter().any(type_contains_unknown),
        typed_ir::Type::Row { items, tail } => {
            items.iter().any(type_contains_unknown) || type_contains_unknown(tail)
        }
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| type_contains_unknown(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        type_contains_unknown(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant
                .cases
                .iter()
                .any(|case| case.payloads.iter().any(type_contains_unknown))
                || variant
                    .tail
                    .as_ref()
                    .is_some_and(|tail| type_contains_unknown(tail))
        }
        typed_ir::Type::Recursive { body, .. } => type_contains_unknown(body),
        typed_ir::Type::Var(_) | typed_ir::Type::Never | typed_ir::Type::Any => false,
    }
}

fn closed_singleton_row_item(ty: &typed_ir::Type) -> Option<&typed_ir::Type> {
    let typed_ir::Type::Row { items, tail } = ty else {
        return None;
    };
    if items.len() == 1 && matches!(tail.as_ref(), typed_ir::Type::Never) {
        items.first()
    } else {
        None
    }
}

fn is_vacuous_bound(ty: &typed_ir::Type, side: BoundSide) -> bool {
    matches!(
        (side, ty),
        (BoundSide::Lower, typed_ir::Type::Never) | (BoundSide::Upper, typed_ir::Type::Any)
    )
}

struct RowResidual<'a> {
    matched: Vec<(&'a typed_ir::Type, &'a typed_ir::Type)>,
    unmatched_left: Vec<typed_ir::Type>,
    unmatched_right: Vec<typed_ir::Type>,
}

fn collect_type_vars(ty: &typed_ir::Type, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Never | typed_ir::Type::Any => {}
        typed_ir::Type::Var(var) => {
            vars.insert(var.clone());
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_vars(arg, vars);
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_vars(param, vars);
            collect_type_vars(param_effect, vars);
            collect_type_vars(ret_effect, vars);
            collect_type_vars(ret, vars);
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_type_vars(item, vars);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_type_vars(&field.value, vars);
            }
            if let Some(spread) = &record.spread {
                collect_record_spread_vars(spread, vars);
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_vars(payload, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_vars(tail, vars);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_type_vars(item, vars);
            }
            collect_type_vars(tail, vars);
        }
        typed_ir::Type::Recursive { var, body } => {
            let inserted = vars.insert(var.clone());
            collect_type_vars(body, vars);
            if inserted {
                vars.remove(var);
            }
        }
    }
}

fn collect_type_arg_vars(arg: &typed_ir::TypeArg, vars: &mut BTreeSet<typed_ir::TypeVar>) {
    match arg {
        typed_ir::TypeArg::Type(ty) => collect_type_vars(ty, vars),
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_type_vars(lower, vars);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_type_vars(upper, vars);
            }
        }
    }
}

fn collect_record_spread_vars(
    spread: &typed_ir::RecordSpread,
    vars: &mut BTreeSet<typed_ir::TypeVar>,
) {
    match spread {
        typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
            collect_type_vars(ty, vars);
        }
    }
}

#[derive(Default)]
struct TypePositionVars {
    value: BTreeSet<typed_ir::TypeVar>,
    effect: BTreeSet<typed_ir::TypeVar>,
}

#[derive(Clone, Copy)]
enum TypePosition {
    Value,
    Effect,
}

fn collect_type_position_vars(
    ty: &typed_ir::Type,
    position: TypePosition,
    params: &BTreeSet<typed_ir::TypeVar>,
    vars: &mut TypePositionVars,
) {
    match ty {
        typed_ir::Type::Var(var) if params.contains(var) => match position {
            TypePosition::Value => {
                vars.value.insert(var.clone());
            }
            TypePosition::Effect => {
                vars.effect.insert(var.clone());
            }
        },
        typed_ir::Type::Var(_)
        | typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any => {}
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            collect_type_position_vars(param, TypePosition::Value, params, vars);
            collect_type_position_vars(param_effect, TypePosition::Effect, params, vars);
            collect_type_position_vars(ret_effect, TypePosition::Effect, params, vars);
            collect_type_position_vars(ret, TypePosition::Value, params, vars);
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_type_arg_position_vars(arg, params, vars);
            }
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_type_position_vars(item, position, params, vars);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_effect_item_position_vars(item, params, vars);
            }
            collect_type_position_vars(tail, TypePosition::Effect, params, vars);
        }
        typed_ir::Type::Record(record) => {
            for field in &record.fields {
                collect_type_position_vars(&field.value, TypePosition::Value, params, vars);
            }
            if let Some(spread) = &record.spread {
                collect_record_spread_position_vars(spread, params, vars);
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &variant.cases {
                for payload in &case.payloads {
                    collect_type_position_vars(payload, TypePosition::Value, params, vars);
                }
            }
            if let Some(tail) = &variant.tail {
                collect_type_position_vars(tail, TypePosition::Value, params, vars);
            }
        }
        typed_ir::Type::Recursive { body, .. } => {
            collect_type_position_vars(body, position, params, vars);
        }
    }
}

fn collect_effect_item_position_vars(
    ty: &typed_ir::Type,
    params: &BTreeSet<typed_ir::TypeVar>,
    vars: &mut TypePositionVars,
) {
    match ty {
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                collect_effect_atom_arg_position_vars(arg, params, vars);
            }
        }
        other => collect_type_position_vars(other, TypePosition::Effect, params, vars),
    }
}

fn collect_effect_atom_arg_position_vars(
    arg: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    vars: &mut TypePositionVars,
) {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            collect_type_position_vars(ty, TypePosition::Effect, params, vars);
        }
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_type_position_vars(lower, TypePosition::Effect, params, vars);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_type_position_vars(upper, TypePosition::Effect, params, vars);
            }
        }
    }
}

fn collect_type_arg_position_vars(
    arg: &typed_ir::TypeArg,
    params: &BTreeSet<typed_ir::TypeVar>,
    vars: &mut TypePositionVars,
) {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            collect_type_position_vars(ty, TypePosition::Value, params, vars);
        }
        typed_ir::TypeArg::Bounds(bounds) => {
            if let Some(lower) = bounds.lower.as_deref() {
                collect_type_position_vars(lower, TypePosition::Value, params, vars);
            }
            if let Some(upper) = bounds.upper.as_deref() {
                collect_type_position_vars(upper, TypePosition::Value, params, vars);
            }
        }
    }
}

fn collect_record_spread_position_vars(
    spread: &typed_ir::RecordSpread,
    params: &BTreeSet<typed_ir::TypeVar>,
    vars: &mut TypePositionVars,
) {
    match spread {
        typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
            collect_type_position_vars(ty, TypePosition::Value, params, vars);
        }
    }
}

fn split_row_items<'a>(
    left_items: &'a [typed_ir::Type],
    right_items: &'a [typed_ir::Type],
) -> RowResidual<'a> {
    let mut matched_right = vec![false; right_items.len()];
    let mut matched = Vec::new();
    let mut unmatched_left = Vec::new();

    for left in left_items {
        let Some((index, right)) = right_items
            .iter()
            .enumerate()
            .find(|(index, right)| !matched_right[*index] && same_effect_head(left, right))
        else {
            unmatched_left.push(left.clone());
            continue;
        };
        matched_right[index] = true;
        matched.push((left, right));
    }

    let unmatched_right = right_items
        .iter()
        .enumerate()
        .filter_map(|(index, right)| (!matched_right[index]).then_some(right.clone()))
        .collect();

    RowResidual {
        matched,
        unmatched_left,
        unmatched_right,
    }
}

fn find_variant_case<'a>(
    variant: &'a typed_ir::VariantType,
    name: &typed_ir::Name,
) -> Option<&'a typed_ir::VariantCase> {
    variant.cases.iter().find(|case| &case.name == name)
}

fn same_effect_head(left: &typed_ir::Type, right: &typed_ir::Type) -> bool {
    match (left, right) {
        (
            typed_ir::Type::Named { path, .. },
            typed_ir::Type::Named {
                path: actual_path, ..
            },
        ) => effect_paths_match(path, actual_path),
        _ => false,
    }
}

fn effect_paths_match(left: &typed_ir::Path, right: &typed_ir::Path) -> bool {
    left == right
        || qualified_prefix_effect_paths_match(left, right)
        || qualified_prefix_effect_paths_match(right, left)
}

fn same_erased_synthetic_effect_atom_path(left: &typed_ir::Path, right: &typed_ir::Path) -> bool {
    left == right && is_synthetic_var_effect_path(left)
}

fn is_synthetic_var_effect_path(path: &typed_ir::Path) -> bool {
    path.segments
        .first()
        .is_some_and(|segment| segment.0.starts_with('&') && segment.0.contains('#'))
}

fn qualified_prefix_effect_paths_match(parent: &typed_ir::Path, child: &typed_ir::Path) -> bool {
    effect_path_can_match_child_prefix(parent)
        && child.segments.len() > parent.segments.len()
        && child.segments.starts_with(parent.segments.as_slice())
}

fn effect_path_can_match_child_prefix(path: &typed_ir::Path) -> bool {
    path.segments.len() > 1
        || path.segments.first().is_some_and(|name| {
            name.0.starts_with('#') || name.0.starts_with('&') && name.0.contains('#')
        })
}

fn effect_row_from_items_and_tail(
    items: Vec<typed_ir::Type>,
    tail: typed_ir::Type,
) -> typed_ir::Type {
    if items.is_empty() {
        return tail;
    }
    typed_ir::Type::Row {
        items,
        tail: Box::new(tail),
    }
}

fn rename_type(
    ty: &typed_ir::Type,
    renames: &BTreeMap<typed_ir::TypeVar, typed_ir::TypeVar>,
) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Var(var) => renames
            .get(var)
            .cloned()
            .map(typed_ir::Type::Var)
            .unwrap_or_else(|| typed_ir::Type::Var(var.clone())),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(rename_type(param, renames)),
            param_effect: Box::new(rename_type(param_effect, renames)),
            ret_effect: Box::new(rename_type(ret_effect, renames)),
            ret: Box::new(rename_type(ret, renames)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| rename_type(item, renames))
                .collect(),
        ),
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| rename_type_arg(arg, renames))
                .collect(),
        },
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .iter()
                .map(|item| rename_type(item, renames))
                .collect(),
            tail: Box::new(rename_type(tail, renames)),
        },
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .iter()
                .map(|item| rename_type(item, renames))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .iter()
                .map(|item| rename_type(item, renames))
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name.clone(),
                    value: rename_type(&field.value, renames),
                    optional: field.optional,
                })
                .collect(),
            spread: record
                .spread
                .as_ref()
                .map(|spread| rename_record_spread(spread, renames)),
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
                        .map(|payload| rename_type(payload, renames))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .as_ref()
                .map(|tail| Box::new(rename_type(tail, renames))),
        }),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: renames.get(var).cloned().unwrap_or_else(|| var.clone()),
            body: Box::new(rename_type(body, renames)),
        },
        typed_ir::Type::Unknown => typed_ir::Type::Unknown,
        typed_ir::Type::Never => typed_ir::Type::Never,
        typed_ir::Type::Any => typed_ir::Type::Any,
    }
}

fn rename_type_arg(
    arg: &typed_ir::TypeArg,
    renames: &BTreeMap<typed_ir::TypeVar, typed_ir::TypeVar>,
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => typed_ir::TypeArg::Type(rename_type(ty, renames)),
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .as_ref()
                .map(|ty| Box::new(rename_type(ty, renames))),
            upper: bounds
                .upper
                .as_ref()
                .map(|ty| Box::new(rename_type(ty, renames))),
        }),
    }
}

fn rename_record_spread(
    spread: &typed_ir::RecordSpread,
    renames: &BTreeMap<typed_ir::TypeVar, typed_ir::TypeVar>,
) -> typed_ir::RecordSpread {
    match spread {
        typed_ir::RecordSpread::Head(ty) => {
            typed_ir::RecordSpread::Head(Box::new(rename_type(ty, renames)))
        }
        typed_ir::RecordSpread::Tail(ty) => {
            typed_ir::RecordSpread::Tail(Box::new(rename_type(ty, renames)))
        }
    }
}

fn materialize_type(
    ty: typed_ir::Type,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::Type {
    materialize_type_inner(ty, substitutions, &mut Vec::new())
}

fn materialize_type_inner(
    ty: typed_ir::Type,
    substitutions: &[typed_ir::TypeSubstitution],
    seen: &mut Vec<typed_ir::TypeVar>,
) -> typed_ir::Type {
    match ty {
        typed_ir::Type::Var(var) => {
            if seen.contains(&var) {
                return typed_ir::Type::Var(var);
            }
            let Some(substitution) = substitutions
                .iter()
                .find(|substitution| substitution.var == var)
            else {
                return typed_ir::Type::Var(var);
            };
            if matches!(&substitution.ty, typed_ir::Type::Var(next) if next == &var) {
                return typed_ir::Type::Var(var);
            }
            seen.push(var);
            let materialized = materialize_type_inner(substitution.ty.clone(), substitutions, seen);
            seen.pop();
            materialized
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => typed_ir::Type::Fun {
            param: Box::new(materialize_type_inner(*param, substitutions, seen)),
            param_effect: Box::new(materialize_type_inner(*param_effect, substitutions, seen)),
            ret_effect: Box::new(materialize_type_inner(*ret_effect, substitutions, seen)),
            ret: Box::new(materialize_type_inner(*ret, substitutions, seen)),
        },
        typed_ir::Type::Tuple(items) => typed_ir::Type::Tuple(
            items
                .into_iter()
                .map(|item| materialize_type_inner(item, substitutions, seen))
                .collect(),
        ),
        typed_ir::Type::Named { path, args } => typed_ir::Type::Named {
            path,
            args: args
                .into_iter()
                .map(|arg| materialize_type_arg(arg, substitutions, seen))
                .collect(),
        },
        typed_ir::Type::Row { items, tail } => typed_ir::Type::Row {
            items: items
                .into_iter()
                .map(|item| materialize_type_inner(item, substitutions, seen))
                .collect(),
            tail: Box::new(materialize_type_inner(*tail, substitutions, seen)),
        },
        typed_ir::Type::Union(items) => typed_ir::Type::Union(
            items
                .into_iter()
                .map(|item| materialize_type_inner(item, substitutions, seen))
                .collect(),
        ),
        typed_ir::Type::Inter(items) => typed_ir::Type::Inter(
            items
                .into_iter()
                .map(|item| materialize_type_inner(item, substitutions, seen))
                .collect(),
        ),
        typed_ir::Type::Record(record) => typed_ir::Type::Record(typed_ir::RecordType {
            fields: record
                .fields
                .into_iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name,
                    value: materialize_type_inner(field.value, substitutions, seen),
                    optional: field.optional,
                })
                .collect(),
            spread: record
                .spread
                .map(|spread| materialize_record_spread(spread, substitutions, seen)),
        }),
        typed_ir::Type::Variant(variant) => typed_ir::Type::Variant(typed_ir::VariantType {
            cases: variant
                .cases
                .into_iter()
                .map(|case| typed_ir::VariantCase {
                    name: case.name,
                    payloads: case
                        .payloads
                        .into_iter()
                        .map(|payload| materialize_type_inner(payload, substitutions, seen))
                        .collect(),
                })
                .collect(),
            tail: variant
                .tail
                .map(|tail| Box::new(materialize_type_inner(*tail, substitutions, seen))),
        }),
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var,
            body: Box::new(materialize_type_inner(*body, substitutions, seen)),
        },
        ty => ty,
    }
}

fn materialize_record_spread(
    spread: typed_ir::RecordSpread,
    substitutions: &[typed_ir::TypeSubstitution],
    seen: &mut Vec<typed_ir::TypeVar>,
) -> typed_ir::RecordSpread {
    match spread {
        typed_ir::RecordSpread::Head(ty) => {
            typed_ir::RecordSpread::Head(Box::new(materialize_type_inner(*ty, substitutions, seen)))
        }
        typed_ir::RecordSpread::Tail(ty) => {
            typed_ir::RecordSpread::Tail(Box::new(materialize_type_inner(*ty, substitutions, seen)))
        }
    }
}

fn materialize_type_arg(
    arg: typed_ir::TypeArg,
    substitutions: &[typed_ir::TypeSubstitution],
    seen: &mut Vec<typed_ir::TypeVar>,
) -> typed_ir::TypeArg {
    match arg {
        typed_ir::TypeArg::Type(ty) => {
            typed_ir::TypeArg::Type(materialize_type_inner(ty, substitutions, seen))
        }
        typed_ir::TypeArg::Bounds(bounds) => typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
            lower: bounds
                .lower
                .map(|ty| Box::new(materialize_type_inner(*ty, substitutions, seen))),
            upper: bounds
                .upper
                .map(|ty| Box::new(materialize_type_inner(*ty, substitutions, seen))),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_runtime_ir::{Expr, ExprKind};

    #[test]
    fn principal_type_is_freshened_into_graph() {
        let mut graph = TypeGraph::default();
        let instance = graph.instantiate_principal(&id_binding());

        assert_eq!(instance.original_binding, path(&["id"]));
        assert!(matches!(
            instance.principal_type,
            typed_ir::Type::Fun { .. }
        ));
        assert_eq!(
            instance.type_params,
            vec![PrincipalTypeParam {
                original: typed_ir::TypeVar("a".into()),
                fresh: typed_ir::TypeVar("a#0".into()),
            }]
        );
        assert!(graph.slot(&typed_ir::TypeVar("a#0".into())).is_some());
    }

    #[test]
    fn graph_solves_fresh_principal_var_from_lower_bound() {
        let mut graph = TypeGraph::default();
        let instance = graph.instantiate_principal(&id_binding());
        let typed_ir::Type::Fun { param, ret, .. } = &instance.principal_type else {
            panic!("expected function principal");
        };

        graph
            .collect_runtime_lower(param, &RuntimeType::Value(int_type()))
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.materialize_core(ret.as_ref().clone()), int_type());
        assert_eq!(
            instance.original_substitutions(&solution),
            vec![typed_ir::TypeSubstitution {
                var: typed_ir::TypeVar("a".into()),
                ty: int_type(),
            }]
        );
        assert!(solution.is_complete());
    }

    #[test]
    fn original_substitutions_chase_solution_chains() {
        let original = typed_ir::TypeVar("a".into());
        let fresh = typed_ir::TypeVar("a#0".into());
        let instance = PrincipalInstance {
            original_binding: path(&["id"]),
            principal_type: typed_ir::Type::Var(fresh.clone()),
            type_params: vec![PrincipalTypeParam {
                original: original.clone(),
                fresh: fresh.clone(),
            }],
        };
        let solution = GraphSolution {
            type_vars: vec![
                ResolvedTypeVar {
                    var: original.clone(),
                    bounds: TypeVarBounds {
                        lower: None,
                        upper: Some(int_type()),
                    },
                    solution: Some(int_type()),
                },
                ResolvedTypeVar {
                    var: fresh,
                    bounds: TypeVarBounds {
                        lower: Some(typed_ir::Type::Var(original.clone())),
                        upper: None,
                    },
                    solution: Some(typed_ir::Type::Var(original.clone())),
                },
            ],
        };

        assert_eq!(
            instance.original_substitutions(&solution),
            vec![typed_ir::TypeSubstitution {
                var: original,
                ty: int_type(),
            }]
        );
    }

    #[test]
    fn named_bound_subtype_recurses_into_synthetic_effect_args() {
        let list_int = list_type(int_type());
        let precise = ref_type(
            synthetic_effect_type("&xs#0", vec![typed_ir::TypeArg::Type(list_int.clone())]),
            list_int.clone(),
        );
        let erased = ref_type(synthetic_effect_type("&xs#0", Vec::new()), list_int);

        assert!(bound_subtype(&precise, &erased));
    }

    #[test]
    fn singleton_row_bound_subtype_matches_erased_effect_atom() {
        let list_int = list_type(int_type());
        let item = synthetic_effect_type("&xs#0", vec![typed_ir::TypeArg::Type(list_int)]);
        let row = effect_row(vec![item]);
        let erased = synthetic_effect_type("&xs#0", Vec::new());

        assert!(bound_subtype(&row, &erased));
    }

    #[test]
    fn subtype_var_upper_chain_propagates_concrete_upper_bound() {
        let mut graph = TypeGraph::default();
        let value = typed_ir::TypeVar("value".into());
        let result = typed_ir::TypeVar("result".into());

        graph
            .constrain_subtype(
                typed_ir::Type::Var(value.clone()),
                typed_ir::Type::Var(result.clone()),
            )
            .unwrap();
        graph
            .constrain_subtype(typed_ir::Type::Var(result), int_type())
            .unwrap();

        let solution = graph.solve();

        assert_eq!(solution.solution_for(&value), Some(&int_type()));
    }

    #[test]
    fn external_lower_var_solves_tracked_upper_without_creating_slot() {
        let mut graph = TypeGraph::default();
        let external = typed_ir::TypeVar("a".into());
        let tracked = typed_ir::TypeVar("a#0".into());
        graph.mark_external_vars([external.clone()]);
        graph.slots.entry(tracked.clone()).or_default();

        graph
            .constrain_subtype(
                typed_ir::Type::Var(external.clone()),
                typed_ir::Type::Var(tracked.clone()),
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(
            solution.solution_for(&tracked),
            Some(&typed_ir::Type::Var(external.clone()))
        );
        assert_eq!(solution.solution_for(&external), None);
        assert!(solution.is_complete());
    }

    #[test]
    fn instantiate_principal_skips_external_var_names() {
        let mut graph = TypeGraph::default();
        graph.mark_external_vars([typed_ir::TypeVar("a#0".into())]);

        let instance = graph.instantiate_principal(&id_binding());

        assert_eq!(
            instance.type_params[0].fresh,
            typed_ir::TypeVar("a#1".into())
        );
        assert!(graph.slot(&typed_ir::TypeVar("a#0".into())).is_none());
        assert!(graph.slot(&typed_ir::TypeVar("a#1".into())).is_some());
    }

    #[test]
    fn subtype_function_result_upper_closes_effect_payload_var() {
        let mut graph = TypeGraph::default();
        let payload = typed_ir::TypeVar("payload".into());
        let result = typed_ir::TypeVar("result".into());
        let principal = fun_type_with_effects(
            typed_ir::Type::Never,
            effect_row(vec![
                effect_type_arg("sub", typed_ir::Type::Var(payload.clone())),
                effect_type("undet"),
            ]),
            effect_type("undet"),
            typed_ir::Type::Var(payload.clone()),
        );
        let expected = fun_type_with_effects(
            typed_ir::Type::Never,
            closed_row(&["sub", "undet"]),
            effect_type("undet"),
            typed_ir::Type::Var(result.clone()),
        );

        graph.constrain_subtype(principal, expected).unwrap();
        graph
            .constrain_subtype(typed_ir::Type::Var(result.clone()), int_type())
            .unwrap();

        let solution = graph.solve();

        assert_eq!(solution.solution_for(&payload), Some(&int_type()));
    }

    #[test]
    fn materialize_core_chases_substitution_chains_without_self_loop() {
        let source = typed_ir::TypeVar("source".into());
        let intermediate = typed_ir::TypeVar("intermediate".into());
        let self_ref = typed_ir::TypeVar("self".into());
        let substitutions = vec![
            typed_ir::TypeSubstitution {
                var: source.clone(),
                ty: typed_ir::Type::Var(intermediate.clone()),
            },
            typed_ir::TypeSubstitution {
                var: intermediate,
                ty: int_type(),
            },
            typed_ir::TypeSubstitution {
                var: self_ref.clone(),
                ty: typed_ir::Type::Var(self_ref.clone()),
            },
        ];

        assert_eq!(
            materialize_core_type(typed_ir::Type::Var(source), &substitutions),
            int_type()
        );
        assert_eq!(
            materialize_core_type(typed_ir::Type::Var(self_ref.clone()), &substitutions),
            typed_ir::Type::Var(self_ref)
        );
    }

    #[test]
    fn any_lower_bound_conflicts_with_concrete_upper_bound() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());

        graph
            .constrain_subtype(typed_ir::Type::Any, typed_ir::Type::Var(var.clone()))
            .unwrap();
        let error = graph
            .constrain_subtype(typed_ir::Type::Var(var.clone()), int_type())
            .unwrap_err();

        assert!(matches!(
            error,
            MonomorphizeDiagnostic::ConflictingBounds {
                var: error_var,
                previous: typed_ir::Type::Any,
                next,
            } if error_var == var && next == int_type()
        ));
    }

    #[test]
    fn function_runtime_lower_bound_flips_parameter_polarity() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());
        let template = fun_type(typed_ir::Type::Var(var.clone()), unit_type());
        let actual = fun_type(int_type(), unit_type());

        graph
            .collect_runtime_lower(&template, &RuntimeType::Value(actual))
            .unwrap();

        let bounds = graph.slot(&var).expect("parameter var should be tracked");
        assert_eq!(bounds.lower, None);
        assert_eq!(bounds.upper, Some(int_type()));
    }

    #[test]
    fn function_runtime_lower_bound_does_not_turn_top_parameter_into_solution() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());
        let template = fun_type(typed_ir::Type::Var(var.clone()), unit_type());
        let actual = fun_type(typed_ir::Type::Any, unit_type());

        graph
            .collect_runtime_lower(&template, &RuntimeType::Value(actual))
            .unwrap();

        assert_eq!(graph.slot(&var).and_then(TypeVarBounds::solution_ref), None);
    }

    #[test]
    fn graph_joins_subtype_lower_bound_into_union_supertype() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("effect".into());
        let last = closed_row(&["last"]);
        let sub = closed_row(&["sub"]);
        let either = typed_ir::Type::Union(vec![sub, last.clone()]);

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(last)),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(either.clone())),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&either)
        );
    }

    #[test]
    fn graph_keeps_existing_union_supertype_lower_bound() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("effect".into());
        let last = closed_row(&["last"]);
        let sub = closed_row(&["sub"]);
        let either = typed_ir::Type::Union(vec![sub, last.clone()]);

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(either.clone())),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(last)),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&either)
        );
    }

    #[test]
    fn graph_treats_named_unit_and_empty_tuple_bounds_as_equivalent() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("unitish".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(unit_type())),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(typed_ir::Type::Tuple(Vec::new()))),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&unit_type())
        );
    }

    #[test]
    fn graph_joins_lower_bounds_using_cast_order() {
        let small = effect_type("small");
        let middle = effect_type("middle");
        let large = effect_type("large");
        let cast_order = TypeCastOrder::from_edges(vec![
            (small.clone(), middle),
            (effect_type("middle"), large.clone()),
        ]);
        let mut graph = TypeGraph::with_cast_order(cast_order);
        let var = typed_ir::TypeVar("value".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(small)),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(large.clone())),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&large)
        );
    }

    #[test]
    fn lower_solution_wins_over_upper_solution() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(int_type())),
                    upper: Some(RuntimeType::Value(number_type())),
                },
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(
            solution.substitutions(),
            vec![typed_ir::TypeSubstitution {
                var,
                ty: int_type(),
            }]
        );
    }

    #[test]
    fn top_and_bottom_are_extremes_not_holes() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(any_type())),
                    upper: Some(RuntimeType::Value(never_type())),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&any_type())
        );
    }

    #[test]
    fn bottom_lower_and_top_upper_are_vacuous_bounds() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(never_type())),
                    upper: Some(RuntimeType::Value(any_type())),
                },
            )
            .unwrap();

        assert_eq!(graph.slot(&var).and_then(TypeVarBounds::solution_ref), None);

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(int_type())),
                    upper: Some(RuntimeType::Value(any_type())),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&int_type())
        );
    }

    #[test]
    fn symbolic_bounds_do_not_conflict_before_concrete_bounds_arrive() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());
        let first = typed_ir::Type::Var(typed_ir::TypeVar("b".into()));
        let second = typed_ir::Type::Var(typed_ir::TypeVar("c".into()));

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(first.clone())),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(second)),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&first)
        );
    }

    #[test]
    fn indirect_var_lower_bound_cycle_is_not_chased_forever() {
        let mut graph = TypeGraph::default();
        let a = typed_ir::TypeVar("a".into());
        let b = typed_ir::TypeVar("b".into());

        graph
            .collect_runtime_lower(
                &typed_ir::Type::Var(a.clone()),
                &RuntimeType::Value(typed_ir::Type::Var(b.clone())),
            )
            .unwrap();
        graph
            .collect_runtime_lower(
                &typed_ir::Type::Var(b.clone()),
                &RuntimeType::Value(typed_ir::Type::Var(a.clone())),
            )
            .unwrap();
        graph
            .constrain_subtype(typed_ir::Type::Var(a.clone()), int_type())
            .unwrap();

        assert_eq!(
            graph.slot(&a).and_then(TypeVarBounds::solution_ref),
            Some(&typed_ir::Type::Var(b))
        );
    }

    #[test]
    fn graph_solution_keeps_lower_and_upper_after_solving() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(int_type())),
                    upper: Some(RuntimeType::Value(number_type())),
                },
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(
            solution.type_vars,
            vec![ResolvedTypeVar {
                var,
                bounds: TypeVarBounds {
                    lower: Some(int_type()),
                    upper: Some(number_type()),
                },
                solution: Some(int_type()),
            }]
        );
        assert!(solution.is_complete());
    }

    #[test]
    fn subtype_constraints_solve_curried_first_application() {
        let mut graph = TypeGraph::default();
        let a_var = typed_ir::TypeVar("a".into());
        let b_var = typed_ir::TypeVar("b".into());
        let a = typed_ir::Type::Var(a_var.clone());
        let b = typed_ir::Type::Var(b_var.clone());
        graph.slots.entry(a_var.clone()).or_default();
        graph.slots.entry(b_var.clone()).or_default();
        let r0 = graph.fresh_hole("apply");
        let r1 = graph.fresh_hole("apply");

        graph
            .constrain_subtype(
                fun_type(a.clone(), fun_type(b.clone(), a.clone())),
                fun_type(int_type(), r0.clone()),
            )
            .unwrap();
        graph
            .constrain_subtype(r0, fun_type(bool_type(), r1.clone()))
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.solution_for(&a_var), Some(&int_type()));
        assert_eq!(solution.solution_for(&b_var), Some(&bool_type()));
        assert_eq!(solution.materialize_core(r1), int_type());
        assert!(solution.is_complete());
    }

    #[test]
    fn subtype_constraints_propagate_after_later_bounds_arrive() {
        let mut graph = TypeGraph::default();
        let a_var = typed_ir::TypeVar("a".into());
        let b_var = typed_ir::TypeVar("b".into());
        graph.slots.entry(a_var.clone()).or_default();
        graph.slots.entry(b_var.clone()).or_default();

        graph
            .constrain_subtype(
                typed_ir::Type::Var(a_var.clone()),
                typed_ir::Type::Var(b_var.clone()),
            )
            .unwrap();
        graph
            .collect_runtime_lower(
                &typed_ir::Type::Var(a_var.clone()),
                &RuntimeType::Value(int_type()),
            )
            .unwrap();

        let solution = graph.solve();

        assert_eq!(solution.solution_for(&a_var), Some(&int_type()));
        assert_eq!(solution.solution_for(&b_var), Some(&int_type()));
    }

    #[test]
    fn union_lower_constraint_propagates_upper_bound_to_items() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("a".into());
        graph.slots.entry(var.clone()).or_default();

        graph
            .constrain_subtype(
                typed_ir::Type::Union(vec![typed_ir::Type::Var(var.clone()), int_type()]),
                int_type(),
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.solution_for(&var), Some(&int_type()));
        assert!(solution.is_complete());
    }

    #[test]
    fn variant_subtype_solves_present_payloads_and_bottoms_absent_upper_payloads() {
        let mut graph = TypeGraph::default();
        let ok_var = typed_ir::TypeVar("ok".into());
        let err_var = typed_ir::TypeVar("err".into());
        graph.slots.entry(ok_var.clone()).or_default();
        graph.slots.entry(err_var.clone()).or_default();

        graph
            .constrain_subtype(
                variant_type(&[("ok", vec![int_type()])]),
                variant_type(&[
                    ("ok", vec![typed_ir::Type::Var(ok_var.clone())]),
                    ("err", vec![typed_ir::Type::Var(err_var.clone())]),
                    ("pending", Vec::new()),
                ]),
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.solution_for(&ok_var), Some(&int_type()));
        assert_eq!(
            solution.solution_for(&err_var),
            Some(&typed_ir::Type::Never)
        );
        assert!(solution.is_complete());
    }

    #[test]
    fn absent_variant_payload_defaults_unbound_intersection_parts_to_bottom() {
        let mut graph = TypeGraph::default();
        let observed = typed_ir::TypeVar("observed".into());
        let residual = typed_ir::TypeVar("residual".into());
        graph.slots.entry(observed.clone()).or_default();
        graph.slots.entry(residual.clone()).or_default();
        graph
            .constrain_subtype(int_type(), typed_ir::Type::Var(observed.clone()))
            .unwrap();

        graph
            .constrain_subtype(
                variant_type(&[("err", vec![bool_type()])]),
                variant_type(&[
                    (
                        "ok",
                        vec![typed_ir::Type::Inter(vec![
                            typed_ir::Type::Var(observed.clone()),
                            typed_ir::Type::Var(residual.clone()),
                        ])],
                    ),
                    ("err", vec![bool_type()]),
                ]),
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.solution_for(&observed), Some(&int_type()));
        assert_eq!(
            solution.solution_for(&residual),
            Some(&typed_ir::Type::Never)
        );
        assert!(solution.is_complete());
    }

    #[test]
    fn record_subtype_solves_field_type_variables() {
        let mut graph = TypeGraph::default();
        let port_var = typed_ir::TypeVar("port".into());
        graph.slots.entry(port_var.clone()).or_default();

        graph
            .constrain_subtype(
                record_type(&[("port", typed_ir::Type::Var(port_var.clone()))]),
                record_type(&[("port", int_type())]),
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.solution_for(&port_var), Some(&int_type()));
        assert!(solution.is_complete());
    }

    #[test]
    fn absent_optional_record_field_defaults_unbound_value_to_bottom() {
        let mut graph = TypeGraph::default();
        let width_var = typed_ir::TypeVar("width".into());
        graph.slots.entry(width_var.clone()).or_default();

        graph
            .constrain_subtype(
                record_type(&[]),
                typed_ir::Type::Record(typed_ir::RecordType {
                    fields: vec![typed_ir::RecordField {
                        name: typed_ir::Name("width".to_string()),
                        value: typed_ir::Type::Var(width_var.clone()),
                        optional: true,
                    }],
                    spread: None,
                }),
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(
            solution.solution_for(&width_var),
            Some(&typed_ir::Type::Never)
        );
        assert!(solution.is_complete());
    }

    #[test]
    fn materialized_union_drops_bottom_and_singleton() {
        let ty = materialize_core_type(
            typed_ir::Type::Union(vec![typed_ir::Type::Never, int_type()]),
            &[],
        );

        assert_eq!(ty, int_type());
    }

    #[test]
    fn normalized_union_absorbs_intersection_subtype() {
        let acc = typed_ir::Type::Var(typed_ir::TypeVar("acc".into()));
        let branch = typed_ir::Type::Var(typed_ir::TypeVar("branch".into()));
        let ty = materialize_core_type(
            typed_ir::Type::Union(vec![
                acc.clone(),
                typed_ir::Type::Inter(vec![acc.clone(), branch]),
            ]),
            &[],
        );

        assert_eq!(ty, acc);
    }

    #[test]
    fn normalized_intersection_absorbs_union_supertype() {
        let acc = typed_ir::Type::Var(typed_ir::TypeVar("acc".into()));
        let branch = typed_ir::Type::Var(typed_ir::TypeVar("branch".into()));
        let ty = materialize_core_type(
            typed_ir::Type::Inter(vec![
                typed_ir::Type::Union(vec![unit_type(), acc.clone(), branch]),
                acc.clone(),
            ]),
            &[],
        );

        assert_eq!(ty, acc);
    }

    #[test]
    fn runtime_function_thunks_feed_function_effect_slots() {
        let mut graph = TypeGraph::default();
        let a_var = typed_ir::TypeVar("a".into());
        let b_var = typed_ir::TypeVar("b".into());
        let param_effect_var = typed_ir::TypeVar("pe".into());
        let ret_effect_var = typed_ir::TypeVar("re".into());
        let template = fun_type_with_effects(
            typed_ir::Type::Var(a_var.clone()),
            typed_ir::Type::Var(param_effect_var.clone()),
            typed_ir::Type::Var(ret_effect_var.clone()),
            typed_ir::Type::Var(b_var.clone()),
        );

        graph
            .collect_runtime_bounds(
                &template,
                &RuntimeBounds::exact(RuntimeType::Fun {
                    param: Box::new(RuntimeType::Thunk {
                        effect: effect_type("arg"),
                        value: Box::new(RuntimeType::Value(int_type())),
                    }),
                    ret: Box::new(RuntimeType::Thunk {
                        effect: effect_type("ret"),
                        value: Box::new(RuntimeType::Value(bool_type())),
                    }),
                }),
            )
            .unwrap();
        let solution = graph.solve();

        assert_eq!(solution.solution_for(&a_var), Some(&int_type()));
        assert_eq!(solution.solution_for(&b_var), Some(&bool_type()));
        assert_eq!(
            solution.solution_for(&param_effect_var),
            Some(&effect_type("arg"))
        );
        assert_eq!(
            solution.solution_for(&ret_effect_var),
            Some(&effect_type("ret"))
        );
        assert!(solution.is_complete());
    }

    #[test]
    fn singleton_closed_effect_row_bound_matches_its_atom() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let atom = effect_type("io");
        let row = typed_ir::Type::Row {
            items: vec![atom.clone()],
            tail: Box::new(typed_ir::Type::Never),
        };

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(row.clone())),
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(atom)),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&row)
        );
    }

    #[test]
    fn empty_effect_row_bound_matches_its_tail() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let open_top_row = typed_ir::Type::Row {
            items: Vec::new(),
            tail: Box::new(typed_ir::Type::Any),
        };

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(typed_ir::Type::Any)),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(open_top_row)),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&typed_ir::Type::Any)
        );
    }

    #[test]
    fn never_effect_row_item_is_empty() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let never_item_row = typed_ir::Type::Row {
            items: vec![typed_ir::Type::Never],
            tail: Box::new(typed_ir::Type::Never),
        };

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(typed_ir::Type::Never)),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(never_item_row)),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(graph.slot(&var).and_then(TypeVarBounds::solution_ref), None);
    }

    #[test]
    fn intersection_bound_drops_top_and_duplicate_rows() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let row = typed_ir::Type::Row {
            items: vec![effect_type("ref_update")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let noisy = typed_ir::Type::Inter(vec![typed_ir::Type::Any, row.clone(), row.clone()]);

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(row.clone())),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(noisy)),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&row)
        );
    }

    #[test]
    fn closed_effect_row_intersection_keeps_common_items() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let parse = effect_type("parse");
        let pick = effect_type("pick");
        let parse_and_pick = typed_ir::Type::Row {
            items: vec![parse.clone(), pick],
            tail: Box::new(typed_ir::Type::Never),
        };
        let parse_only = typed_ir::Type::Row {
            items: vec![parse],
            tail: Box::new(typed_ir::Type::Never),
        };
        let intersection = typed_ir::Type::Inter(vec![parse_and_pick, parse_only.clone()]);

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(intersection)),
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(parse_only.clone())),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(|bounds| bounds.upper.as_ref()),
            Some(&parse_only)
        );
    }

    #[test]
    fn closed_effect_row_subtypes_open_effect_row_intersection() {
        let read = effect_type("read");
        let write = effect_type("write");
        let closed = typed_ir::Type::Row {
            items: vec![read.clone(), write.clone()],
            tail: Box::new(typed_ir::Type::Never),
        };
        let read_open = typed_ir::Type::Row {
            items: vec![read],
            tail: Box::new(typed_ir::Type::Any),
        };
        let write_open = typed_ir::Type::Row {
            items: vec![write],
            tail: Box::new(typed_ir::Type::Any),
        };
        let open_intersection = typed_ir::Type::Inter(vec![read_open, write_open]);

        assert!(bound_subtype(&closed, &open_intersection));
    }

    #[test]
    fn synthetic_effect_atom_payload_is_below_erased_atom() {
        let erased = effect_type("&xs#1");
        let payload = effect_type_arg("&xs#1", int_type());

        assert!(bound_subtype(&payload, &erased));
        assert!(!bound_subtype(&erased, &payload));
    }

    #[test]
    fn upper_bound_prefers_payload_effect_atom_below_erased_atom() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let erased = effect_type("&xs#1");
        let payload = effect_type_arg("&xs#1", int_type());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(erased)),
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(payload.clone())),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(|bounds| bounds.upper.as_ref()),
            Some(&payload)
        );
    }

    #[test]
    fn lower_bound_prefers_erased_effect_atom_above_payload_atom() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let erased = effect_type("&xs#1");
        let payload = effect_type_arg("&xs#1", int_type());

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(erased.clone())),
                    upper: None,
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(payload)),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(|bounds| bounds.lower.as_ref()),
            Some(&erased)
        );
    }

    #[test]
    fn upper_bound_prefers_closed_row_below_open_row_intersection() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let state = effect_type("&s");
        let var_effect = effect_type("var");
        let closed = typed_ir::Type::Row {
            items: vec![state.clone(), var_effect.clone()],
            tail: Box::new(typed_ir::Type::Never),
        };
        let state_open = typed_ir::Type::Row {
            items: vec![state],
            tail: Box::new(typed_ir::Type::Any),
        };
        let var_open = typed_ir::Type::Row {
            items: vec![var_effect],
            tail: Box::new(typed_ir::Type::Any),
        };
        let recursive_open = typed_ir::Type::Recursive {
            var: typed_ir::TypeVar("tail".into()),
            body: Box::new(typed_ir::Type::Row {
                items: Vec::new(),
                tail: Box::new(typed_ir::Type::Any),
            }),
        };
        let open_intersection = typed_ir::Type::Inter(vec![state_open, var_open, recursive_open]);

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(open_intersection)),
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(closed.clone())),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(|bounds| bounds.upper.as_ref()),
            Some(&closed)
        );
    }

    #[test]
    fn closed_effect_row_item_flattens_into_outer_row() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("e".into());
        let nested = typed_ir::Type::Row {
            items: vec![typed_ir::Type::Row {
                items: vec![effect_type("junction")],
                tail: Box::new(typed_ir::Type::Never),
            }],
            tail: Box::new(typed_ir::Type::Never),
        };
        let expected = typed_ir::Type::Row {
            items: vec![effect_type("junction")],
            tail: Box::new(typed_ir::Type::Never),
        };

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: Some(RuntimeType::Value(nested)),
                    upper: None,
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(TypeVarBounds::solution_ref),
            Some(&expected)
        );
    }

    #[test]
    fn function_upper_bounds_merge_by_variance() {
        let mut graph = TypeGraph::default();
        let var = typed_ir::TypeVar("f".into());
        let precise = fun_type_with_effects(
            bool_type(),
            typed_ir::Type::Never,
            closed_row(&["parse"]),
            int_type(),
        );
        let broad = fun_type_with_effects(
            bool_type(),
            typed_ir::Type::Any,
            typed_ir::Type::Any,
            int_type(),
        );

        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(broad)),
                },
            )
            .unwrap();
        graph
            .collect_runtime_bounds(
                &typed_ir::Type::Var(var.clone()),
                &RuntimeBounds {
                    lower: None,
                    upper: Some(RuntimeType::Value(precise.clone())),
                },
            )
            .unwrap();

        assert_eq!(
            graph.slot(&var).and_then(|bounds| bounds.upper.as_ref()),
            Some(&precise)
        );
    }

    #[test]
    fn graph_solution_reports_open_type_vars() {
        let mut graph = TypeGraph::default();
        graph.instantiate_principal(&id_binding());
        let solution = graph.solve();

        assert!(!solution.is_complete());
    }

    #[test]
    fn effect_atom_payload_only_type_params_default_as_effect_params() {
        let payload = typed_ir::TypeVar("payload".into());
        let binding = Binding {
            name: path(&["stateful"]),
            type_params: vec![payload.clone()],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: fun_type_with_effects(
                    unit_type(),
                    typed_ir::Type::Never,
                    effect_row(vec![effect_type_arg(
                        "state",
                        typed_ir::Type::Var(payload.clone()),
                    )]),
                    unit_type(),
                ),
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        };
        let mut graph = TypeGraph::default();
        let instance = graph.instantiate_principal(&binding);
        let fresh = instance.type_params[0].fresh.clone();

        graph
            .default_unbound_lower(instance.effect_only_type_params(), typed_ir::Type::Never)
            .unwrap();
        let solution = graph.solve();

        assert!(solution.is_complete());
        assert_eq!(solution.solution_for(&fresh), Some(&typed_ir::Type::Never));
    }

    fn id_binding() -> Binding {
        Binding {
            name: path(&["id"]),
            type_params: vec![typed_ir::TypeVar("a".into())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Fun {
                    param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                    param_effect: Box::new(typed_ir::Type::Never),
                    ret_effect: Box::new(typed_ir::Type::Never),
                    ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("a".into()))),
                },
            },
            body: Expr::typed(ExprKind::Tuple(Vec::new()), RuntimeType::Unknown),
        }
    }

    fn int_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["Int"]),
            args: Vec::new(),
        }
    }

    fn bool_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["Bool"]),
            args: Vec::new(),
        }
    }

    fn unit_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["unit"]),
            args: Vec::new(),
        }
    }

    fn any_type() -> typed_ir::Type {
        typed_ir::Type::Any
    }

    fn number_type() -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["Number"]),
            args: Vec::new(),
        }
    }

    fn list_type(item: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "list", "list"]),
            args: vec![typed_ir::TypeArg::Type(item)],
        }
    }

    fn ref_type(effect: typed_ir::Type, value: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&["std", "var", "ref"]),
            args: vec![
                typed_ir::TypeArg::Type(effect),
                typed_ir::TypeArg::Type(value),
            ],
        }
    }

    fn never_type() -> typed_ir::Type {
        typed_ir::Type::Never
    }

    fn variant_type(cases: &[(&str, Vec<typed_ir::Type>)]) -> typed_ir::Type {
        typed_ir::Type::Variant(typed_ir::VariantType {
            cases: cases
                .iter()
                .map(|(name, payloads)| typed_ir::VariantCase {
                    name: typed_ir::Name((*name).to_string()),
                    payloads: payloads.clone(),
                })
                .collect(),
            tail: None,
        })
    }

    fn record_type(fields: &[(&str, typed_ir::Type)]) -> typed_ir::Type {
        typed_ir::Type::Record(typed_ir::RecordType {
            fields: fields
                .iter()
                .map(|(name, value)| typed_ir::RecordField {
                    name: typed_ir::Name((*name).to_string()),
                    value: value.clone(),
                    optional: false,
                })
                .collect(),
            spread: None,
        })
    }

    fn fun_type(param: typed_ir::Type, ret: typed_ir::Type) -> typed_ir::Type {
        fun_type_with_effects(param, typed_ir::Type::Never, typed_ir::Type::Never, ret)
    }

    fn fun_type_with_effects(
        param: typed_ir::Type,
        param_effect: typed_ir::Type,
        ret_effect: typed_ir::Type,
        ret: typed_ir::Type,
    ) -> typed_ir::Type {
        typed_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(param_effect),
            ret_effect: Box::new(ret_effect),
            ret: Box::new(ret),
        }
    }

    fn effect_type(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&[name]),
            args: Vec::new(),
        }
    }

    fn effect_type_arg(name: &str, arg: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&[name]),
            args: vec![typed_ir::TypeArg::Type(arg)],
        }
    }

    fn synthetic_effect_type(name: &str, args: Vec<typed_ir::TypeArg>) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: path(&[name]),
            args,
        }
    }

    fn effect_row(items: Vec<typed_ir::Type>) -> typed_ir::Type {
        typed_ir::Type::Row {
            items,
            tail: Box::new(typed_ir::Type::Never),
        }
    }

    fn closed_row(items: &[&str]) -> typed_ir::Type {
        effect_row(items.iter().map(|item| effect_type(item)).collect())
    }

    fn path(segments: &[&str]) -> typed_ir::Path {
        typed_ir::Path::new(
            segments
                .iter()
                .map(|segment| typed_ir::Name((*segment).into()))
                .collect(),
        )
    }
}
