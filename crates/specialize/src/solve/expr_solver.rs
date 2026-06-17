use super::*;

mod control;
mod instantiate;
mod pattern;

impl<'a> ExprTypeSolver<'a> {
    pub(super) fn expr(
        &mut self,
        expr: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        if expected.is_some() && matches!(self.arena.expr(expr), poly_expr::Expr::Var(_)) {
            self.plan.mark_contextual_value_fetch(expr);
        }

        if let Some(expected) = expected {
            self.set_expr_expected(expr, expected.clone())?;
            if let Some(actual) = self.plan.actual(expr).cloned() {
                self.constrain_expr_boundary(actual.clone(), expected)?;
                return Ok(actual);
            }
            let actual = self.infer_expr(expr, Some(expected.clone()))?;
            self.constrain_expr_boundary(actual.clone(), expected)?;
            self.plan.set_actual(expr, actual.clone())?;
            return Ok(actual);
        }

        if let Some(actual) = self.plan.actual(expr) {
            return Ok(actual.clone());
        }

        let actual = self.infer_expr(expr, None)?;
        self.plan.set_actual(expr, actual.clone())?;
        Ok(actual)
    }

    pub(super) fn set_expr_expected(
        &mut self,
        expr: poly_expr::ExprId,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        if let Some(existing) = self.plan.expected(expr).cloned()
            && existing != ty
            && let Some(merged) = merge_expr_expected_for_solver(&existing, &ty)
            && self.type_open_vars_are_graph_slots(&merged)
        {
            self.plan.types.entry(expr).or_default().expected = Some(merged);
            return Ok(());
        }
        self.plan.set_expected(expr, ty)
    }

    pub(super) fn freshen_external_type(&mut self, ty: Type, context: TypeSlotKind) -> Type {
        let mut vars = HashMap::new();
        self.freshen_external_type_with_vars(ty, context, &mut vars)
    }

    pub(super) fn freshen_external_type_with_vars(
        &mut self,
        ty: Type,
        context: TypeSlotKind,
        vars: &mut HashMap<(u32, TypeSlotKind), Type>,
    ) -> Type {
        match ty {
            Type::OpenVar(var) => vars
                .entry((var, context))
                .or_insert_with(|| self.graph.fresh_slot(context))
                .clone(),
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => Type::Fun {
                arg: Box::new(self.freshen_external_type_with_vars(
                    *arg,
                    TypeSlotKind::Value,
                    vars,
                )),
                arg_effect: Box::new(self.freshen_external_type_with_vars(
                    *arg_effect,
                    TypeSlotKind::Effect,
                    vars,
                )),
                ret_effect: Box::new(self.freshen_external_type_with_vars(
                    *ret_effect,
                    TypeSlotKind::Effect,
                    vars,
                )),
                ret: Box::new(self.freshen_external_type_with_vars(
                    *ret,
                    TypeSlotKind::Value,
                    vars,
                )),
            },
            Type::Thunk { effect, value } => Type::Thunk {
                effect: Box::new(self.freshen_external_type_with_vars(
                    *effect,
                    TypeSlotKind::Effect,
                    vars,
                )),
                value: Box::new(self.freshen_external_type_with_vars(
                    *value,
                    TypeSlotKind::Value,
                    vars,
                )),
            },
            Type::Con { path, args } => Type::Con {
                args: args
                    .into_iter()
                    .enumerate()
                    .map(|(index, arg)| {
                        let arg_context = if std_types::is_ref_effect_arg(&path, index) {
                            TypeSlotKind::Effect
                        } else {
                            TypeSlotKind::Value
                        };
                        self.freshen_external_type_with_vars(arg, arg_context, vars)
                    })
                    .collect(),
                path,
            },
            Type::Record(fields) => Type::Record(
                fields
                    .into_iter()
                    .map(|field| TypeField {
                        name: field.name,
                        value: self.freshen_external_type_with_vars(
                            field.value,
                            TypeSlotKind::Value,
                            vars,
                        ),
                        optional: field.optional,
                    })
                    .collect(),
            ),
            Type::PolyVariant(variants) => Type::PolyVariant(
                variants
                    .into_iter()
                    .map(|variant| TypeVariant {
                        name: variant.name,
                        payloads: variant
                            .payloads
                            .into_iter()
                            .map(|payload| {
                                self.freshen_external_type_with_vars(
                                    payload,
                                    TypeSlotKind::Value,
                                    vars,
                                )
                            })
                            .collect(),
                    })
                    .collect(),
            ),
            Type::Tuple(items) => Type::Tuple(
                items
                    .into_iter()
                    .map(|item| {
                        self.freshen_external_type_with_vars(item, TypeSlotKind::Value, vars)
                    })
                    .collect(),
            ),
            Type::EffectRow(items) => Type::EffectRow(
                items
                    .into_iter()
                    .map(|item| {
                        self.freshen_external_type_with_vars(item, TypeSlotKind::Effect, vars)
                    })
                    .collect(),
            ),
            Type::Stack { inner, weight } => Type::Stack {
                inner: Box::new(self.freshen_external_type_with_vars(*inner, context, vars)),
                weight,
            },
            Type::Union(left, right) => Type::Union(
                Box::new(self.freshen_external_type_with_vars(*left, context, vars)),
                Box::new(self.freshen_external_type_with_vars(*right, context, vars)),
            ),
            Type::Intersection(left, right) => Type::Intersection(
                Box::new(self.freshen_external_type_with_vars(*left, context, vars)),
                Box::new(self.freshen_external_type_with_vars(*right, context, vars)),
            ),
            Type::Any | Type::Never => ty,
        }
    }

    pub(super) fn type_open_vars_are_graph_slots(&self, ty: &Type) -> bool {
        match ty {
            Type::OpenVar(slot) => self.graph.ensure_slot(*slot).is_ok(),
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => {
                self.type_open_vars_are_graph_slots(arg)
                    && self.type_open_vars_are_graph_slots(arg_effect)
                    && self.type_open_vars_are_graph_slots(ret_effect)
                    && self.type_open_vars_are_graph_slots(ret)
            }
            Type::Thunk { effect, value } => {
                self.type_open_vars_are_graph_slots(effect)
                    && self.type_open_vars_are_graph_slots(value)
            }
            Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => args
                .iter()
                .all(|arg| self.type_open_vars_are_graph_slots(arg)),
            Type::Record(fields) => fields
                .iter()
                .all(|field| self.type_open_vars_are_graph_slots(&field.value)),
            Type::PolyVariant(variants) => variants.iter().all(|variant| {
                variant
                    .payloads
                    .iter()
                    .all(|payload| self.type_open_vars_are_graph_slots(payload))
            }),
            Type::Union(left, right) | Type::Intersection(left, right) => {
                self.type_open_vars_are_graph_slots(left)
                    && self.type_open_vars_are_graph_slots(right)
            }
            Type::Stack { inner, .. } => self.type_open_vars_are_graph_slots(inner),
            Type::Any | Type::Never => true,
        }
    }

    pub(super) fn infer_expr(
        &mut self,
        expr: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        use poly_expr::Expr as PolyExpr;
        match self.arena.expr(expr) {
            PolyExpr::Lit(lit) => Ok(lit_type(lit)),
            PolyExpr::PrimitiveOp(op) => Ok(self.primitive_type(*op, expected.as_ref())),
            PolyExpr::Var(ref_id) => {
                if expected.is_some() {
                    self.plan.mark_contextual_value_fetch(expr);
                }
                self.var_type(*ref_id, expected.as_ref())
            }
            PolyExpr::App(callee, arg) => self.apply_type(expr, *callee, *arg, expected),
            PolyExpr::RefSet(reference, value) => self.ref_set_type(*reference, *value),
            PolyExpr::Lambda(param, body) => self.lambda_type(*param, *body, expected),
            PolyExpr::Tuple(items) => self.tuple_type(items, expected.as_ref()),
            PolyExpr::Record { fields, spread } => self.record_type(fields, spread, expected),
            PolyExpr::PolyVariant(tag, payloads) => {
                self.poly_variant_type(tag, payloads, expected.as_ref())
            }
            PolyExpr::Select(base, select) => self.select_type(*base, *select, expected),
            PolyExpr::Case(scrutinee, arms) => self.case_type(expr, *scrutinee, arms, expected),
            PolyExpr::Catch(body, arms) => self.catch_type(*body, arms, expected),
            PolyExpr::Block(stmts, tail) => self.block_type(Some(expr), stmts, *tail, expected),
        }
    }

    pub(super) fn constrain_expr_boundary(
        &mut self,
        actual: Type,
        expected: Type,
    ) -> Result<(), SpecializeError> {
        if let Type::Thunk {
            value: actual_value,
            ..
        } = &actual
            && !matches!(expected, Type::Thunk { .. })
        {
            return self
                .graph
                .constrain_subtype(actual_value.as_ref().clone(), expected);
        }
        self.graph.constrain_subtype(actual, expected)
    }

    pub(super) fn apply_type(
        &mut self,
        expr: poly_expr::ExprId,
        callee: poly_expr::ExprId,
        arg: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let callee_expected = expected
            .as_ref()
            .and_then(|ret| self.primitive_spine_callee_expected(callee, ret.clone()));
        let callee_ty = self.apply_callee_type(callee, callee_expected)?;
        let (callee_value, callee_effect) = split_runtime_computation_shape(callee_ty.clone());
        if let Some((arg_ty, ret_ty)) = function_runtime_parts(&callee_value) {
            let (ret_ty, has_evaluation_effect) = self.apply_known_function_arg(
                callee,
                arg,
                arg_ty,
                ret_ty,
                callee_effect,
                expected.as_ref(),
            )?;
            if has_evaluation_effect && matches!(ret_ty, Type::Thunk { .. }) {
                self.plan.mark_raw_thunk_computation(expr);
            }
            if let Some(expected) = expected {
                self.constrain_expr_boundary(ret_ty.clone(), expected)?;
            }
            return Ok(ret_ty);
        }

        let arg_ty = self.expr(arg, None)?;
        let ret_ty = expected.unwrap_or_else(|| self.fresh_value_slot());
        let callee_expected = types::pure_function_type(arg_ty.clone(), ret_ty.clone());
        self.graph.constrain_subtype(callee_ty, callee_expected)?;
        self.expr(arg, Some(arg_ty))?;
        Ok(ret_ty)
    }

    pub(super) fn call_callee_ret_expected(
        &mut self,
        ret_ty: &Type,
        expected: Option<&Type>,
    ) -> Type {
        if runtime_value_is_never(ret_ty) {
            return ret_ty.clone();
        }
        if expected.is_none() && !type_contains_open_var(ret_ty) {
            return ret_ty.clone();
        }
        let (_, ret_effect) = split_runtime_computation_shape(ret_ty.clone());
        let expected_value = match expected {
            Some(expected) => split_runtime_computation_shape(expected.clone()).0,
            None => self.fresh_value_slot(),
        };
        types::runtime_shape(ret_effect, expected_value)
    }

    pub(super) fn apply_callee_type(
        &mut self,
        callee: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        if expected.is_none()
            && let poly_expr::Expr::Var(ref_id) = self.arena.expr(callee)
            && let Some(def) = self.arena.ref_target(*ref_id)
            && !self.local_types.contains_key(&def)
            && !self.constraining_def_types.contains_key(&def)
            && let Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                body: Some(_),
                ..
            }) = self.arena.defs.get(def)
        {
            return self.instantiate_scheme_type_only(def, scheme);
        }
        self.expr(callee, expected)
    }

    pub(super) fn apply_known_function_arg(
        &mut self,
        callee: poly_expr::ExprId,
        arg: poly_expr::ExprId,
        arg_ty: Type,
        ret_ty: Type,
        callee_effect: Type,
        expected: Option<&Type>,
    ) -> Result<(Type, bool), SpecializeError> {
        let (arg_value, arg_effect) = split_runtime_computation_shape(arg_ty.clone());
        let (callee_arg_expected, call_arg_effect) = if arg_effect.is_pure_effect() {
            let call_arg = self.expr_as_call_value(arg, arg_value)?;
            (call_arg.value, call_arg.effect)
        } else {
            self.expr(arg, Some(arg_ty))?;
            (
                types::runtime_shape(arg_effect, arg_value),
                Type::pure_effect(),
            )
        };
        let (callee_arg_value, _) = split_runtime_computation_shape(callee_arg_expected.clone());
        self.constrain_callee_pattern_defaults(callee, callee_arg_value)?;
        let expected_ret = self.call_callee_ret_expected(&ret_ty, expected);
        if !matches!(ret_ty, Type::Union(_, _) | Type::Intersection(_, _)) {
            self.graph
                .constrain_subtype(ret_ty.clone(), expected_ret.clone())?;
        }
        self.constrain_apply_callee(
            callee,
            types::pure_function_type(callee_arg_expected, expected_ret.clone()),
        )?;
        let has_evaluation_effect =
            !callee_effect.is_pure_effect() || !call_arg_effect.is_pure_effect();
        let result = self.call_result_shape(expected_ret, [callee_effect, call_arg_effect])?;
        Ok((result, has_evaluation_effect))
    }

    pub(super) fn constrain_apply_callee(
        &mut self,
        callee: poly_expr::ExprId,
        expected: Type,
    ) -> Result<(), SpecializeError> {
        if self.plan.expected(callee).is_none() {
            if self.plan.actual(callee).is_some() && self.expr_can_refine_with_expected(callee) {
                self.set_expr_expected(callee, expected.clone())?;
                let refined = self.infer_expr(callee, Some(expected.clone()))?;
                self.plan.refine_actual(callee, refined.clone())?;
                return self.constrain_expr_boundary(refined, expected);
            }
            self.expr(callee, Some(expected))?;
            return Ok(());
        }
        let actual = self.expr(callee, None)?;
        self.constrain_expr_boundary(actual, expected)
    }

    pub(super) fn expr_can_refine_with_expected(&self, expr: poly_expr::ExprId) -> bool {
        match self.arena.expr(expr) {
            poly_expr::Expr::Var(_) | poly_expr::Expr::App(_, _) => true,
            poly_expr::Expr::Select(_, select) => matches!(
                self.arena.select(*select).resolution,
                Some(poly_expr::SelectResolution::Method { .. })
                    | Some(poly_expr::SelectResolution::TypeclassMethod { .. })
            ),
            _ => false,
        }
    }

    pub(super) fn constrain_callee_pattern_defaults(
        &mut self,
        callee: poly_expr::ExprId,
        arg_ty: Type,
    ) -> Result<(), SpecializeError> {
        let Some(param) = self.callee_lambda_param(callee) else {
            return Ok(());
        };
        let local_types = self.local_types.clone();
        let result = self.constrain_pat_defaults(param, arg_ty);
        self.local_types = local_types;
        result
    }

    pub(super) fn callee_lambda_param(
        &self,
        callee: poly_expr::ExprId,
    ) -> Option<poly_expr::PatId> {
        let poly_expr::Expr::Var(ref_id) = self.arena.expr(callee) else {
            return None;
        };
        let def = self.arena.ref_target(*ref_id)?;
        let poly_expr::Def::Let {
            body: Some(body), ..
        } = self.arena.defs.get(def)?
        else {
            return None;
        };
        let poly_expr::Expr::Lambda(param, _) = self.arena.expr(*body) else {
            return None;
        };
        Some(*param)
    }

    pub(super) fn expr_as_call_value(
        &mut self,
        expr: poly_expr::ExprId,
        expected_value: Type,
    ) -> Result<CallArgument, SpecializeError> {
        let actual = if let Some(actual) = self.plan.actual(expr).cloned() {
            actual
        } else if matches!(self.arena.expr(expr), poly_expr::Expr::Var(_)) {
            self.expr(expr, None)?
        } else {
            let actual = self.infer_expr(expr, Some(expected_value.clone()))?;
            self.plan.set_actual(expr, actual.clone())?;
            actual
        };
        self.set_expr_expected(expr, expected_value.clone())?;
        let (actual_value, actual_effect) = split_runtime_computation_shape(actual);
        self.graph
            .constrain_subtype(actual_value.clone(), expected_value)?;
        Ok(CallArgument {
            value: actual_value,
            effect: actual_effect,
        })
    }

    pub(super) fn call_result_shape(
        &mut self,
        ret_ty: Type,
        effects: impl IntoIterator<Item = Type>,
    ) -> Result<Type, SpecializeError> {
        let (ret_value, ret_effect) = split_runtime_computation_shape(ret_ty);
        let effect = self.join_call_effects(std::iter::once(ret_effect).chain(effects))?;
        Ok(types::runtime_shape(effect, ret_value))
    }

    pub(super) fn join_call_effects(
        &mut self,
        effects: impl IntoIterator<Item = Type>,
    ) -> Result<Type, SpecializeError> {
        let mut effects = effects
            .into_iter()
            .filter(|effect| !effect.is_pure_effect())
            .collect::<Vec<_>>();
        match effects.len() {
            0 => Ok(Type::pure_effect()),
            1 => Ok(effects.pop().expect("checked one effect")),
            _ => {
                let effect = self.fresh_effect_slot();
                for lower in effects {
                    self.graph.constrain_subtype(lower, effect.clone())?;
                }
                Ok(effect)
            }
        }
    }

    pub(super) fn ref_set_type(
        &mut self,
        reference: poly_expr::ExprId,
        value: poly_expr::ExprId,
    ) -> Result<Type, SpecializeError> {
        let value_actual = self.expr(value, None)?;
        let (value_ty, value_effect) = split_runtime_computation_shape(value_actual);
        let update_effect = self.fresh_effect_slot();
        let reference_actual = self.expr(
            reference,
            Some(std_types::ref_type(update_effect.clone(), value_ty)),
        )?;
        let (_, reference_effect) = split_runtime_computation_shape(reference_actual);
        self.call_result_shape(
            Type::unit(),
            [value_effect, reference_effect, update_effect],
        )
    }

    pub(super) fn case_type(
        &mut self,
        expr: poly_expr::ExprId,
        scrutinee: poly_expr::ExprId,
        arms: &[poly_expr::CaseArm],
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let scrutinee_actual = self.expr(scrutinee, None)?;
        let (scrutinee_value, scrutinee_effect) = split_runtime_computation_shape(scrutinee_actual);
        let pattern_value = match (&scrutinee_value, self.case_scrutinee_pattern_type(arms)) {
            (Type::OpenVar(_), Some(pattern_type)) => pattern_type,
            _ => scrutinee_value.clone(),
        };
        self.expr(scrutinee, Some(pattern_value.clone()))?;

        let expected_value = expected
            .map(split_runtime_computation_shape)
            .map(|(value, _)| value);
        let result_value = self.fresh_value_slot();
        if let Some(expected_value) = &expected_value {
            self.graph
                .constrain_subtype(result_value.clone(), expected_value.clone())?;
        }
        let mut effects = vec![scrutinee_effect];
        for arm in arms {
            let reachable = self.case_arm_reachable(arm.pat, &pattern_value);
            self.bind_pat(arm.pat, pattern_value.clone())?;
            if let Some(guard) = arm.guard {
                let guard_actual = self.expr(guard, Some(bool_type()))?;
                if reachable {
                    effects.push(split_runtime_computation_shape(guard_actual).1);
                }
            }
            let body_expected = expected_value
                .as_ref()
                .cloned()
                .unwrap_or_else(|| result_value.clone());
            let body_actual = self.expr(arm.body, Some(body_expected))?;
            let (body_value, body_effect) = split_runtime_computation_shape(body_actual);
            if reachable {
                self.graph
                    .constrain_subtype(body_value, result_value.clone())?;
                effects.push(body_effect);
            }
        }

        let effect = self.join_call_effects(effects)?;
        let result = types::runtime_shape(effect, result_value);
        if matches!(result, Type::Thunk { .. }) {
            self.plan.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    pub(super) fn case_arm_reachable(&self, pat: poly_expr::PatId, scrutinee_ty: &Type) -> bool {
        match self.arena.pat(pat) {
            poly_expr::Pat::PolyVariant(tag, payloads) => {
                let Type::PolyVariant(variants) = scrutinee_ty else {
                    return true;
                };
                variants
                    .iter()
                    .any(|variant| variant.name == *tag && variant.payloads.len() == payloads.len())
            }
            poly_expr::Pat::Or(left, right) => {
                self.case_arm_reachable(*left, scrutinee_ty)
                    || self.case_arm_reachable(*right, scrutinee_ty)
            }
            poly_expr::Pat::As(inner, _) => self.case_arm_reachable(*inner, scrutinee_ty),
            _ => true,
        }
    }

    pub(super) fn case_scrutinee_pattern_type(
        &mut self,
        arms: &[poly_expr::CaseArm],
    ) -> Option<Type> {
        let mut variants = Vec::new();
        for arm in arms {
            self.collect_pat_poly_variants(arm.pat, &mut variants);
        }
        (!variants.is_empty()).then_some(Type::PolyVariant(variants))
    }

    pub(super) fn collect_pat_poly_variants(
        &mut self,
        pat: poly_expr::PatId,
        variants: &mut Vec<TypeVariant>,
    ) {
        match self.arena.pat(pat) {
            poly_expr::Pat::PolyVariant(tag, payloads) => {
                if variants
                    .iter()
                    .any(|variant| variant.name == *tag && variant.payloads.len() == payloads.len())
                {
                    return;
                }
                variants.push(TypeVariant {
                    name: tag.clone(),
                    payloads: payloads.iter().map(|_| self.fresh_value_slot()).collect(),
                });
            }
            poly_expr::Pat::Or(left, right) => {
                self.collect_pat_poly_variants(*left, variants);
                self.collect_pat_poly_variants(*right, variants);
            }
            poly_expr::Pat::As(inner, _) => {
                self.collect_pat_poly_variants(*inner, variants);
            }
            poly_expr::Pat::Lit(_)
            | poly_expr::Pat::Wild
            | poly_expr::Pat::Var(_)
            | poly_expr::Pat::Tuple(_)
            | poly_expr::Pat::List { .. }
            | poly_expr::Pat::Record { .. }
            | poly_expr::Pat::Con(_, _)
            | poly_expr::Pat::Ref(_) => {}
        }
    }

    pub(super) fn local_let_value_can_defer(&self, value: poly_expr::ExprId) -> bool {
        matches!(self.arena.expr(value), poly_expr::Expr::Lambda(_, _))
    }
}
