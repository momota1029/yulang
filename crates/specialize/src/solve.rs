//! `mono` instance 内で erased expression に型を割り当てる作業状態。
//!
//! `poly` は式 node ごとの型を保持しない。ここでは instance/root ごとに主型と erased IR から
//! use-site の concrete 型を再構成し、mono IR へ写す段階が参照する plan だけを残す。

use std::collections::{HashMap, HashSet};

use mono::{Type, TypeField, TypeVariant};
use poly::expr as poly_expr;

use crate::{
    ExprTypeRole, SpecializeError, convert_def, def_kind, lit_type, roles, std_types, types,
};

#[derive(Debug, Clone, Default)]
pub(crate) struct ExprTypePlan {
    types: HashMap<poly_expr::ExprId, ExprTypes>,
    raw_thunk_computations: HashSet<poly_expr::ExprId>,
}

impl ExprTypePlan {
    pub(crate) fn actual_type_of(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.types
            .get(&expr)
            .and_then(|types| types.actual.as_ref())
    }

    pub(crate) fn boundary(&self, expr: poly_expr::ExprId) -> Option<ExprTypeBoundary<'_>> {
        let types = self.types.get(&expr)?;
        Some(ExprTypeBoundary {
            actual: types.actual.as_ref()?,
            expected: types.expected.as_ref()?,
        })
    }

    pub(crate) fn is_raw_thunk_computation(&self, expr: poly_expr::ExprId) -> bool {
        self.raw_thunk_computations.contains(&expr)
    }

    fn set_actual(&mut self, expr: poly_expr::ExprId, ty: Type) -> Result<(), SpecializeError> {
        self.types
            .entry(expr)
            .or_default()
            .set(expr, ExprTypeRole::Actual, ty)
    }

    fn set_expected(&mut self, expr: poly_expr::ExprId, ty: Type) -> Result<(), SpecializeError> {
        self.types
            .entry(expr)
            .or_default()
            .set(expr, ExprTypeRole::Expected, ty)
    }

    fn mark_raw_thunk_computation(&mut self, expr: poly_expr::ExprId) {
        self.raw_thunk_computations.insert(expr);
    }

    fn actual(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.types
            .get(&expr)
            .and_then(|types| types.actual.as_ref())
    }

    fn finalize(&self, graph: &ConstraintGraph<'_>) -> Result<Self, SpecializeError> {
        let mut resolver = TypeResolver::new(graph);
        let mut out = Self {
            types: HashMap::new(),
            raw_thunk_computations: self.raw_thunk_computations.clone(),
        };
        for (expr, types) in &self.types {
            if let Some(actual) = &types.actual {
                out.set_actual(*expr, resolver.resolve(actual)?)?;
            }
            if let Some(expected) = &types.expected {
                out.set_expected(*expr, resolver.resolve(expected)?)?;
            }
        }
        Ok(out)
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct ExprTypeBoundary<'a> {
    pub actual: &'a Type,
    pub expected: &'a Type,
}

#[derive(Debug, Clone, Default)]
struct ExprTypes {
    actual: Option<Type>,
    expected: Option<Type>,
}

impl ExprTypes {
    fn set(
        &mut self,
        expr: poly_expr::ExprId,
        role: ExprTypeRole,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        let slot = match role {
            ExprTypeRole::Actual => &mut self.actual,
            ExprTypeRole::Expected => &mut self.expected,
        };
        if let Some(existing) = slot {
            if existing == &ty {
                return Ok(());
            }
            return Err(SpecializeError::ConflictingExprType {
                expr: expr.0,
                role,
                existing: existing.clone(),
                incoming: ty,
            });
        }
        *slot = Some(ty);
        Ok(())
    }
}

pub(crate) fn solve_expr(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
    expected: Option<&Type>,
) -> Result<ExprTypePlan, SpecializeError> {
    let mut solver = ExprTypeSolver {
        arena,
        graph: ConstraintGraph::new(arena),
        plan: ExprTypePlan::default(),
        local_types: HashMap::new(),
    };
    solver.expr(expr, expected.cloned())?;
    solver.graph.resolve_role_demands()?;
    solver.plan.finalize(&solver.graph)
}

struct ExprTypeSolver<'a> {
    arena: &'a poly_expr::Arena,
    graph: ConstraintGraph<'a>,
    plan: ExprTypePlan,
    local_types: HashMap<poly_expr::DefId, Type>,
}

impl<'a> ExprTypeSolver<'a> {
    fn expr(
        &mut self,
        expr: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        if let Some(expected) = expected {
            self.plan.set_expected(expr, expected.clone())?;
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

    fn infer_expr(
        &mut self,
        expr: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        use poly_expr::Expr as PolyExpr;
        match self.arena.expr(expr) {
            PolyExpr::Lit(lit) => Ok(lit_type(lit)),
            PolyExpr::PrimitiveOp(op) => Ok(self.primitive_type(*op, expected.as_ref())),
            PolyExpr::Var(ref_id) => self.var_type(*ref_id),
            PolyExpr::App(callee, arg) => self.apply_type(expr, *callee, *arg, expected),
            PolyExpr::RefSet(reference, value) => {
                self.expr(*reference, None)?;
                self.expr(*value, None)?;
                Ok(Type::unit())
            }
            PolyExpr::Lambda(param, body) => self.lambda_type(*param, *body, expected),
            PolyExpr::Tuple(items) => self.tuple_type(items, expected.as_ref()),
            PolyExpr::Record { fields, spread } => self.record_type(fields, spread, expected),
            PolyExpr::PolyVariant(tag, payloads) => {
                self.poly_variant_type(tag, payloads, expected.as_ref())
            }
            PolyExpr::Select(base, select) => self.select_type(*base, *select, expected),
            PolyExpr::Case(scrutinee, arms) => self.case_type(expr, *scrutinee, arms, expected),
            PolyExpr::Catch(body, arms) => self.catch_type(*body, arms, expected),
            PolyExpr::Block(stmts, tail) => self.block_type(stmts, *tail, expected),
        }
    }

    fn constrain_expr_boundary(
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

    fn apply_type(
        &mut self,
        expr: poly_expr::ExprId,
        callee: poly_expr::ExprId,
        arg: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let callee_expected = expected
            .as_ref()
            .and_then(|ret| self.primitive_spine_callee_expected(callee, ret.clone()));
        let callee_ty = self.expr(callee, callee_expected)?;
        let (callee_value, callee_effect) = split_runtime_computation_shape(callee_ty.clone());
        if let Some((arg_ty, ret_ty)) = function_runtime_parts(&callee_value) {
            if !callee_effect.is_pure_effect() {
                self.plan.set_expected(callee, callee_value)?;
            }
            let (ret_ty, has_evaluation_effect) =
                self.apply_known_function_arg(arg, arg_ty, ret_ty, callee_effect)?;
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

    fn apply_known_function_arg(
        &mut self,
        arg: poly_expr::ExprId,
        arg_ty: Type,
        ret_ty: Type,
        callee_effect: Type,
    ) -> Result<(Type, bool), SpecializeError> {
        let (arg_value, arg_effect) = split_runtime_computation_shape(arg_ty.clone());
        let call_arg_effect = if arg_effect.is_pure_effect() {
            self.expr_as_call_value(arg, arg_value)?
        } else {
            self.expr(arg, Some(arg_ty))?;
            Type::pure_effect()
        };
        let has_evaluation_effect =
            !callee_effect.is_pure_effect() || !call_arg_effect.is_pure_effect();
        let result = self.call_result_shape(ret_ty, [callee_effect, call_arg_effect])?;
        Ok((result, has_evaluation_effect))
    }

    fn expr_as_call_value(
        &mut self,
        expr: poly_expr::ExprId,
        expected_value: Type,
    ) -> Result<Type, SpecializeError> {
        self.plan.set_expected(expr, expected_value.clone())?;
        let actual = if let Some(actual) = self.plan.actual(expr).cloned() {
            actual
        } else {
            let actual = self.infer_expr(expr, Some(expected_value.clone()))?;
            self.plan.set_actual(expr, actual.clone())?;
            actual
        };
        let (actual_value, actual_effect) = split_runtime_computation_shape(actual);
        self.graph.constrain_subtype(actual_value, expected_value)?;
        Ok(actual_effect)
    }

    fn call_result_shape(
        &mut self,
        ret_ty: Type,
        effects: impl IntoIterator<Item = Type>,
    ) -> Result<Type, SpecializeError> {
        let (ret_value, ret_effect) = split_runtime_computation_shape(ret_ty);
        let effect = self.join_call_effects(std::iter::once(ret_effect).chain(effects))?;
        Ok(types::runtime_shape(effect, ret_value))
    }

    fn join_call_effects(
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

    fn case_type(
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

        let expected_result = expected.unwrap_or_else(|| self.fresh_value_slot());
        let (result_value, _) = split_runtime_computation_shape(expected_result);
        let mut effects = vec![scrutinee_effect];
        for arm in arms {
            self.bind_pat(arm.pat, pattern_value.clone())?;
            if let Some(guard) = arm.guard {
                let guard_actual = self.expr(guard, Some(bool_type()))?;
                effects.push(split_runtime_computation_shape(guard_actual).1);
            }
            let body_actual = self.expr(arm.body, Some(result_value.clone()))?;
            effects.push(split_runtime_computation_shape(body_actual).1);
        }

        let effect = self.join_call_effects(effects)?;
        let result = types::runtime_shape(effect, result_value);
        if matches!(result, Type::Thunk { .. }) {
            self.plan.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    fn case_scrutinee_pattern_type(&mut self, arms: &[poly_expr::CaseArm]) -> Option<Type> {
        let mut variants = Vec::new();
        for arm in arms {
            self.collect_pat_poly_variants(arm.pat, &mut variants);
        }
        (!variants.is_empty()).then_some(Type::PolyVariant(variants))
    }

    fn collect_pat_poly_variants(
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

    fn primitive_spine_callee_expected(
        &self,
        callee: poly_expr::ExprId,
        ret: Type,
    ) -> Option<Type> {
        let (op, applied) = self.primitive_spine(callee)?;
        let ret = runtime_value_shape(&ret).clone();
        let arg = primitive_spine_arg_type(op, applied, &ret)?;
        Some(types::pure_function_type(arg, ret))
    }

    fn primitive_spine(&self, expr: poly_expr::ExprId) -> Option<(poly_expr::PrimitiveOp, usize)> {
        match self.arena.expr(expr) {
            poly_expr::Expr::PrimitiveOp(op) => Some((*op, 0)),
            poly_expr::Expr::App(callee, _) => {
                let (op, applied) = self.primitive_spine(*callee)?;
                Some((op, applied + 1))
            }
            _ => None,
        }
    }

    fn catch_type(
        &mut self,
        body: poly_expr::ExprId,
        arms: &[poly_expr::CatchArm],
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_result = expected.unwrap_or_else(|| self.fresh_value_slot());
        let (result, _) = split_runtime_computation_shape(expected_result);
        let body_actual = self.expr(body, None)?;
        let (scrutinee_value, scrutinee_effect) = split_runtime_computation_shape(body_actual);
        self.expr(body, Some(scrutinee_value.clone()))?;
        for arm in arms {
            self.bind_catch_arm(arm, scrutinee_value.clone(), scrutinee_effect.clone())?;
            if let Some(guard) = arm.guard {
                self.expr(guard, Some(bool_type()))?;
            }
            self.expr(arm.body, Some(result.clone()))?;
        }
        Ok(result)
    }

    fn bind_catch_arm(
        &mut self,
        arm: &poly_expr::CatchArm,
        scrutinee_value: Type,
        scrutinee_effect: Type,
    ) -> Result<(), SpecializeError> {
        let Some(continuation) = arm.continuation else {
            self.bind_pat(arm.pat, scrutinee_value)?;
            return Ok(());
        };

        let operation =
            self.catch_operation_types(arm.operation.as_ref(), scrutinee_effect.clone())?;
        self.bind_pat(arm.pat, operation.payload)?;
        let continuation_ret = types::runtime_shape(scrutinee_effect, scrutinee_value);
        self.bind_pat(
            continuation,
            types::pure_function_type(operation.continuation_input, continuation_ret),
        )
    }

    fn catch_operation_types(
        &mut self,
        operation: Option<&poly_expr::CatchOperation>,
        scrutinee_effect: Type,
    ) -> Result<CatchOperationTypes, SpecializeError> {
        let Some(operation) = operation else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
            });
        };
        let Some(def) = operation.def else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
            });
        };
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
            });
        };
        let operation_ty = self.instantiate_scheme(def, scheme)?;
        let Some((payload, ret)) = function_runtime_parts(&operation_ty) else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
            });
        };
        let (continuation_input, operation_effect) = split_runtime_computation_shape(ret);
        self.constrain_operation_effect_to_scrutinee(operation_effect, scrutinee_effect)?;
        Ok(CatchOperationTypes {
            payload,
            continuation_input,
        })
    }

    fn constrain_operation_effect_to_scrutinee(
        &mut self,
        operation_effect: Type,
        scrutinee_effect: Type,
    ) -> Result<(), SpecializeError> {
        if let (Type::EffectRow(operation_items), Type::EffectRow(scrutinee_items)) =
            (&operation_effect, &scrutinee_effect)
        {
            let mut constrained = false;
            for operation_item in operation_items {
                let Some(scrutinee_item) =
                    matching_effect_row_item(operation_item, scrutinee_items)
                else {
                    continue;
                };
                self.graph
                    .constrain_subtype(operation_item.clone(), scrutinee_item.clone())?;
                self.graph
                    .constrain_subtype(scrutinee_item.clone(), operation_item.clone())?;
                constrained = true;
            }
            if constrained {
                return Ok(());
            }
        }
        self.graph
            .constrain_subtype(operation_effect.clone(), scrutinee_effect.clone())?;
        self.graph
            .constrain_subtype(scrutinee_effect, operation_effect)
    }

    fn lambda_type(
        &mut self,
        param: poly_expr::PatId,
        body: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let function = match expected {
            Some(Type::Fun { .. }) => expected.expect("checked as function"),
            Some(other) => {
                self.expr(body, None)?;
                return Ok(other);
            }
            None => types::pure_function_type(self.fresh_value_slot(), self.fresh_value_slot()),
        };
        let Type::Fun { arg, ret, .. } = &function else {
            unreachable!("function shape checked above");
        };
        self.bind_pat(param, arg.as_ref().clone())?;
        self.expr(body, Some(ret.as_ref().clone()))?;
        Ok(function)
    }

    fn tuple_type(
        &mut self,
        items: &[poly_expr::ExprId],
        expected: Option<&Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_items = match expected {
            Some(Type::Tuple(expected_items)) if expected_items.len() == items.len() => {
                Some(expected_items.as_slice())
            }
            _ => None,
        };
        let mut item_types = Vec::with_capacity(items.len());
        for (index, item) in items.iter().enumerate() {
            let expected = expected_items.and_then(|items| items.get(index)).cloned();
            item_types.push(self.expr(*item, expected)?);
        }
        Ok(expected.cloned().unwrap_or(Type::Tuple(item_types)))
    }

    fn block_type(
        &mut self,
        stmts: &[poly_expr::Stmt],
        tail: Option<poly_expr::ExprId>,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        for stmt in stmts {
            match stmt {
                poly_expr::Stmt::Let(_, pat, value) => {
                    let value_ty = self.expr(*value, None)?;
                    self.bind_pat(*pat, value_ty)?;
                }
                poly_expr::Stmt::Expr(value) => {
                    self.expr(*value, None)?;
                }
                poly_expr::Stmt::Module(_, body) => {
                    self.block_type(body, None, None)?;
                }
            }
        }
        match tail {
            Some(tail) => self.expr(tail, expected),
            None => Ok(Type::unit()),
        }
    }

    fn record_type(
        &mut self,
        fields: &[(String, poly_expr::ExprId)],
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_fields = match &expected {
            Some(Type::Record(fields)) => Some(fields.as_slice()),
            _ => None,
        };
        let mut typed_fields = Vec::with_capacity(fields.len());
        for (name, value) in fields {
            let field_expected = expected_fields
                .and_then(|fields| record_field_type(fields, name))
                .map(|field| field.value.clone());
            typed_fields.push(TypeField {
                name: name.clone(),
                value: self.expr(*value, field_expected)?,
                optional: false,
            });
        }

        match spread {
            poly_expr::RecordSpread::None => Ok(Type::Record(typed_fields)),
            poly_expr::RecordSpread::Head(expr) => {
                let spread = self.expr(*expr, None)?;
                Ok(match spread {
                    Type::Record(spread_fields) => {
                        Type::Record(join_record_fields(spread_fields, typed_fields))
                    }
                    _ => expected.unwrap_or_else(|| self.fresh_value_slot()),
                })
            }
            poly_expr::RecordSpread::Tail(expr) => {
                let spread = self.expr(*expr, None)?;
                Ok(match spread {
                    Type::Record(spread_fields) => {
                        Type::Record(join_record_fields(typed_fields, spread_fields))
                    }
                    _ => expected.unwrap_or_else(|| self.fresh_value_slot()),
                })
            }
        }
    }

    fn poly_variant_type(
        &mut self,
        tag: &str,
        payloads: &[poly_expr::ExprId],
        expected: Option<&Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_variant = match expected {
            Some(Type::PolyVariant(variants)) => variants
                .iter()
                .find(|variant| variant.name == tag && variant.payloads.len() == payloads.len()),
            _ => None,
        };
        let mut typed_payloads = Vec::with_capacity(payloads.len());
        for (index, payload) in payloads.iter().enumerate() {
            let payload_expected =
                expected_variant.and_then(|variant| variant.payloads.get(index).cloned());
            typed_payloads.push(self.expr(*payload, payload_expected)?);
        }
        Ok(Type::PolyVariant(vec![TypeVariant {
            name: tag.to_string(),
            payloads: typed_payloads,
        }]))
    }

    fn select_type(
        &mut self,
        base: poly_expr::ExprId,
        select: poly_expr::SelectId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let select = self.arena.select(select);
        match select.resolution {
            Some(poly_expr::SelectResolution::RecordField) => {
                self.record_select_type(base, &select.name, expected)
            }
            Some(poly_expr::SelectResolution::Method { def }) => {
                self.method_select_type(base, def, expected)
            }
            Some(poly_expr::SelectResolution::TypeclassMethod { member }) => {
                self.method_select_type(base, member, expected)
            }
            None => {
                self.expr(base, None)?;
                Ok(expected.unwrap_or_else(|| self.fresh_value_slot()))
            }
        }
    }

    fn record_select_type(
        &mut self,
        base: poly_expr::ExprId,
        name: &str,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let base_ty = self.expr(base, None)?;
        if let Type::Record(fields) = &base_ty
            && let Some(field) = record_field_type(fields, name)
        {
            return Ok(field.value.clone());
        }

        let field_ty = expected.unwrap_or_else(|| self.fresh_value_slot());
        self.expr(
            base,
            Some(Type::Record(vec![TypeField {
                name: name.to_string(),
                value: field_ty.clone(),
                optional: false,
            }])),
        )?;
        Ok(field_ty)
    }

    fn method_select_type(
        &mut self,
        base: poly_expr::ExprId,
        def: poly_expr::DefId,
        _expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            self.expr(base, None)?;
            return Ok(self.fresh_value_slot());
        };
        let method_ty = self.instantiate_scheme(def, scheme)?;
        let Some((receiver_ty, result_ty)) = function_runtime_parts(&method_ty) else {
            self.expr(base, None)?;
            return Ok(self.fresh_value_slot());
        };
        self.expr(base, Some(receiver_ty))?;
        Ok(result_ty)
    }

    fn bind_pat(&mut self, pat: poly_expr::PatId, ty: Type) -> Result<(), SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match self.arena.pat(pat) {
            PolyPat::Wild => {}
            PolyPat::Lit(lit) => {
                let lit_ty = lit_type(lit);
                self.graph.constrain_subtype(lit_ty.clone(), ty.clone())?;
                self.graph.constrain_subtype(ty, lit_ty)?;
            }
            PolyPat::Var(def) => {
                self.local_types.insert(*def, ty);
            }
            PolyPat::As(inner, def) => {
                self.local_types.insert(*def, ty.clone());
                self.bind_pat(*inner, ty)?;
            }
            PolyPat::Tuple(items) => {
                if let Type::Tuple(item_types) = ty {
                    for (item, item_ty) in items.iter().zip(item_types) {
                        self.bind_pat(*item, item_ty)?;
                    }
                }
            }
            PolyPat::List {
                prefix,
                spread,
                suffix,
            } => {
                self.bind_list_pat(prefix, *spread, suffix, ty)?;
            }
            PolyPat::Record { fields, spread } => {
                self.bind_record_pat(fields, spread, ty)?;
            }
            PolyPat::Con(ref_id, payloads) => {
                self.bind_constructor_pat(*ref_id, payloads, ty)?;
            }
            PolyPat::PolyVariant(tag, payloads) => {
                if let Type::PolyVariant(variants) = ty {
                    match variants.iter().find(|variant| variant.name == *tag) {
                        Some(variant) => {
                            for (payload, payload_ty) in payloads.iter().zip(&variant.payloads) {
                                self.bind_pat(*payload, payload_ty.clone())?;
                            }
                        }
                        None => {
                            for payload in payloads {
                                self.bind_pat(*payload, Type::Never)?;
                            }
                        }
                    }
                }
            }
            PolyPat::Or(left, right) => {
                self.bind_pat(*left, ty.clone())?;
                self.bind_pat(*right, ty)?;
            }
            PolyPat::Ref(ref_id) => {
                self.bind_ref_pat(*ref_id, ty)?;
            }
        }
        Ok(())
    }

    fn bind_list_pat(
        &mut self,
        prefix: &[poly_expr::PatId],
        spread: Option<poly_expr::PatId>,
        suffix: &[poly_expr::PatId],
        ty: Type,
    ) -> Result<(), SpecializeError> {
        let item_ty = list_item_type(&ty).unwrap_or_else(|| self.fresh_value_slot());
        for item in prefix.iter().chain(suffix) {
            self.bind_pat(*item, item_ty.clone())?;
        }
        if let Some(spread) = spread {
            self.bind_pat(spread, ty)?;
        }
        Ok(())
    }

    fn bind_record_pat(
        &mut self,
        fields: &[(String, poly_expr::PatId)],
        spread: &poly_expr::RecordSpread<poly_expr::DefId>,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        let Type::Record(record_fields) = ty else {
            for (_, pat) in fields {
                let field_ty = self.fresh_value_slot();
                self.bind_pat(*pat, field_ty)?;
            }
            if let Some(def) = record_spread_def(spread) {
                let spread_ty = self.fresh_value_slot();
                self.local_types.insert(def, spread_ty);
            }
            return Ok(());
        };

        for (name, pat) in fields {
            let field_ty = record_field_type(&record_fields, name)
                .map(|field| field.value.clone())
                .unwrap_or_else(|| self.fresh_value_slot());
            self.bind_pat(*pat, field_ty)?;
        }
        if let Some(def) = record_spread_def(spread) {
            let captured = record_fields
                .into_iter()
                .filter(|field| !fields.iter().any(|(name, _)| name == &field.name))
                .collect::<Vec<_>>();
            self.local_types.insert(def, Type::Record(captured));
        }
        Ok(())
    }

    fn bind_constructor_pat(
        &mut self,
        ref_id: poly_expr::RefId,
        payloads: &[poly_expr::PatId],
        scrutinee_ty: Type,
    ) -> Result<(), SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            return Ok(());
        };
        let constructor_ty = self.instantiate_scheme(def, scheme)?;
        let Some((payload_tys, owner_ty)) = split_function_spine(constructor_ty, payloads.len())
        else {
            return Ok(());
        };
        self.graph
            .constrain_subtype(owner_ty.clone(), scrutinee_ty.clone())?;
        self.graph.constrain_subtype(scrutinee_ty, owner_ty)?;
        for (payload, payload_ty) in payloads.iter().zip(payload_tys) {
            self.bind_pat(*payload, payload_ty)?;
        }
        Ok(())
    }

    fn bind_ref_pat(
        &mut self,
        ref_id: poly_expr::RefId,
        scrutinee_ty: Type,
    ) -> Result<(), SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if let Some(ref_ty) = self.local_types.get(&def).cloned() {
            self.graph
                .constrain_subtype(ref_ty.clone(), scrutinee_ty.clone())?;
            self.graph.constrain_subtype(scrutinee_ty, ref_ty)?;
            return Ok(());
        }
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                ..
            }) => {
                let ref_ty = self.instantiate_scheme(def, scheme)?;
                self.graph
                    .constrain_subtype(ref_ty.clone(), scrutinee_ty.clone())?;
                self.graph.constrain_subtype(scrutinee_ty, ref_ty)
            }
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => Ok(()),
            _ => Ok(()),
        }
    }

    fn var_type(&mut self, ref_id: poly_expr::RefId) -> Result<Type, SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if let Some(local_ty) = self.local_types.get(&def).cloned() {
            return Ok(local_ty);
        }
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                ..
            }) => self.instantiate_scheme(def, scheme),
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => {
                Ok(self.fresh_value_slot())
            }
            Some(poly_expr::Def::Let { scheme: None, .. }) => Err(SpecializeError::MissingScheme {
                def: convert_def(def),
            }),
            Some(other) => Err(SpecializeError::UnsupportedDefKind {
                def: convert_def(def),
                kind: def_kind(other),
            }),
            None => Err(SpecializeError::MissingDef {
                def: convert_def(def),
            }),
        }
    }

    fn instantiate_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let mut slots = Vec::new();
        let instantiated =
            types::instantiate_scheme_with_fresh_and_roles(self.arena, def, scheme, |kind| {
                let slot = match kind {
                    types::SchemeQuantifierKind::Value => self.fresh_value_slot(),
                    types::SchemeQuantifierKind::Effect => self.fresh_effect_slot(),
                };
                slots.push(slot.clone());
                slot
            })?;
        for slot in slots {
            if let Type::OpenVar(slot) = slot {
                self.graph.ensure_slot(slot)?;
            }
        }
        self.graph.add_role_demands(instantiated.role_predicates);
        self.graph
            .constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    fn fresh_value_slot(&mut self) -> Type {
        self.graph.fresh_slot(TypeSlotKind::Value)
    }

    fn fresh_effect_slot(&mut self) -> Type {
        self.graph.fresh_slot(TypeSlotKind::Effect)
    }

    fn primitive_type(&mut self, op: poly_expr::PrimitiveOp, expected: Option<&Type>) -> Type {
        if let Some(expected) = expected {
            return self.primitive_type_from_expected(op, expected);
        }

        use poly_expr::PrimitiveOp;
        match op {
            PrimitiveOp::YadaYada => Type::Never,
            PrimitiveOp::BoolNot => unary_type(bool_type(), bool_type()),
            PrimitiveOp::BoolEq => binary_type(bool_type(), bool_type()),
            PrimitiveOp::ListEmpty => {
                let item = self.fresh_value_slot();
                unary_type(Type::unit(), list_type(item))
            }
            PrimitiveOp::ListSingleton => {
                let item = self.fresh_value_slot();
                unary_type(item.clone(), list_type(item))
            }
            PrimitiveOp::ListLen => {
                let item = self.fresh_value_slot();
                unary_type(list_type(item), int_type())
            }
            PrimitiveOp::ListMerge => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(vec![list.clone(), list.clone()], list)
            }
            PrimitiveOp::ListIndex => {
                let item = self.fresh_value_slot();
                function_type(vec![list_type(item.clone()), int_type()], item)
            }
            PrimitiveOp::ListIndexRange => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(vec![list.clone(), range_type()], list)
            }
            PrimitiveOp::ListSplice => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(vec![list.clone(), range_type(), list.clone()], list)
            }
            PrimitiveOp::ListIndexRangeRaw => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(vec![list.clone(), int_type(), int_type()], list)
            }
            PrimitiveOp::ListSpliceRaw => {
                let item = self.fresh_value_slot();
                let list = list_type(item);
                function_type(
                    vec![list.clone(), int_type(), int_type(), list.clone()],
                    list,
                )
            }
            PrimitiveOp::ListViewRaw => {
                let item = self.fresh_value_slot();
                unary_type(list_type(item.clone()), list_view_type(item))
            }
            PrimitiveOp::StringLen | PrimitiveOp::StringLineCount => {
                unary_type(str_type(), int_type())
            }
            PrimitiveOp::StringIndex => function_type(vec![str_type(), int_type()], char_type()),
            PrimitiveOp::StringIndexRange => {
                function_type(vec![str_type(), range_type()], str_type())
            }
            PrimitiveOp::StringSplice => {
                function_type(vec![str_type(), range_type(), str_type()], str_type())
            }
            PrimitiveOp::StringIndexRangeRaw => {
                function_type(vec![str_type(), int_type(), int_type()], str_type())
            }
            PrimitiveOp::StringSpliceRaw => function_type(
                vec![str_type(), int_type(), int_type(), str_type()],
                str_type(),
            ),
            PrimitiveOp::StringLineRange => {
                function_type(vec![str_type(), int_type()], range_type())
            }
            PrimitiveOp::IntAdd
            | PrimitiveOp::IntSub
            | PrimitiveOp::IntMul
            | PrimitiveOp::IntDiv
            | PrimitiveOp::IntMod => binary_type(int_type(), int_type()),
            PrimitiveOp::IntEq
            | PrimitiveOp::IntLt
            | PrimitiveOp::IntLe
            | PrimitiveOp::IntGt
            | PrimitiveOp::IntGe => binary_type(int_type(), bool_type()),
            PrimitiveOp::FloatAdd
            | PrimitiveOp::FloatSub
            | PrimitiveOp::FloatMul
            | PrimitiveOp::FloatDiv => binary_type(float_type(), float_type()),
            PrimitiveOp::FloatEq
            | PrimitiveOp::FloatLt
            | PrimitiveOp::FloatLe
            | PrimitiveOp::FloatGt
            | PrimitiveOp::FloatGe => binary_type(float_type(), bool_type()),
            PrimitiveOp::StringEq => binary_type(str_type(), bool_type()),
            PrimitiveOp::StringConcat => binary_type(str_type(), str_type()),
            PrimitiveOp::StringToBytes => unary_type(str_type(), bytes_type()),
            PrimitiveOp::CharEq => binary_type(char_type(), bool_type()),
            PrimitiveOp::CharToString => unary_type(char_type(), str_type()),
            PrimitiveOp::CharIsWhitespace
            | PrimitiveOp::CharIsPunctuation
            | PrimitiveOp::CharIsWord => unary_type(char_type(), bool_type()),
            PrimitiveOp::BytesLen => unary_type(bytes_type(), int_type()),
            PrimitiveOp::BytesEq => binary_type(bytes_type(), bool_type()),
            PrimitiveOp::BytesConcat => binary_type(bytes_type(), bytes_type()),
            PrimitiveOp::BytesIndex => function_type(vec![bytes_type(), int_type()], int_type()),
            PrimitiveOp::BytesIndexRange => {
                function_type(vec![bytes_type(), range_type()], bytes_type())
            }
            PrimitiveOp::BytesToUtf8Raw => {
                unary_type(bytes_type(), Type::Tuple(vec![str_type(), int_type()]))
            }
            PrimitiveOp::BytesToPath => unary_type(bytes_type(), path_type()),
            PrimitiveOp::PathToBytes => unary_type(path_type(), bytes_type()),
            PrimitiveOp::IntToString | PrimitiveOp::IntToHex | PrimitiveOp::IntToUpperHex => {
                unary_type(int_type(), str_type())
            }
            PrimitiveOp::FloatToString => unary_type(float_type(), str_type()),
            PrimitiveOp::BoolToString => unary_type(bool_type(), str_type()),
        }
    }

    fn primitive_type_from_expected(
        &mut self,
        op: poly_expr::PrimitiveOp,
        expected: &Type,
    ) -> Type {
        let _ = op;
        expected.clone()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeSlotKind {
    Value,
    Effect,
}

struct CatchOperationTypes {
    payload: Type,
    continuation_input: Type,
}

impl TypeSlotKind {
    fn default_type(self) -> Type {
        match self {
            Self::Value => Type::unit(),
            Self::Effect => Type::pure_effect(),
        }
    }
}

struct ConstraintGraph<'a> {
    arena: &'a poly_expr::Arena,
    slots: Vec<TypeSlot>,
    role_demands: Vec<types::InstantiatedRolePredicate>,
}

impl<'a> ConstraintGraph<'a> {
    fn new(arena: &'a poly_expr::Arena) -> Self {
        Self {
            arena,
            slots: Vec::new(),
            role_demands: Vec::new(),
        }
    }

    fn fresh_slot(&mut self, kind: TypeSlotKind) -> Type {
        let id = self.slots.len() as u32;
        self.slots.push(TypeSlot::new(kind));
        Type::OpenVar(id)
    }

    fn ensure_slot(&self, slot: u32) -> Result<(), SpecializeError> {
        if (slot as usize) < self.slots.len() {
            return Ok(());
        }
        Err(SpecializeError::InvalidTypeSlot { slot })
    }

    fn add_role_demands(
        &mut self,
        demands: impl IntoIterator<Item = types::InstantiatedRolePredicate>,
    ) {
        self.role_demands.extend(demands);
    }

    fn constrain_recursive_bounds(
        &mut self,
        bounds: impl IntoIterator<Item = types::InstantiatedRecursiveBound>,
    ) -> Result<(), SpecializeError> {
        for bound in bounds {
            self.constrain_subtype(bound.lower, bound.value.clone())?;
            self.constrain_subtype(bound.value, bound.upper)?;
        }
        Ok(())
    }

    fn resolve_role_demands(&mut self) -> Result<(), SpecializeError> {
        let mut applied = HashSet::new();
        loop {
            let mut progressed = false;
            let demands = self.role_demands.clone();
            for demand in demands {
                if applied.contains(&demand) {
                    continue;
                }
                if self.try_apply_role_demand(&demand)? {
                    applied.insert(demand);
                    progressed = true;
                }
            }
            if !progressed {
                return Ok(());
            }
        }
    }

    fn try_apply_role_demand(
        &mut self,
        demand: &types::InstantiatedRolePredicate,
    ) -> Result<bool, SpecializeError> {
        let Some(input_types) = self.resolve_role_input_types(demand)? else {
            return Ok(false);
        };
        let applications = self
            .arena
            .role_impls
            .candidates(&demand.role)
            .iter()
            .filter_map(|candidate| {
                roles::candidate_application(&self.arena.typ, demand, candidate, &input_types)
            })
            .collect::<Vec<_>>();
        let [application] = applications.as_slice() else {
            return Ok(false);
        };

        for (lower, candidate, upper) in &application.associated {
            self.constrain_subtype(lower.clone(), candidate.clone())?;
            self.constrain_subtype(candidate.clone(), upper.clone())?;
        }
        self.add_role_demands(application.prerequisites.clone());
        Ok(true)
    }

    fn resolve_role_input_types(
        &self,
        demand: &types::InstantiatedRolePredicate,
    ) -> Result<Option<Vec<Type>>, SpecializeError> {
        let mut resolver = TypeResolver::new(self);
        let mut inputs = Vec::with_capacity(demand.inputs.len());
        for input in &demand.inputs {
            let Some(ty) = resolve_role_arg_exact_type(self, &mut resolver, input)? else {
                return Ok(None);
            };
            inputs.push(ty);
        }
        Ok(Some(inputs))
    }

    fn slot(&self, slot: u32) -> Result<&TypeSlot, SpecializeError> {
        self.slots
            .get(slot as usize)
            .ok_or(SpecializeError::InvalidTypeSlot { slot })
    }

    fn slot_is_value(&self, slot: u32) -> bool {
        self.slots
            .get(slot as usize)
            .is_some_and(|slot| slot.kind == TypeSlotKind::Value)
    }

    fn constrain_subtype(&mut self, lower: Type, upper: Type) -> Result<(), SpecializeError> {
        if lower == upper {
            return Ok(());
        }
        match (lower, upper) {
            (Type::Never, _) | (_, Type::Any) => Ok(()),
            (Type::OpenVar(lower), Type::OpenVar(upper)) => self.add_edge(lower, upper),
            (Type::Thunk { value, .. }, Type::OpenVar(slot)) if self.slot_is_value(slot) => {
                self.constrain_subtype(*value, Type::OpenVar(slot))
            }
            (Type::OpenVar(slot), upper) => self.add_upper(slot, upper),
            (lower, Type::OpenVar(slot)) => self.add_lower(slot, lower),
            (
                Type::Fun {
                    arg: lower_arg,
                    arg_effect: lower_arg_eff,
                    ret_effect: lower_ret_eff,
                    ret: lower_ret,
                },
                Type::Fun {
                    arg: upper_arg,
                    arg_effect: upper_arg_eff,
                    ret_effect: upper_ret_eff,
                    ret: upper_ret,
                },
            ) => {
                self.constrain_subtype(*upper_arg, *lower_arg)?;
                self.constrain_subtype(*upper_arg_eff, *lower_arg_eff)?;
                self.constrain_subtype(*lower_ret_eff, *upper_ret_eff)?;
                self.constrain_subtype(*lower_ret, *upper_ret)
            }
            (
                Type::Thunk {
                    effect: lower_effect,
                    value: lower_value,
                },
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) => {
                self.constrain_subtype(*lower_effect, *upper_effect)?;
                self.constrain_subtype(*lower_value, *upper_value)
            }
            (
                lower,
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) => {
                self.constrain_subtype(lower, *upper_value)?;
                self.constrain_subtype(Type::pure_effect(), *upper_effect)
            }
            (
                Type::Thunk {
                    effect: lower_effect,
                    value: lower_value,
                },
                upper,
            ) => {
                self.constrain_subtype(*lower_value, upper)?;
                self.constrain_subtype(*lower_effect, Type::pure_effect())
            }
            (
                Type::Con {
                    path: lower_path,
                    args: lower_args,
                },
                Type::Con {
                    path: upper_path,
                    args: upper_args,
                },
            ) if lower_path == upper_path && lower_args.len() == upper_args.len() => {
                for (lower, upper) in lower_args.into_iter().zip(upper_args) {
                    self.constrain_subtype(lower.clone(), upper.clone())?;
                    self.constrain_subtype(upper, lower)?;
                }
                Ok(())
            }
            (
                Type::Con {
                    path: lower_path,
                    args: lower_args,
                },
                Type::Con {
                    path: upper_path,
                    args: upper_args,
                },
            ) => {
                let lower = Type::Con {
                    path: lower_path.clone(),
                    args: lower_args,
                };
                let upper = Type::Con {
                    path: upper_path.clone(),
                    args: upper_args,
                };
                self.constrain_direct_cast(&lower_path, &upper_path, lower, upper)
            }
            (Type::Tuple(lower_items), Type::Tuple(upper_items))
                if lower_items.len() == upper_items.len() =>
            {
                for (lower, upper) in lower_items.into_iter().zip(upper_items) {
                    self.constrain_subtype(lower, upper)?;
                }
                Ok(())
            }
            (Type::Record(lower_fields), Type::Record(upper_fields)) => {
                for upper_field in upper_fields {
                    let Some(lower_field) = record_field_type(&lower_fields, &upper_field.name)
                    else {
                        continue;
                    };
                    self.constrain_subtype(lower_field.value.clone(), upper_field.value)?;
                }
                Ok(())
            }
            (Type::PolyVariant(lower_variants), Type::PolyVariant(upper_variants)) => {
                for lower_variant in lower_variants {
                    let Some(upper_variant) = upper_variants.iter().find(|variant| {
                        variant.name == lower_variant.name
                            && variant.payloads.len() == lower_variant.payloads.len()
                    }) else {
                        continue;
                    };
                    for (lower, upper) in lower_variant
                        .payloads
                        .into_iter()
                        .zip(upper_variant.payloads.iter().cloned())
                    {
                        self.constrain_subtype(lower, upper)?;
                    }
                }
                Ok(())
            }
            (Type::EffectRow(lower_items), Type::EffectRow(upper_items)) => {
                self.constrain_effect_rows(lower_items, upper_items)
            }
            (Type::Stack { inner: lower, .. }, Type::Stack { inner: upper, .. }) => {
                self.constrain_subtype(*lower, *upper)
            }
            (Type::Stack { inner, weight }, upper) => {
                let Some(lower) = self.stack_constraint_projection(*inner, weight) else {
                    return Ok(());
                };
                self.constrain_subtype(lower, upper)
            }
            (lower, Type::Stack { inner, weight }) => {
                let Some(upper) = self.stack_constraint_projection(*inner, weight) else {
                    return Ok(());
                };
                self.constrain_subtype(lower, upper)
            }
            (Type::Union(left, right), upper) => {
                self.constrain_subtype(*left, upper.clone())?;
                self.constrain_subtype(*right, upper)
            }
            (lower, Type::Intersection(left, right)) => {
                self.constrain_subtype(lower.clone(), *left)?;
                self.constrain_subtype(lower, *right)
            }
            _ => Ok(()),
        }
    }

    fn constrain_direct_cast(
        &mut self,
        source: &[String],
        target: &[String],
        lower: Type,
        upper: Type,
    ) -> Result<(), SpecializeError> {
        let candidates = self
            .arena
            .cast_rules
            .iter()
            .filter(|rule| rule.source == source && rule.target == target)
            .cloned()
            .collect::<Vec<_>>();
        for candidate in candidates {
            let predicate = self.instantiate_cast_scheme(candidate.def, &candidate.scheme)?;
            self.constrain_subtype(
                predicate,
                types::pure_function_type(lower.clone(), upper.clone()),
            )?;
        }
        Ok(())
    }

    fn stack_constraint_projection(&self, inner: Type, weight: mono::StackWeight) -> Option<Type> {
        match types::simplify_stack_type(inner, weight) {
            Type::Stack { inner, .. } if self.stack_constraint_can_use_inner(&inner) => {
                Some(*inner)
            }
            Type::Stack { .. } => None,
            ty => Some(ty),
        }
    }

    fn stack_constraint_can_use_inner(&self, inner: &Type) -> bool {
        !matches!(
            inner,
            Type::OpenVar(slot)
                if self
                    .slots
                    .get(*slot as usize)
                    .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
        )
    }

    fn instantiate_cast_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let arena = self.arena;
        let instantiated = types::instantiate_scheme_with_fresh_and_roles(
            arena,
            def,
            scheme,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.fresh_slot(TypeSlotKind::Value),
                types::SchemeQuantifierKind::Effect => self.fresh_slot(TypeSlotKind::Effect),
            },
        )?;
        self.add_role_demands(instantiated.role_predicates);
        self.constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    fn direct_closed_cast_subtype(&self, lower: &Type, upper: &Type) -> bool {
        let Some(source) = con_path_without_args(lower) else {
            return false;
        };
        let Some(target) = con_path_without_args(upper) else {
            return false;
        };
        self.arena.cast_rules.iter().any(|rule| {
            rule.source == source
                && rule.target == target
                && rule.scheme.quantifiers.is_empty()
                && rule.scheme.role_predicates.is_empty()
                && rule.scheme.recursive_bounds.is_empty()
                && rule.scheme.stack_quantifiers.is_empty()
        })
    }

    fn constrain_effect_rows(
        &mut self,
        lower_items: Vec<Type>,
        upper_items: Vec<Type>,
    ) -> Result<(), SpecializeError> {
        let (lower_items, lower_tail) = self.split_effect_row_tail(lower_items);
        let (upper_items, upper_tail) = self.split_effect_row_tail(upper_items);
        let mut matched_upper = vec![false; upper_items.len()];
        let mut lower_extra = Vec::new();

        for lower in lower_items {
            let Some(upper_index) = upper_items.iter().enumerate().find_map(|(index, upper)| {
                (!matched_upper[index] && same_effect_row_family(&lower, upper)).then_some(index)
            }) else {
                lower_extra.push(lower);
                continue;
            };
            matched_upper[upper_index] = true;
            self.constrain_subtype(lower, upper_items[upper_index].clone())?;
        }

        let upper_extra = upper_items
            .into_iter()
            .enumerate()
            .filter_map(|(index, upper)| (!matched_upper[index]).then_some(upper))
            .collect::<Vec<_>>();
        if !lower_extra.is_empty() {
            if let Some(upper_tail) = upper_tail.clone() {
                self.constrain_subtype(Type::EffectRow(lower_extra), upper_tail)?;
            }
        }
        if !upper_extra.is_empty() {
            if let Some(lower_tail) = lower_tail.clone() {
                self.constrain_subtype(lower_tail, Type::EffectRow(upper_extra))?;
            }
        }

        match (lower_tail, upper_tail) {
            (Some(lower_tail), Some(upper_tail)) => self.constrain_subtype(lower_tail, upper_tail),
            _ => Ok(()),
        }
    }

    fn split_effect_row_tail(&self, mut items: Vec<Type>) -> (Vec<Type>, Option<Type>) {
        let Some(Type::OpenVar(slot)) = items.last().cloned() else {
            return (items, None);
        };
        if self
            .slots
            .get(slot as usize)
            .is_some_and(|slot| slot.kind == TypeSlotKind::Effect)
        {
            items.pop();
            return (items, Some(Type::OpenVar(slot)));
        }
        (items, None)
    }

    fn add_edge(&mut self, lower: u32, upper: u32) -> Result<(), SpecializeError> {
        self.ensure_slot(lower)?;
        self.ensure_slot(upper)?;
        if lower == upper {
            return Ok(());
        }
        let lower_index = lower as usize;
        let upper_index = upper as usize;
        if !self.slots[lower_index].successors.contains(&upper) {
            self.slots[lower_index].successors.push(upper);
        }
        if !self.slots[upper_index].predecessors.contains(&lower) {
            self.slots[upper_index].predecessors.push(lower);
        }
        let lowers = self.slots[lower_index].lower.clone();
        for bound in lowers {
            self.add_lower(upper, bound)?;
        }
        let uppers = self.slots[upper_index].upper.clone();
        for bound in uppers {
            self.add_upper(lower, bound)?;
        }
        Ok(())
    }

    fn add_lower(&mut self, slot: u32, lower: Type) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let slot_index = slot as usize;
        if self.slots[slot_index].lower.contains(&lower) {
            return Ok(());
        }
        self.slots[slot_index].lower.push(lower.clone());
        let uppers = self.slots[slot_index].upper.clone();
        for upper in uppers {
            self.constrain_subtype(lower.clone(), upper)?;
        }
        let successors = self.slots[slot_index].successors.clone();
        for successor in successors {
            self.add_lower(successor, lower.clone())?;
        }
        Ok(())
    }

    fn add_upper(&mut self, slot: u32, upper: Type) -> Result<(), SpecializeError> {
        self.ensure_slot(slot)?;
        let slot_index = slot as usize;
        if self.slots[slot_index].upper.contains(&upper) {
            return Ok(());
        }
        self.slots[slot_index].upper.push(upper.clone());
        let lowers = self.slots[slot_index].lower.clone();
        for lower in lowers {
            self.constrain_subtype(lower, upper.clone())?;
        }
        let predecessors = self.slots[slot_index].predecessors.clone();
        for predecessor in predecessors {
            self.add_upper(predecessor, upper.clone())?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct TypeSlot {
    kind: TypeSlotKind,
    lower: Vec<Type>,
    upper: Vec<Type>,
    successors: Vec<u32>,
    predecessors: Vec<u32>,
}

impl TypeSlot {
    fn new(kind: TypeSlotKind) -> Self {
        Self {
            kind,
            lower: Vec::new(),
            upper: Vec::new(),
            successors: Vec::new(),
            predecessors: Vec::new(),
        }
    }
}

struct TypeResolver<'graph, 'arena> {
    graph: &'graph ConstraintGraph<'arena>,
    solutions: HashMap<u32, Type>,
    resolving: HashSet<u32>,
}

impl<'graph, 'arena> TypeResolver<'graph, 'arena> {
    fn new(graph: &'graph ConstraintGraph<'arena>) -> Self {
        Self {
            graph,
            solutions: HashMap::new(),
            resolving: HashSet::new(),
        }
    }

    fn resolve(&mut self, ty: &Type) -> Result<Type, SpecializeError> {
        match ty {
            Type::Any => Ok(Type::Any),
            Type::Never => Ok(Type::Never),
            Type::Con { path, args } => Ok(Type::Con {
                path: path.clone(),
                args: self.resolve_all(args)?,
            }),
            Type::Fun {
                arg,
                arg_effect,
                ret_effect,
                ret,
            } => Ok(Type::Fun {
                arg: Box::new(self.resolve(arg)?),
                arg_effect: Box::new(self.resolve(arg_effect)?),
                ret_effect: Box::new(self.resolve(ret_effect)?),
                ret: Box::new(self.resolve(ret)?),
            }),
            Type::Thunk { effect, value } => {
                let effect = self.resolve(effect)?;
                let value = self.resolve(value)?;
                if effect.is_pure_effect() {
                    return Ok(value);
                }
                Ok(Type::Thunk {
                    effect: Box::new(effect),
                    value: Box::new(value),
                })
            }
            Type::Record(fields) => fields
                .iter()
                .map(|field| {
                    Ok(mono::TypeField {
                        name: field.name.clone(),
                        value: self.resolve(&field.value)?,
                        optional: field.optional,
                    })
                })
                .collect::<Result<Vec<_>, _>>()
                .map(Type::Record),
            Type::PolyVariant(variants) => variants
                .iter()
                .map(|variant| {
                    Ok(mono::TypeVariant {
                        name: variant.name.clone(),
                        payloads: self.resolve_all(&variant.payloads)?,
                    })
                })
                .collect::<Result<Vec<_>, _>>()
                .map(Type::PolyVariant),
            Type::Tuple(items) => self.resolve_all(items).map(Type::Tuple),
            Type::EffectRow(items) => Ok(types::simplify_type(Type::EffectRow(
                self.resolve_all(items)?,
            ))),
            Type::Stack { inner, weight } => Ok(types::simplify_stack_type(
                self.resolve(inner)?,
                weight.clone(),
            )),
            Type::Union(left, right) => Ok(types::simplify_type(Type::Union(
                Box::new(self.resolve(left)?),
                Box::new(self.resolve(right)?),
            ))),
            Type::Intersection(left, right) => Ok(types::simplify_type(Type::Intersection(
                Box::new(self.resolve(left)?),
                Box::new(self.resolve(right)?),
            ))),
            Type::OpenVar(slot) => self.slot_solution(*slot),
        }
    }

    fn resolve_all(&mut self, tys: &[Type]) -> Result<Vec<Type>, SpecializeError> {
        tys.iter().map(|ty| self.resolve(ty)).collect()
    }

    fn slot_solution(&mut self, slot: u32) -> Result<Type, SpecializeError> {
        if let Some(solution) = self.solutions.get(&slot) {
            return Ok(solution.clone());
        }
        let slot_data = self.graph.slot(slot)?;
        let slot_kind = slot_data.kind;
        let lower_bounds = slot_data.lower.clone();
        let upper_bounds = slot_data.upper.clone();
        if !self.resolving.insert(slot) {
            return Ok(slot_kind.default_type());
        }
        let lower = self.join_candidates(slot, slot_kind, &lower_bounds)?;
        let upper = self.meet_candidates(slot, slot_kind, &upper_bounds)?;
        let solution = match (lower, upper) {
            (Some(lower), Some(upper)) if type_candidates_equivalent(&lower, &upper) => lower,
            (Some(lower), Some(upper)) if type_candidate_subtype(self.graph, &lower, &upper) => {
                lower
            }
            (Some(lower), Some(upper)) => {
                return Err(SpecializeError::ConflictingTypeCandidates {
                    slot,
                    existing: lower,
                    incoming: upper,
                });
            }
            (Some(lower), None) => lower,
            (None, Some(upper)) => upper,
            (None, None) if slot_kind == TypeSlotKind::Effect => Type::pure_effect(),
            (None, None) => return Err(SpecializeError::UndeterminedTypeSlot { slot }),
        };
        self.resolving.remove(&slot);
        self.solutions.insert(slot, solution.clone());
        Ok(solution)
    }

    fn join_candidates(
        &mut self,
        slot: u32,
        slot_kind: TypeSlotKind,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut candidate: Option<Type> = None;
        for bound in bounds {
            let resolved = self.resolve(bound)?;
            candidate = Some(match candidate {
                Some(existing) if slot_kind == TypeSlotKind::Effect => {
                    join_effect_type_candidates(existing, resolved)
                }
                Some(existing) => join_type_candidates(self.graph, slot, existing, resolved)?,
                None => resolved,
            });
        }
        Ok(candidate)
    }

    fn meet_candidates(
        &mut self,
        slot: u32,
        slot_kind: TypeSlotKind,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut candidate: Option<Type> = None;
        for bound in bounds {
            let resolved = self.resolve(bound)?;
            candidate = Some(match candidate {
                Some(existing) if slot_kind == TypeSlotKind::Effect => {
                    meet_effect_type_candidates(existing, resolved)
                }
                Some(existing) => meet_type_candidates(self.graph, slot, existing, resolved)?,
                None => resolved,
            });
        }
        Ok(candidate)
    }
}

fn join_effect_type_candidates(left: Type, right: Type) -> Type {
    if left.is_pure_effect() {
        return right;
    }
    if right.is_pure_effect() {
        return left;
    }
    match (left, right) {
        (Type::EffectRow(mut left), Type::EffectRow(right)) => {
            for item in right {
                if !left.contains(&item) {
                    left.push(item);
                }
            }
            Type::EffectRow(left)
        }
        (left, right) => types::simplify_type(Type::Union(Box::new(left), Box::new(right))),
    }
}

fn meet_effect_type_candidates(left: Type, right: Type) -> Type {
    if left.is_pure_effect() || right.is_pure_effect() {
        return Type::pure_effect();
    }
    match (left, right) {
        (Type::EffectRow(left), Type::EffectRow(right)) => types::simplify_type(Type::EffectRow(
            left.into_iter()
                .filter(|item| right.contains(item))
                .collect(),
        )),
        (left, right) => types::simplify_type(Type::Intersection(Box::new(left), Box::new(right))),
    }
}

fn join_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    if type_candidates_equivalent(&left, &right) || type_candidate_subtype(graph, &right, &left) {
        return Ok(left);
    }
    if type_candidate_subtype(graph, &left, &right) {
        return Ok(right);
    }
    match (left, right) {
        (Type::Never, right) => Ok(right),
        (left, Type::Never) => Ok(left),
        (Type::Any, _) | (_, Type::Any) => Ok(Type::Any),
        (left, right) => Err(SpecializeError::ConflictingTypeCandidates {
            slot,
            existing: left,
            incoming: right,
        }),
    }
}

fn meet_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    if type_candidates_equivalent(&left, &right) || type_candidate_subtype(graph, &left, &right) {
        return Ok(left);
    }
    if type_candidate_subtype(graph, &right, &left) {
        return Ok(right);
    }
    match (left, right) {
        (Type::Any, right) => Ok(right),
        (left, Type::Any) => Ok(left),
        (Type::Never, _) | (_, Type::Never) => Ok(Type::Never),
        (left, right) => Err(SpecializeError::ConflictingTypeCandidates {
            slot,
            existing: left,
            incoming: right,
        }),
    }
}

fn type_candidates_equivalent(left: &Type, right: &Type) -> bool {
    left == right || left.is_pure_effect() && right.is_pure_effect()
}

fn type_candidate_subtype(graph: &ConstraintGraph<'_>, lower: &Type, upper: &Type) -> bool {
    if type_candidates_equivalent(lower, upper)
        || matches!(lower, Type::Never)
        || matches!(upper, Type::Any)
        || graph.direct_closed_cast_subtype(lower, upper)
    {
        return true;
    }
    match (lower, upper) {
        (Type::Union(left, right), _) => {
            type_candidate_subtype(graph, left, upper)
                && type_candidate_subtype(graph, right, upper)
        }
        (_, Type::Union(left, right)) => {
            type_candidate_subtype(graph, lower, left)
                || type_candidate_subtype(graph, lower, right)
        }
        (Type::Intersection(left, right), _) => {
            type_candidate_subtype(graph, left, upper)
                || type_candidate_subtype(graph, right, upper)
        }
        (_, Type::Intersection(left, right)) => {
            type_candidate_subtype(graph, lower, left)
                && type_candidate_subtype(graph, lower, right)
        }
        (lower, Type::Thunk { effect, value }) if effect.is_pure_effect() => {
            type_candidate_subtype(graph, lower, value)
        }
        (Type::Thunk { effect, value }, upper) if effect.is_pure_effect() => {
            type_candidate_subtype(graph, value, upper)
        }
        (
            Type::Con {
                path: lower_path,
                args: lower_args,
            },
            Type::Con {
                path: upper_path,
                args: upper_args,
            },
        ) => {
            lower_path == upper_path
                && lower_args.len() == upper_args.len()
                && lower_args
                    .iter()
                    .zip(upper_args)
                    .all(|(lower, upper)| type_candidates_equivalent(lower, upper))
        }
        (
            Type::Fun {
                arg: lower_arg,
                arg_effect: lower_arg_effect,
                ret_effect: lower_ret_effect,
                ret: lower_ret,
            },
            Type::Fun {
                arg: upper_arg,
                arg_effect: upper_arg_effect,
                ret_effect: upper_ret_effect,
                ret: upper_ret,
            },
        ) => {
            type_candidate_subtype(graph, upper_arg, lower_arg)
                && type_candidate_subtype(graph, upper_arg_effect, lower_arg_effect)
                && type_candidate_subtype(graph, lower_ret_effect, upper_ret_effect)
                && type_candidate_subtype(graph, lower_ret, upper_ret)
        }
        (
            Type::Thunk {
                effect: lower_effect,
                value: lower_value,
            },
            Type::Thunk {
                effect: upper_effect,
                value: upper_value,
            },
        ) => {
            type_candidate_subtype(graph, lower_effect, upper_effect)
                && type_candidate_subtype(graph, lower_value, upper_value)
        }
        (Type::Tuple(lower_items), Type::Tuple(upper_items)) => {
            lower_items.len() == upper_items.len()
                && lower_items
                    .iter()
                    .zip(upper_items)
                    .all(|(lower, upper)| type_candidate_subtype(graph, lower, upper))
        }
        (Type::Record(lower_fields), Type::Record(upper_fields)) => {
            upper_fields.iter().all(|upper_field| {
                upper_field.optional
                    || record_field_type(lower_fields, &upper_field.name).is_some_and(
                        |lower_field| {
                            type_candidate_subtype(graph, &lower_field.value, &upper_field.value)
                        },
                    )
            })
        }
        (Type::PolyVariant(lower_variants), Type::PolyVariant(upper_variants)) => {
            lower_variants.iter().all(|lower_variant| {
                upper_variants
                    .iter()
                    .find(|upper_variant| {
                        upper_variant.name == lower_variant.name
                            && upper_variant.payloads.len() == lower_variant.payloads.len()
                    })
                    .is_some_and(|upper_variant| {
                        lower_variant
                            .payloads
                            .iter()
                            .zip(&upper_variant.payloads)
                            .all(|(lower, upper)| type_candidate_subtype(graph, lower, upper))
                    })
            })
        }
        (Type::EffectRow(lower_items), Type::EffectRow(upper_items)) => {
            lower_items.len() == upper_items.len()
                && lower_items
                    .iter()
                    .zip(upper_items)
                    .all(|(lower, upper)| type_candidate_subtype(graph, lower, upper))
        }
        (Type::Stack { inner: lower, .. }, Type::Stack { inner: upper, .. }) => {
            type_candidate_subtype(graph, lower, upper)
        }
        (Type::Stack { inner, weight }, upper) => graph
            .stack_constraint_projection(inner.as_ref().clone(), weight.clone())
            .is_some_and(|lower| type_candidate_subtype(graph, &lower, upper)),
        (lower, Type::Stack { inner, weight }) => graph
            .stack_constraint_projection(inner.as_ref().clone(), weight.clone())
            .is_some_and(|upper| type_candidate_subtype(graph, lower, &upper)),
        _ => false,
    }
}

fn resolve_role_arg_exact_type(
    graph: &ConstraintGraph<'_>,
    resolver: &mut TypeResolver<'_, '_>,
    arg: &types::InstantiatedRoleArg,
) -> Result<Option<Type>, SpecializeError> {
    let lower = resolve_role_arg_bound(resolver, &arg.lower, RoleArgBound::Lower)?;
    let upper = resolve_role_arg_bound(resolver, &arg.upper, RoleArgBound::Upper)?;
    Ok(choose_resolved_role_arg_exact_type(graph, lower, upper))
}

fn resolve_role_arg_bound(
    resolver: &mut TypeResolver<'_, '_>,
    bound: &Type,
    side: RoleArgBound,
) -> Result<Option<Type>, SpecializeError> {
    match resolver.resolve(bound) {
        Ok(ty) => Ok(side.non_trivial(ty)),
        Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(None),
        Err(error) => Err(error),
    }
}

#[derive(Debug, Clone, Copy)]
enum RoleArgBound {
    Lower,
    Upper,
}

impl RoleArgBound {
    fn non_trivial(self, ty: Type) -> Option<Type> {
        match (self, &ty) {
            (Self::Lower, Type::Never) | (Self::Upper, Type::Any) => None,
            _ => Some(ty),
        }
    }
}

fn choose_resolved_role_arg_exact_type(
    graph: &ConstraintGraph<'_>,
    lower: Option<Type>,
    upper: Option<Type>,
) -> Option<Type> {
    match (lower, upper) {
        (Some(lower), Some(upper)) if type_candidates_equivalent(&lower, &upper) => Some(lower),
        (Some(lower), Some(upper)) if type_candidate_subtype(graph, &lower, &upper) => Some(lower),
        (Some(lower), Some(upper)) if type_candidate_subtype(graph, &upper, &lower) => Some(upper),
        (Some(lower), None) => Some(lower),
        (None, Some(upper)) => Some(upper),
        _ => None,
    }
}

fn con_path_without_args(ty: &Type) -> Option<&[String]> {
    let Type::Con { path, args } = ty else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    Some(path)
}

fn record_field_type<'a>(fields: &'a [TypeField], name: &str) -> Option<&'a TypeField> {
    fields.iter().find(|field| field.name == name)
}

fn join_record_fields(mut head: Vec<TypeField>, tail: Vec<TypeField>) -> Vec<TypeField> {
    head.extend(tail);
    head
}

fn record_spread_def(
    spread: &poly_expr::RecordSpread<poly_expr::DefId>,
) -> Option<poly_expr::DefId> {
    match spread {
        poly_expr::RecordSpread::Head(def) | poly_expr::RecordSpread::Tail(def) => Some(*def),
        poly_expr::RecordSpread::None => None,
    }
}

fn list_item_type(ty: &Type) -> Option<Type> {
    let Type::Con { args, .. } = ty else {
        return None;
    };
    let [item] = args.as_slice() else {
        return None;
    };
    Some(item.clone())
}

fn primitive_spine_arg_type(
    op: poly_expr::PrimitiveOp,
    applied: usize,
    ret: &Type,
) -> Option<Type> {
    use poly_expr::PrimitiveOp;

    let final_ret = runtime_value_shape(final_return_type(ret));
    let list = list_item_type(final_ret).map(|_| final_ret.clone());
    let item = list.as_ref().and_then(list_item_type);
    match (op, applied) {
        (PrimitiveOp::ListEmpty, 0) => Some(Type::unit()),
        (PrimitiveOp::ListSingleton, 0) => item,
        (PrimitiveOp::ListMerge, 0 | 1)
        | (PrimitiveOp::ListIndexRange, 0)
        | (PrimitiveOp::ListSplice, 0 | 2)
        | (PrimitiveOp::ListIndexRangeRaw, 0)
        | (PrimitiveOp::ListSpliceRaw, 0 | 3) => list,
        (PrimitiveOp::ListIndexRange, 1) | (PrimitiveOp::ListSplice, 1) => Some(range_type()),
        (PrimitiveOp::ListIndexRangeRaw, 1 | 2) | (PrimitiveOp::ListSpliceRaw, 1 | 2) => {
            Some(int_type())
        }
        _ => None,
    }
}

fn final_return_type(mut ty: &Type) -> &Type {
    while let Type::Fun { ret, .. } = ty {
        ty = ret;
    }
    ty
}

fn runtime_value_shape(ty: &Type) -> &Type {
    match ty {
        Type::Thunk { value, .. } => value,
        _ => ty,
    }
}

fn function_runtime_parts(ty: &Type) -> Option<(Type, Type)> {
    let Type::Fun { arg, ret, .. } = ty else {
        return None;
    };
    Some((arg.as_ref().clone(), ret.as_ref().clone()))
}

fn split_function_spine(mut ty: Type, arity: usize) -> Option<(Vec<Type>, Type)> {
    let mut args = Vec::with_capacity(arity);
    for _ in 0..arity {
        let Type::Fun { arg, ret, .. } = ty else {
            return None;
        };
        args.push(*arg);
        ty = *ret;
    }
    Some((args, ty))
}

fn split_runtime_computation_shape(shape: Type) -> (Type, Type) {
    match shape {
        Type::Thunk { effect, value } => (*value, *effect),
        value => (value, Type::pure_effect()),
    }
}

fn matching_effect_row_item(item: &Type, candidates: &[Type]) -> Option<Type> {
    candidates
        .iter()
        .find(|candidate| same_effect_row_family(item, candidate))
        .cloned()
}

fn same_effect_row_family(left: &Type, right: &Type) -> bool {
    matches!(
        (left, right),
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if left_path == right_path && left_args.len() == right_args.len()
    )
}

fn function_type(args: Vec<Type>, ret: Type) -> Type {
    args.into_iter()
        .rev()
        .fold(ret, |ret, arg| types::pure_function_type(arg, ret))
}

fn unary_type(arg: Type, ret: Type) -> Type {
    function_type(vec![arg], ret)
}

fn binary_type(arg: Type, ret: Type) -> Type {
    function_type(vec![arg.clone(), arg], ret)
}

fn con_type(name: &str) -> Type {
    Type::Con {
        path: vec![name.to_string()],
        args: Vec::new(),
    }
}

fn int_type() -> Type {
    con_type("int")
}

fn float_type() -> Type {
    con_type("float")
}

fn bool_type() -> Type {
    con_type("bool")
}

fn str_type() -> Type {
    std_types::str_type()
}

fn char_type() -> Type {
    std_types::char_type()
}

fn list_type(item: Type) -> Type {
    std_types::list_type(item)
}

fn list_view_type(item: Type) -> Type {
    std_types::list_view_type(item)
}

fn bytes_type() -> Type {
    std_types::bytes_type()
}

fn path_type() -> Type {
    std_types::path_type()
}

fn range_type() -> Type {
    std_types::range_type()
}

#[cfg(test)]
mod tests {
    use mono::Type;

    use super::{ConstraintGraph, TypeResolver, TypeSlotKind, solve_expr};

    #[test]
    fn root_generic_call_gets_types_for_apply_callee_and_arg() {
        let lowering = lower_source("my id x = x\nid(1)\n");
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("root expression should solve");

        let poly::expr::Expr::App(callee, arg) = arena.expr(root) else {
            panic!("root should be an apply");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "int"
        );
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(*callee).unwrap()),
            "int -> int"
        );
        assert_eq!(plan.actual_type_of(*arg), Some(&int_type()));
    }

    #[test]
    fn higher_order_direct_ref_argument_uses_outer_apply_type() {
        let lowering = lower_source("my id x = x\nmy apply f x = f(x)\napply(id)(1)\n");
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("root expression should solve");

        let poly::expr::Expr::App(inner, arg) = arena.expr(root) else {
            panic!("root should be an apply");
        };
        let poly::expr::Expr::App(apply, id) = arena.expr(*inner) else {
            panic!("callee should be an apply");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "int"
        );
        assert_eq!(plan.actual_type_of(*arg), Some(&int_type()));
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(*inner).unwrap()),
            "int -> int"
        );
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(*apply).unwrap()),
            "(int -> int) -> int -> int"
        );
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(*id).unwrap()),
            "int -> int"
        );
    }

    #[test]
    fn root_case_without_expected_type_errors_when_arm_results_do_not_join() {
        let lowering = lower_source("case true: true -> 1, false -> 2.0\n");
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let error = solve_expr(arena, root, None).expect_err("root case should be ambiguous");

        assert_conflicting_type_candidates(error, "int", "float");
    }

    #[test]
    fn root_case_uses_direct_cast_as_join_candidate() {
        let lowering =
            lower_source("cast(x: int): float = 0.0\ncase true: true -> 1, false -> 2.0\n");
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("root case should solve");

        let poly::expr::Expr::Case(_, arms) = arena.expr(root) else {
            panic!("root should be a case");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "float"
        );
        assert_eq!(plan.actual_type_of(arms[0].body), Some(&int_type()));
        assert_eq!(plan.actual_type_of(arms[1].body), Some(&float_type()));
        assert_eq!(
            mono::dump::dump_type(plan.boundary(arms[0].body).unwrap().expected),
            "float"
        );
        assert_eq!(
            mono::dump::dump_type(plan.boundary(arms[1].body).unwrap().expected),
            "float"
        );
    }

    #[test]
    fn root_case_uses_variant_patterns_as_scrutinee_expectation() {
        let lowering = lower_source("case :disabled: :label text -> text, :disabled -> \"\"\n");
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("variant case should solve");

        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "std::text::str::str"
        );
    }

    #[test]
    fn root_role_associated_type_is_resolved_from_poly_impl_candidate() {
        let mut arena = poly::expr::Arena::new();
        let range = con_arg(&mut arena.typ, vec!["range".to_string()]);
        let int = con_arg(&mut arena.typ, vec!["int".to_string()]);
        arena.role_impls.insert(poly::roles::RoleImplCandidate {
            impl_def: None,
            role: vec!["Fold".to_string()],
            inputs: vec![range],
            associated: vec![poly::roles::RoleAssociatedConstraint {
                name: "item".to_string(),
                value: int,
            }],
            prerequisites: Vec::new(),
            methods: Vec::new(),
        });

        let container = arena.fresh_type_var();
        let item = arena.fresh_type_var();
        let container_arg = var_arg(&mut arena.typ, container);
        let item_arg = var_arg(&mut arena.typ, item);
        let predicate_arg = arena.typ.alloc_neg(poly::types::Neg::Var(container));
        let predicate_arg_eff = arena.typ.alloc_neg(poly::types::Neg::Bot);
        let predicate_ret_eff = arena.typ.alloc_pos(poly::types::Pos::Bot);
        let predicate_ret = arena.typ.alloc_pos(poly::types::Pos::Var(item));
        let predicate = arena.typ.alloc_pos(poly::types::Pos::Fun {
            arg: predicate_arg,
            arg_eff: predicate_arg_eff,
            ret_eff: predicate_ret_eff,
            ret: predicate_ret,
        });
        let each_scheme = poly::types::Scheme {
            quantifiers: vec![container, item],
            role_predicates: vec![poly::types::RolePredicate {
                role: vec!["Fold".to_string()],
                inputs: vec![poly::types::RolePredicateArg::Invariant(
                    arena.typ.alloc_neu(poly::types::Neu::Bounds(
                        container_arg.lower,
                        container_arg.upper,
                    )),
                )],
                associated: vec![poly::types::RoleAssociatedType {
                    name: "item".to_string(),
                    value: arena
                        .typ
                        .alloc_neu(poly::types::Neu::Bounds(item_arg.lower, item_arg.upper)),
                }],
            }],
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate,
        };
        let each_def = let_def(&mut arena, Some(each_scheme));
        let range_scheme = monomorphic_scheme(range);
        let range_def = let_def(&mut arena, Some(range_scheme));
        let each_expr = resolved_var_expr(&mut arena, each_def);
        let range_expr = resolved_var_expr(&mut arena, range_def);
        let root = arena.add_expr(poly::expr::Expr::App(each_expr, range_expr));

        let plan = solve_expr(&arena, root, None).expect("role associated type should solve");

        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "int"
        );
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(each_expr).unwrap()),
            "range -> int"
        );
    }

    #[test]
    fn pure_function_argument_effect_passes_to_apply_result() {
        let lowering = lower_source(
            "act out:\n  our read: unit -> int\n\
             my id x = x\n\
             id(out::read(()))\n",
        );
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("pure function call should solve");

        let poly::expr::Expr::App(_, arg) = arena.expr(root) else {
            panic!("root should be an apply");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "thunk[[out], int]"
        );
        assert_eq!(
            mono::dump::dump_type(plan.boundary(*arg).unwrap().actual),
            "thunk[[out], int]"
        );
        assert_eq!(
            mono::dump::dump_type(plan.boundary(*arg).unwrap().expected),
            "int"
        );
    }

    #[test]
    fn effect_row_subtyping_matches_items_by_path_before_tail_residual() {
        let arena = poly::expr::Arena::new();
        let mut graph = ConstraintGraph::new(&arena);
        let tail = graph.fresh_slot(TypeSlotKind::Effect);

        graph
            .constrain_subtype(
                Type::EffectRow(vec![effect_item("nondet")]),
                Type::EffectRow(vec![effect_item("junction"), tail.clone()]),
            )
            .expect("effect row subtype should solve");

        let mut resolver = TypeResolver::new(&graph);
        assert_eq!(
            mono::dump::dump_type(&resolver.resolve(&tail).unwrap()),
            "[nondet]"
        );
    }

    #[test]
    fn case_scrutinee_effect_passes_to_case_result() {
        let lowering = lower_source(
            "act out:\n  our read: unit -> int\n\
             case out::read(()):\n\
             \x20 1 -> 2\n\
             \x20 _ -> 3\n",
        );
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("effectful case should solve");

        let poly::expr::Expr::Case(scrutinee, _) = arena.expr(root) else {
            panic!("root should be a case");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "thunk[[out], int]"
        );
        assert_eq!(
            mono::dump::dump_type(plan.boundary(*scrutinee).unwrap().actual),
            "thunk[[out], int]"
        );
        assert_eq!(
            mono::dump::dump_type(plan.boundary(*scrutinee).unwrap().expected),
            "int"
        );
    }

    #[test]
    fn root_case_errors_instead_of_using_transitive_casts_as_join_candidate() {
        let lowering = lower_source(
            "cast(x: int): bool = true\n\
             cast(x: bool): float = 0.0\n\
             case true: true -> 1, false -> 2.0\n",
        );
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let error = solve_expr(arena, root, None).expect_err("root case should be ambiguous");

        assert_conflicting_type_candidates(error, "int", "float");
    }

    #[test]
    fn catch_effect_arm_uses_operation_type_for_payload_and_continuation() {
        let lowering = lower_source(
            "act out:\n  our say: int -> unit\n\
             catch out::say(1):\n\
             \x20 out::say msg, k -> k(())\n\
             \x20 value -> value\n",
        );
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("handled effect should solve");

        let poly::expr::Expr::Catch(body, arms) = arena.expr(root) else {
            panic!("root should be a catch");
        };
        assert_eq!(
            arms[0].operation.as_ref().map(|operation| &operation.path),
            Some(&vec!["out".to_string(), "say".to_string()])
        );
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "unit"
        );
        assert_eq!(
            mono::dump::dump_type(plan.boundary(*body).unwrap().actual),
            "thunk[[out], unit]"
        );
        assert_eq!(
            mono::dump::dump_type(plan.boundary(*body).unwrap().expected),
            "unit"
        );

        let poly::expr::Expr::App(continuation, resume_value) = arena.expr(arms[0].body) else {
            panic!("effect arm body should resume the continuation");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(*continuation).unwrap()),
            "unit -> thunk[[out], unit]"
        );
        assert_eq!(plan.actual_type_of(*resume_value), Some(&unit_type()));
        assert_eq!(
            mono::dump::dump_type(plan.boundary(arms[0].body).unwrap().actual),
            "thunk[[out], unit]"
        );
        assert_eq!(
            mono::dump::dump_type(plan.boundary(arms[0].body).unwrap().expected),
            "unit"
        );
    }

    #[test]
    fn catch_effect_arm_matches_generic_operation_effect_to_scrutinee_effect() {
        let lowering = lower_source(
            "act var 't:\n  our get: unit -> 't\n\
             catch var::get():\n\
             \x20 var::get(), k -> k(1)\n\
             \x20 value -> value\n",
        );
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("generic handled effect should solve");

        let poly::expr::Expr::Catch(body, arms) = arena.expr(root) else {
            panic!("root should be a catch");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "int"
        );
        assert_eq!(
            mono::dump::dump_type(plan.boundary(*body).unwrap().actual),
            "thunk[[var(int)], int]"
        );
        let poly::expr::Expr::App(continuation, resume_value) = arena.expr(arms[0].body) else {
            panic!("effect arm body should resume the continuation");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(*continuation).unwrap()),
            "int -> thunk[[var(int)], int]"
        );
        assert_eq!(plan.actual_type_of(*resume_value), Some(&int_type()));
    }

    #[test]
    fn case_constructor_pattern_binds_payload_from_scrutinee_type() {
        let lowering = lower_source(
            "enum opt 'a:\n  none\n  some 'a\n\
             my id x = x\n\
             case opt::some 1:\n\
             \x20 opt::some x -> id(x)\n\
             \x20 _ -> 0\n",
        );
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("constructor case should solve");

        let poly::expr::Expr::Case(_, arms) = arena.expr(root) else {
            panic!("root should be a case");
        };
        let poly::expr::Expr::App(_, payload_ref) = arena.expr(arms[0].body) else {
            panic!("first arm body should call id");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "int"
        );
        assert_eq!(plan.actual_type_of(*payload_ref), Some(&int_type()));
    }

    #[test]
    fn case_record_pattern_binds_field_from_scrutinee_type() {
        let lowering = lower_source(
            "my id x = x\n\
             case { width: 1 }:\n\
             \x20 { width } -> id(width)\n\
             \x20 _ -> 0\n",
        );
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("record case should solve");

        let poly::expr::Expr::Case(_, arms) = arena.expr(root) else {
            panic!("root should be a case");
        };
        let poly::expr::Expr::App(_, field_ref) = arena.expr(arms[0].body) else {
            panic!("first arm body should call id");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "int"
        );
        assert_eq!(plan.actual_type_of(*field_ref), Some(&int_type()));
    }

    #[test]
    fn record_select_reads_base_field_type() {
        let lowering = lower_source("my id x = x\nid(({ width: 1 }).width)\n");
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("record select should solve");

        let poly::expr::Expr::App(_, select) = arena.expr(root) else {
            panic!("root should call id");
        };
        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "int"
        );
        assert_eq!(plan.actual_type_of(*select), Some(&int_type()));
    }

    fn assert_conflicting_type_candidates(error: crate::SpecializeError, left: &str, right: &str) {
        let crate::SpecializeError::ConflictingTypeCandidates {
            existing, incoming, ..
        } = error
        else {
            panic!("expected conflicting type candidates, got {error:?}");
        };
        assert_eq!(mono::dump::dump_type(&existing), left);
        assert_eq!(mono::dump::dump_type(&incoming), right);
    }

    fn int_type() -> Type {
        Type::Con {
            path: vec!["int".to_string()],
            args: Vec::new(),
        }
    }

    fn float_type() -> Type {
        Type::Con {
            path: vec!["float".to_string()],
            args: Vec::new(),
        }
    }

    fn unit_type() -> Type {
        Type::unit()
    }

    fn effect_item(name: &str) -> Type {
        Type::Con {
            path: vec![name.to_string()],
            args: Vec::new(),
        }
    }

    fn con_arg(
        types: &mut poly::types::TypeArena,
        path: Vec<String>,
    ) -> poly::roles::RoleConstraintArg {
        poly::roles::RoleConstraintArg {
            lower: types.alloc_pos(poly::types::Pos::Con(path.clone(), Vec::new())),
            upper: types.alloc_neg(poly::types::Neg::Con(path, Vec::new())),
        }
    }

    fn var_arg(
        types: &mut poly::types::TypeArena,
        var: poly::types::TypeVar,
    ) -> poly::roles::RoleConstraintArg {
        poly::roles::RoleConstraintArg {
            lower: types.alloc_pos(poly::types::Pos::Var(var)),
            upper: types.alloc_neg(poly::types::Neg::Var(var)),
        }
    }

    fn monomorphic_scheme(arg: poly::roles::RoleConstraintArg) -> poly::types::Scheme {
        poly::types::Scheme {
            quantifiers: Vec::new(),
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate: arg.lower,
        }
    }

    fn let_def(
        arena: &mut poly::expr::Arena,
        scheme: Option<poly::types::Scheme>,
    ) -> poly::expr::DefId {
        let def = arena.defs.fresh();
        arena.defs.set(
            def,
            poly::expr::Def::Let {
                vis: poly::expr::Vis::My,
                scheme,
                body: None,
                children: Vec::new(),
            },
        );
        def
    }

    fn resolved_var_expr(
        arena: &mut poly::expr::Arena,
        def: poly::expr::DefId,
    ) -> poly::expr::ExprId {
        let reference = arena.add_ref();
        arena.resolve_ref(reference, def);
        arena.add_expr(poly::expr::Expr::Var(reference))
    }

    fn lower_source(source: &str) -> infer::lowering::BodyLowering {
        let files = sources::load(vec![sources::SourceFile {
            module_path: sources::Path::default(),
            source: source.to_string(),
        }]);
        let output = infer::dump::dump_loaded_files(&files).expect("source should lower");
        assert!(
            output.lowering.errors.is_empty(),
            "body lowering errors: {:?}",
            output.lowering.errors
        );
        output.lowering
    }
}
