//! `mono` instance 内で erased expression に型を割り当てる作業状態。
//!
//! `poly` は式 node ごとの型を保持しない。ここでは instance/root ごとに主型と erased IR から
//! use-site の concrete 型を再構成し、mono IR へ写す段階が参照する plan だけを残す。

use std::collections::{HashMap, HashSet, VecDeque};

use mono::{
    EffectFamilies, EffectFamily, StackWeight, StackWeightEntry, Type, TypeField, TypeVariant,
};
use poly::expr as poly_expr;

use crate::{
    ExprTypeRole, SpecializeError, convert_def, def_kind, lit_type, roles, std_types, types,
};

#[derive(Debug, Clone, Default)]
pub(crate) struct ExprTypePlan {
    types: HashMap<poly_expr::ExprId, ExprTypes>,
    raw_thunk_computations: HashSet<poly_expr::ExprId>,
    contextual_value_fetches: HashSet<poly_expr::ExprId>,
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

    fn mark_contextual_value_fetch(&mut self, expr: poly_expr::ExprId) {
        self.contextual_value_fetches.insert(expr);
    }

    fn actual(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.types
            .get(&expr)
            .and_then(|types| types.actual.as_ref())
    }

    fn expected(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.types
            .get(&expr)
            .and_then(|types| types.expected.as_ref())
    }

    fn finalize(&self, graph: &ConstraintGraph<'_>) -> Result<Self, SpecializeError> {
        let solution = graph.solve_type_graph()?;
        let mut resolver = TypeResolver::with_solution(graph, &solution);
        let mut out = Self {
            types: HashMap::new(),
            raw_thunk_computations: self.raw_thunk_computations.clone(),
            contextual_value_fetches: self.contextual_value_fetches.clone(),
        };
        for (expr, types) in &self.types {
            let mut resolved_actual = None;
            if let Some(actual) = &types.actual {
                let actual = match resolver.resolve(actual) {
                    Ok(actual) => actual,
                    Err(SpecializeError::UndeterminedTypeSlot { .. })
                        if let Some(actual) = resolver
                            .resolve_erased_effectful_actual(actual, types.expected.as_ref()) =>
                    {
                        actual
                    }
                    Err(SpecializeError::UndeterminedTypeSlot { .. })
                        if types
                            .expected
                            .as_ref()
                            .is_some_and(|expected| expected == actual)
                            && unresolved_exact_boundary_can_be_erased(graph.arena, *expr) =>
                    {
                        continue;
                    }
                    Err(SpecializeError::UndeterminedTypeSlot { .. })
                        if unresolved_actual_boundary_can_be_erased(
                            graph.arena,
                            *expr,
                            actual,
                            types.expected.as_ref(),
                        ) =>
                    {
                        continue;
                    }
                    Err(error @ SpecializeError::UndeterminedTypeSlot { .. })
                        if self.contextual_value_fetches.contains(expr) =>
                    {
                        let Some(expected) = &types.expected else {
                            return Err(error);
                        };
                        match resolver.resolve(expected) {
                            Ok(expected) => expected,
                            Err(SpecializeError::UndeterminedTypeSlot { .. })
                                if unresolved_exact_boundary_can_be_erased(graph.arena, *expr) =>
                            {
                                continue;
                            }
                            Err(expected_error) => {
                                return Err(expected_error);
                            }
                        }
                    }
                    Err(error @ SpecializeError::UndeterminedTypeSlot { .. }) => {
                        eprintln!(
                            "finalize actual failed expr={:?} tree={} actual={actual:?} expected={:?} error={error:?}",
                            expr,
                            debug_expr_tree(graph.arena, *expr, 3),
                            types.expected
                        );
                        return Err(error);
                    }
                    Err(error) => return Err(error),
                };
                resolved_actual = Some(actual.clone());
                out.set_actual(*expr, actual)?;
            }
            if let Some(expected) = &types.expected {
                match resolver.resolve(expected) {
                    Ok(expected) => out.set_expected(*expr, expected)?,
                    Err(SpecializeError::UndeterminedTypeSlot { .. })
                        if self.contextual_value_fetches.contains(expr)
                            && resolved_actual
                                .as_ref()
                                .is_some_and(|actual| !type_contains_open_var(actual)) =>
                    {
                        out.set_expected(
                            *expr,
                            resolved_actual
                                .clone()
                                .expect("checked resolved actual for contextual fallback"),
                        )?;
                    }
                    Err(SpecializeError::UndeterminedTypeSlot { .. })
                        if let Some(expected) = resolved_actual.as_ref().and_then(|actual| {
                            erased_expected_for_effectful_actual(expected, actual)
                        }) =>
                    {
                        out.set_expected(*expr, expected)?;
                    }
                    Err(SpecializeError::UndeterminedTypeSlot { .. })
                        if resolved_actual.as_ref().is_some_and(|actual| {
                            unresolved_expected_can_use_actual(expected, actual)
                        }) =>
                    {
                        out.set_expected(
                            *expr,
                            resolved_actual
                                .clone()
                                .expect("checked resolved actual for fallback"),
                        )?;
                    }
                    Err(SpecializeError::UndeterminedTypeSlot { .. })
                        if types.actual.as_ref().is_some_and(|actual| {
                            unresolved_actual_boundary_can_be_erased(
                                graph.arena,
                                *expr,
                                actual,
                                Some(expected),
                            )
                        }) =>
                    {
                        continue;
                    }
                    Err(error @ SpecializeError::UndeterminedTypeSlot { .. }) => {
                        eprintln!(
                            "finalize expected failed expr={:?} tree={} actual={:?} expected={expected:?} error={error:?}",
                            expr,
                            debug_expr_tree(graph.arena, *expr, 3),
                            types.actual
                        );
                        return Err(error);
                    }
                    Err(error) => return Err(error),
                }
            }
        }
        Ok(out)
    }
}

fn unresolved_exact_boundary_can_be_erased(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
) -> bool {
    if let poly_expr::Expr::PrimitiveOp(op) = arena.expr(expr) {
        return !matches!(op, poly_expr::PrimitiveOp::ListViewRaw);
    }
    let poly_expr::Expr::Var(ref_id) = arena.expr(expr) else {
        return false;
    };
    let Some(def) = arena.ref_target(*ref_id) else {
        return false;
    };
    if arena.constructors.contains_key(&def) {
        return false;
    }
    if arena.effect_operations.contains_key(&def) {
        return true;
    }
    match arena.defs.get(def) {
        Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => true,
        Some(poly_expr::Def::Let { .. }) => false,
        _ => false,
    }
}

fn unresolved_actual_boundary_can_be_erased(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
    actual: &Type,
    expected: Option<&Type>,
) -> bool {
    match arena.expr(expr) {
        poly_expr::Expr::App(_, _) => {
            expected.is_some_and(|expected| function_boundary_shapes_match(actual, expected))
        }
        _ => false,
    }
}

fn function_boundary_shapes_match(actual: &Type, expected: &Type) -> bool {
    matches!(
        (runtime_value_shape(actual), runtime_value_shape(expected)),
        (Type::Fun { .. }, Type::Fun { .. })
    )
}

fn unresolved_expected_can_use_actual(expected: &Type, actual: &Type) -> bool {
    match (expected, actual) {
        (Type::Thunk { .. }, Type::Thunk { .. }) => {
            type_contains_open_var(expected) && !type_contains_open_var(actual)
        }
        (Type::PolyVariant(expected), Type::PolyVariant(actual)) => actual.iter().all(|actual| {
            expected.iter().any(|expected| {
                expected.name == actual.name && expected.payloads.len() == actual.payloads.len()
            })
        }),
        _ => false,
    }
}

fn erased_expected_for_effectful_actual(expected: &Type, actual: &Type) -> Option<Type> {
    let (
        Type::OpenVar(_),
        Type::Thunk {
            value: actual_value,
            ..
        },
    ) = (expected, actual)
    else {
        return None;
    };
    Some(actual_value.as_ref().clone())
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
            if role == ExprTypeRole::Expected
                && let Some(merged) = merge_expr_expected(existing, &ty)
            {
                *existing = merged;
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

fn merge_expr_expected(existing: &Type, incoming: &Type) -> Option<Type> {
    if existing == incoming {
        return Some(existing.clone());
    }
    match (existing, incoming) {
        (Type::OpenVar(_), Type::OpenVar(_)) => Some(existing.clone()),
        (Type::OpenVar(_), incoming) if !type_contains_open_var(incoming) => Some(incoming.clone()),
        (existing, Type::OpenVar(_)) if !type_contains_open_var(existing) => Some(existing.clone()),
        (
            Type::Con {
                path: existing_path,
                args: existing_args,
            },
            Type::Con {
                path: incoming_path,
                args: incoming_args,
            },
        ) if existing_path == incoming_path && existing_args.len() == incoming_args.len() => {
            let args = existing_args
                .iter()
                .zip(incoming_args)
                .map(|(existing, incoming)| merge_expr_expected(existing, incoming))
                .collect::<Option<Vec<_>>>()?;
            Some(Type::Con {
                path: existing_path.clone(),
                args,
            })
        }
        (
            Type::Fun {
                arg: existing_arg,
                arg_effect: existing_arg_effect,
                ret_effect: existing_ret_effect,
                ret: existing_ret,
            },
            Type::Fun {
                arg: incoming_arg,
                arg_effect: incoming_arg_effect,
                ret_effect: incoming_ret_effect,
                ret: incoming_ret,
            },
        ) => Some(Type::Fun {
            arg: Box::new(merge_expr_expected(existing_arg, incoming_arg)?),
            arg_effect: Box::new(merge_expr_expected(
                existing_arg_effect,
                incoming_arg_effect,
            )?),
            ret_effect: Box::new(merge_expr_expected(
                existing_ret_effect,
                incoming_ret_effect,
            )?),
            ret: Box::new(merge_expr_expected(existing_ret, incoming_ret)?),
        }),
        (
            Type::Thunk {
                effect: existing_effect,
                value: existing_value,
            },
            Type::Thunk {
                effect: incoming_effect,
                value: incoming_value,
            },
        ) => Some(Type::Thunk {
            effect: Box::new(merge_expr_expected(existing_effect, incoming_effect)?),
            value: Box::new(merge_expr_expected(existing_value, incoming_value)?),
        }),
        (Type::EffectRow(existing_items), Type::EffectRow(incoming_items))
            if existing_items.len() == incoming_items.len() =>
        {
            Some(Type::EffectRow(
                existing_items
                    .iter()
                    .zip(incoming_items)
                    .map(|(existing, incoming)| merge_expr_expected(existing, incoming))
                    .collect::<Option<Vec<_>>>()?,
            ))
        }
        (Type::Tuple(existing_items), Type::Tuple(incoming_items))
            if existing_items.len() == incoming_items.len() =>
        {
            Some(Type::Tuple(
                existing_items
                    .iter()
                    .zip(incoming_items)
                    .map(|(existing, incoming)| merge_expr_expected(existing, incoming))
                    .collect::<Option<Vec<_>>>()?,
            ))
        }
        (existing, incoming) => match (
            type_contains_open_var(existing),
            type_contains_open_var(incoming),
        ) {
            (true, false) => Some(incoming.clone()),
            (false, true) => Some(existing.clone()),
            _ => None,
        },
    }
}

fn merge_expr_expected_for_solver(existing: &Type, incoming: &Type) -> Option<Type> {
    merge_expr_expected(existing, incoming).or_else(|| {
        if existing == incoming {
            return Some(existing.clone());
        }
        match (existing, incoming) {
            (Type::Any, incoming) => Some(incoming.clone()),
            (existing, Type::Any) => Some(existing.clone()),
            (Type::Never, _) | (_, Type::Never) => Some(Type::Never),
            (Type::OpenVar(_), incoming) => Some(incoming.clone()),
            (existing, Type::OpenVar(_)) => Some(existing.clone()),
            (
                Type::Con {
                    path: existing_path,
                    args: existing_args,
                },
                Type::Con {
                    path: incoming_path,
                    args: incoming_args,
                },
            ) if existing_path == incoming_path && existing_args.len() == incoming_args.len() => {
                let args = existing_args
                    .iter()
                    .zip(incoming_args)
                    .map(|(existing, incoming)| merge_expr_expected_for_solver(existing, incoming))
                    .collect::<Option<Vec<_>>>()?;
                Some(Type::Con {
                    path: existing_path.clone(),
                    args,
                })
            }
            (
                Type::Fun {
                    arg: existing_arg,
                    arg_effect: existing_arg_effect,
                    ret_effect: existing_ret_effect,
                    ret: existing_ret,
                },
                Type::Fun {
                    arg: incoming_arg,
                    arg_effect: incoming_arg_effect,
                    ret_effect: incoming_ret_effect,
                    ret: incoming_ret,
                },
            ) => Some(Type::Fun {
                arg: Box::new(merge_expr_expected_for_solver(existing_arg, incoming_arg)?),
                arg_effect: Box::new(merge_expr_expected_for_solver(
                    existing_arg_effect,
                    incoming_arg_effect,
                )?),
                ret_effect: Box::new(merge_expr_expected_for_solver(
                    existing_ret_effect,
                    incoming_ret_effect,
                )?),
                ret: Box::new(merge_expr_expected_for_solver(existing_ret, incoming_ret)?),
            }),
            (
                Type::Thunk {
                    effect: existing_effect,
                    value: existing_value,
                },
                Type::Thunk {
                    effect: incoming_effect,
                    value: incoming_value,
                },
            ) => Some(Type::Thunk {
                effect: Box::new(merge_expr_expected_for_solver(
                    existing_effect,
                    incoming_effect,
                )?),
                value: Box::new(merge_expr_expected_for_solver(
                    existing_value,
                    incoming_value,
                )?),
            }),
            (Type::EffectRow(existing_items), Type::EffectRow(incoming_items))
                if existing_items.len() == incoming_items.len() =>
            {
                Some(Type::EffectRow(
                    existing_items
                        .iter()
                        .zip(incoming_items)
                        .map(|(existing, incoming)| {
                            merge_expr_expected_for_solver(existing, incoming)
                        })
                        .collect::<Option<Vec<_>>>()?,
                ))
            }
            (Type::Tuple(existing_items), Type::Tuple(incoming_items))
                if existing_items.len() == incoming_items.len() =>
            {
                Some(Type::Tuple(
                    existing_items
                        .iter()
                        .zip(incoming_items)
                        .map(|(existing, incoming)| {
                            merge_expr_expected_for_solver(existing, incoming)
                        })
                        .collect::<Option<Vec<_>>>()?,
                ))
            }
            (existing, incoming) => match (
                type_contains_open_var(existing),
                type_contains_open_var(incoming),
            ) {
                (true, false) => Some(incoming.clone()),
                (false, true) => Some(existing.clone()),
                _ => None,
            },
        }
    })
}

struct LocalLetSchemeType {
    def: poly_expr::DefId,
    monomorphic_ty: Option<Type>,
}

impl LocalLetSchemeType {
    fn is_polymorphic(&self) -> bool {
        self.monomorphic_ty.is_none()
    }

    fn expr_expected(&self) -> Option<Type> {
        self.monomorphic_ty.clone()
    }

    fn binding_type(self) -> Option<Type> {
        self.monomorphic_ty
    }

    fn prebound_type(&self) -> Option<Type> {
        self.monomorphic_ty.clone()
    }
}

pub(crate) fn solve_expr(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
    expected: Option<&Type>,
) -> Result<ExprTypePlan, SpecializeError> {
    solve_expr_with_active_def(arena, expr, expected, None)
}

pub(crate) fn solve_def_expr(
    arena: &poly_expr::Arena,
    def: poly_expr::DefId,
    expr: poly_expr::ExprId,
    expected: &Type,
) -> Result<ExprTypePlan, SpecializeError> {
    solve_expr_with_active_def(arena, expr, Some(expected), Some(def))
}

fn solve_expr_with_active_def(
    arena: &poly_expr::Arena,
    expr: poly_expr::ExprId,
    expected: Option<&Type>,
    active_def: Option<poly_expr::DefId>,
) -> Result<ExprTypePlan, SpecializeError> {
    let mut solver = ExprTypeSolver {
        arena,
        graph: ConstraintGraph::new(arena),
        plan: ExprTypePlan::default(),
        local_types: HashMap::new(),
        constraining_def_types: HashMap::new(),
    };
    let expected = expected
        .cloned()
        .map(|expected| solver.freshen_external_type(expected, TypeSlotKind::Value));
    if let Some(active_def) = active_def {
        if let Some(expected) = &expected {
            solver
                .constraining_def_types
                .insert(active_def, expected.clone());
        }
    }
    solver.expr(expr, expected)?;
    solver.graph.resolve_role_demands()?;
    solver.plan.finalize(&solver.graph)
}

struct ExprTypeSolver<'a> {
    arena: &'a poly_expr::Arena,
    graph: ConstraintGraph<'a>,
    plan: ExprTypePlan,
    local_types: HashMap<poly_expr::DefId, Type>,
    constraining_def_types: HashMap<poly_expr::DefId, Type>,
}

impl<'a> ExprTypeSolver<'a> {
    fn expr(
        &mut self,
        expr: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        if expected.is_some() && matches!(self.arena.expr(expr), poly_expr::Expr::Var(_)) {
            self.plan.mark_contextual_value_fetch(expr);
        }

        if let Some(expected) = expected {
            if type_mentions_ref_update_unit(&expected) {
                eprintln!(
                    "expr {:?} {} expected ref_update_unit {:?} tree={}",
                    expr,
                    expr_kind_label(self.arena.expr(expr)),
                    expected,
                    debug_expr_tree(self.arena, expr, 3)
                );
            }
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

    fn set_expr_expected(
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

    fn freshen_external_type(&mut self, ty: Type, context: TypeSlotKind) -> Type {
        let mut vars = HashMap::new();
        self.freshen_external_type_with_vars(ty, context, &mut vars)
    }

    fn freshen_external_type_with_vars(
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

    fn type_open_vars_are_graph_slots(&self, ty: &Type) -> bool {
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

    fn infer_expr(
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
        if let poly_expr::Expr::Var(ref_id) = self.arena.expr(callee)
            && let Some(def) = self.arena.ref_target(*ref_id)
            && let Some(operation) = self.arena.effect_operations.get(&def)
        {
            eprintln!(
                "effect op call expr={:?} callee={:?} path={:?} expected={:?}",
                expr, callee, operation.path, expected
            );
        }
        let callee_expected = expected
            .as_ref()
            .and_then(|ret| self.primitive_spine_callee_expected(callee, ret.clone()));
        let callee_ty = self.expr(callee, callee_expected)?;
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

    fn call_callee_ret_expected(
        &mut self,
        ret_ty: &Type,
        expected: Option<&Type>,
        fresh_result: bool,
    ) -> Type {
        if runtime_value_is_never(ret_ty) {
            return ret_ty.clone();
        }
        if expected.is_none() && (!fresh_result || !type_contains_open_var(ret_ty)) {
            return ret_ty.clone();
        }
        let (_, ret_effect) = split_runtime_computation_shape(ret_ty.clone());
        let expected_value = match expected {
            Some(expected) => split_runtime_computation_shape(expected.clone()).0,
            None => self.fresh_value_slot(),
        };
        types::runtime_shape(ret_effect, expected_value)
    }

    fn apply_known_function_arg(
        &mut self,
        callee: poly_expr::ExprId,
        arg: poly_expr::ExprId,
        arg_ty: Type,
        ret_ty: Type,
        callee_effect: Type,
        expected: Option<&Type>,
    ) -> Result<(Type, bool), SpecializeError> {
        let declared_arg_ty = arg_ty.clone();
        let (arg_value, arg_effect) = split_runtime_computation_shape(arg_ty.clone());
        self.constrain_callee_pattern_defaults(callee, arg_value.clone())?;
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
        let narrows_arg =
            value_argument_narrows_polyvariant(&declared_arg_ty, &callee_arg_expected);
        let expected_ret = self.call_callee_ret_expected(&ret_ty, expected, narrows_arg);
        self.constrain_apply_callee(
            callee,
            types::pure_function_type(callee_arg_expected, expected_ret.clone()),
        )?;
        let has_evaluation_effect =
            !callee_effect.is_pure_effect() || !call_arg_effect.is_pure_effect();
        let result = self.call_result_shape(expected_ret, [callee_effect, call_arg_effect])?;
        self.graph.constrain_subtype(ret_ty, result.clone())?;
        Ok((result, has_evaluation_effect))
    }

    fn constrain_apply_callee(
        &mut self,
        callee: poly_expr::ExprId,
        expected: Type,
    ) -> Result<(), SpecializeError> {
        if self.plan.expected(callee).is_none() {
            if self.plan.actual(callee).is_some() && self.expr_can_refine_with_expected(callee) {
                self.set_expr_expected(callee, expected.clone())?;
                let refined = self.infer_expr(callee, Some(expected.clone()))?;
                return self.constrain_expr_boundary(refined, expected);
            }
            self.expr(callee, Some(expected))?;
            return Ok(());
        }
        let actual = self.expr(callee, None)?;
        self.constrain_expr_boundary(actual, expected)
    }

    fn expr_can_refine_with_expected(&self, expr: poly_expr::ExprId) -> bool {
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

    fn constrain_callee_pattern_defaults(
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

    fn callee_lambda_param(&self, callee: poly_expr::ExprId) -> Option<poly_expr::PatId> {
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

    fn expr_as_call_value(
        &mut self,
        expr: poly_expr::ExprId,
        expected_value: Type,
    ) -> Result<CallArgument, SpecializeError> {
        self.set_expr_expected(expr, expected_value.clone())?;
        let actual = if let Some(actual) = self.plan.actual(expr).cloned() {
            actual
        } else {
            let actual = self.infer_expr(expr, Some(expected_value.clone()))?;
            self.plan.set_actual(expr, actual.clone())?;
            actual
        };
        let (actual_value, actual_effect) = split_runtime_computation_shape(actual);
        self.graph
            .constrain_subtype(actual_value.clone(), expected_value)?;
        Ok(CallArgument {
            value: actual_value,
            effect: actual_effect,
        })
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

    fn ref_set_type(
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

    fn case_arm_reachable(&self, pat: poly_expr::PatId, scrutinee_ty: &Type) -> bool {
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
        let mut handled_effects = Vec::new();
        let mut effects = Vec::new();
        for arm in arms {
            if let Some(handled) =
                self.bind_catch_arm(arm, scrutinee_value.clone(), scrutinee_effect.clone())?
            {
                handled_effects.push(handled);
            }
            if let Some(guard) = arm.guard {
                let guard_actual = self.expr(guard, Some(bool_type()))?;
                effects.push(split_runtime_computation_shape(guard_actual).1);
            }
            let arm_actual = self.expr(arm.body, Some(result.clone()))?;
            effects.push(split_runtime_computation_shape(arm_actual).1);
        }
        effects.push(catch_residual_effect(scrutinee_effect, &handled_effects));
        let effect = self.join_call_effects(effects)?;
        let result = types::runtime_shape(effect, result);
        if matches!(result, Type::Thunk { .. }) {
            self.plan.mark_raw_thunk_computation(body);
        }
        Ok(result)
    }

    fn bind_catch_arm(
        &mut self,
        arm: &poly_expr::CatchArm,
        scrutinee_value: Type,
        scrutinee_effect: Type,
    ) -> Result<Option<Type>, SpecializeError> {
        let Some(continuation) = arm.continuation else {
            self.bind_pat(arm.pat, scrutinee_value)?;
            return Ok(None);
        };

        let operation =
            self.catch_operation_types(arm.operation.as_ref(), scrutinee_effect.clone())?;
        self.bind_pat(arm.pat, operation.payload)?;
        let continuation_ret = types::runtime_shape(operation.residual_effect, scrutinee_value);
        self.bind_pat(
            continuation,
            types::pure_function_type(operation.continuation_input, continuation_ret),
        )?;
        Ok(Some(operation.effect))
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
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let Some(def) = operation.def else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
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
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let operation_ty = self.instantiate_scheme(def, scheme)?;
        let Some((payload, ret)) = function_runtime_parts(&operation_ty) else {
            let payload = self.fresh_value_slot();
            return Ok(CatchOperationTypes {
                payload: payload.clone(),
                continuation_input: payload,
                effect: Type::pure_effect(),
                residual_effect: scrutinee_effect,
            });
        };
        let (continuation_input, operation_effect) = split_runtime_computation_shape(ret);
        let handled_effect = self
            .constrain_operation_effect_to_scrutinee(operation_effect, scrutinee_effect.clone())?;
        let residual_effect =
            catch_residual_effect(scrutinee_effect, std::slice::from_ref(&handled_effect));
        Ok(CatchOperationTypes {
            payload,
            continuation_input,
            effect: handled_effect,
            residual_effect,
        })
    }

    fn constrain_operation_effect_to_scrutinee(
        &mut self,
        operation_effect: Type,
        scrutinee_effect: Type,
    ) -> Result<Type, SpecializeError> {
        if let (Type::EffectRow(operation_items), Type::EffectRow(scrutinee_items)) =
            (&operation_effect, &scrutinee_effect)
        {
            let mut constrained = false;
            let mut handled_items = Vec::new();
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
                handled_items.push(scrutinee_item);
            }
            if constrained {
                return Ok(Type::EffectRow(handled_items));
            }
        }
        self.graph
            .constrain_subtype(operation_effect.clone(), scrutinee_effect.clone())?;
        self.graph
            .constrain_subtype(scrutinee_effect, operation_effect.clone())?;
        Ok(operation_effect)
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
        Ok(Type::Tuple(item_types))
    }

    fn block_type(
        &mut self,
        expr: Option<poly_expr::ExprId>,
        stmts: &[poly_expr::Stmt],
        tail: Option<poly_expr::ExprId>,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let expected_result = expected.unwrap_or_else(|| self.fresh_value_slot());
        let (result_value, _) = split_runtime_computation_shape(expected_result);
        let mut effects = Vec::new();
        for stmt in stmts {
            match stmt {
                poly_expr::Stmt::Let(_, pat, value) => {
                    let scheme_type = self.local_let_scheme_type(*pat)?;
                    let previous_prebound_local =
                        self.prebind_local_let_scheme(scheme_type.as_ref());
                    if scheme_type
                        .as_ref()
                        .is_some_and(LocalLetSchemeType::is_polymorphic)
                        && self.local_let_value_can_defer(*value)
                    {
                        effects.push(Type::pure_effect());
                        continue;
                    }
                    let expected = scheme_type
                        .as_ref()
                        .and_then(|scheme| scheme.expr_expected());
                    let value_ty = match self.expr(*value, expected) {
                        Ok(value_ty) => value_ty,
                        Err(error) => {
                            self.restore_prebound_local(previous_prebound_local);
                            return Err(error);
                        }
                    };
                    let (value_ty, effect) = split_runtime_computation_shape(value_ty);
                    if !effect.is_pure_effect() {
                        if let Err(error) = self.expr(*value, Some(value_ty.clone())) {
                            self.restore_prebound_local(previous_prebound_local);
                            return Err(error);
                        }
                    }
                    effects.push(effect);
                    let binding_ty = if let Some(scheme) = scheme_type {
                        scheme.binding_type()
                    } else {
                        Some(value_ty)
                    };
                    if let Some(binding_ty) = binding_ty {
                        self.bind_pat(*pat, binding_ty)?;
                    }
                }
                poly_expr::Stmt::Expr(value) => {
                    let value_ty = self.expr(*value, None)?;
                    effects.push(split_runtime_computation_shape(value_ty).1);
                }
                poly_expr::Stmt::Module(_, body) => {
                    let value_ty = self.block_type(None, body, None, None)?;
                    effects.push(split_runtime_computation_shape(value_ty).1);
                }
            }
        }
        let tail_ty = match tail {
            Some(tail) => self.expr(tail, Some(result_value.clone()))?,
            None => Type::unit(),
        };
        effects.push(split_runtime_computation_shape(tail_ty).1);
        let effect = self.join_call_effects(effects)?;
        let result = types::runtime_shape(effect, result_value);
        if let Some(expr) = expr
            && matches!(result, Type::Thunk { .. })
        {
            self.plan.mark_raw_thunk_computation(expr);
        }
        Ok(result)
    }

    fn prebind_local_let_scheme(
        &mut self,
        scheme_type: Option<&LocalLetSchemeType>,
    ) -> Option<(poly_expr::DefId, Option<Type>)> {
        let scheme_type = scheme_type?;
        let ty = scheme_type.prebound_type()?;
        Some((
            scheme_type.def,
            self.local_types.insert(scheme_type.def, ty),
        ))
    }

    fn restore_prebound_local(&mut self, previous: Option<(poly_expr::DefId, Option<Type>)>) {
        let Some((def, previous_ty)) = previous else {
            return;
        };
        match previous_ty {
            Some(previous_ty) => {
                self.local_types.insert(def, previous_ty);
            }
            None => {
                self.local_types.remove(&def);
            }
        }
    }

    fn local_let_scheme_type(
        &mut self,
        pat: poly_expr::PatId,
    ) -> Result<Option<LocalLetSchemeType>, SpecializeError> {
        let poly_expr::Pat::Var(def) = self.arena.pat(pat) else {
            return Ok(None);
        };
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(*def)
        else {
            return Ok(None);
        };
        if !scheme.quantifiers.is_empty() || !scheme.stack_quantifiers.is_empty() {
            return Ok(Some(LocalLetSchemeType {
                def: *def,
                monomorphic_ty: None,
            }));
        }
        let ty = self.instantiate_monomorphic_scheme(*def, scheme)?;
        Ok(Some(LocalLetSchemeType {
            def: *def,
            monomorphic_ty: Some(ty),
        }))
    }

    fn local_let_value_can_defer(&self, value: poly_expr::ExprId) -> bool {
        matches!(self.arena.expr(value), poly_expr::Expr::Lambda(_, _))
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
                self.method_select_type(base, def, expected, MethodDemandMode::Emit)
            }
            Some(poly_expr::SelectResolution::TypeclassMethod { member }) => self
                .method_select_type(
                    base,
                    member,
                    expected,
                    MethodDemandMode::DeferWithoutExpected,
                ),
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
        expected: Option<Type>,
        demand_mode: MethodDemandMode,
    ) -> Result<Type, SpecializeError> {
        let Some(poly_expr::Def::Let {
            scheme: Some(scheme),
            ..
        }) = self.arena.defs.get(def)
        else {
            self.expr(base, None)?;
            return Ok(self.fresh_value_slot());
        };
        let method_ty = match expected.as_ref() {
            Some(expected) => {
                let expected = self.selected_method_scheme_expected(expected.clone());
                self.instantiate_scheme_with_expected(def, scheme, &expected)?
            }
            None if demand_mode == MethodDemandMode::DeferWithoutExpected => {
                self.instantiate_scheme_type_only(def, scheme)?
            }
            None => self.instantiate_scheme(def, scheme)?,
        };
        let Some((receiver_ty, result_ty)) = function_runtime_parts(&method_ty) else {
            self.expr(base, None)?;
            return Ok(self.fresh_value_slot());
        };
        self.expr(base, Some(receiver_ty))?;
        Ok(result_ty)
    }

    fn selected_method_scheme_expected(&mut self, selected: Type) -> Type {
        types::pure_function_type(self.fresh_value_slot(), selected)
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
                if def.0 == 711 {
                    eprintln!("bind target def={def:?} ty={ty:?}");
                }
                self.local_types.insert(*def, ty);
            }
            PolyPat::As(inner, def) => {
                if def.0 == 711 {
                    eprintln!("bind target as def={def:?} ty={ty:?}");
                }
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
        fields: &[poly_expr::RecordPatField],
        spread: &poly_expr::RecordSpread<poly_expr::DefId>,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        let Type::Record(record_fields) = ty else {
            for field in fields {
                let field_ty = self.record_pattern_default_type(field, None)?;
                self.bind_pat(field.pat, field_ty)?;
            }
            if let Some(def) = record_spread_def(spread) {
                let spread_ty = self.fresh_value_slot();
                self.local_types.insert(def, spread_ty);
            }
            return Ok(());
        };

        for field in fields {
            let expected =
                record_field_type(&record_fields, &field.name).map(|field| field.value.clone());
            let field_ty = self.record_pattern_default_type(field, expected)?;
            self.bind_pat(field.pat, field_ty)?;
        }
        if let Some(def) = record_spread_def(spread) {
            let captured = record_fields
                .into_iter()
                .filter(|field| !fields.iter().any(|pattern| pattern.name == field.name))
                .collect::<Vec<_>>();
            self.local_types.insert(def, Type::Record(captured));
        }
        Ok(())
    }

    fn record_pattern_default_type(
        &mut self,
        field: &poly_expr::RecordPatField,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let Some(default) = field.default else {
            return Ok(expected.unwrap_or_else(|| self.fresh_value_slot()));
        };
        let expected = expected.unwrap_or_else(|| self.fresh_value_slot());
        let actual = self.expr(default, Some(expected.clone()))?;
        self.graph.constrain_subtype(actual.clone(), expected)?;
        Ok(actual)
    }

    fn constrain_pat_defaults(
        &mut self,
        pat: poly_expr::PatId,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match self.arena.pat(pat) {
            PolyPat::Wild | PolyPat::Lit(_) | PolyPat::Ref(_) => {}
            PolyPat::Var(def) => {
                if def.0 == 711 {
                    eprintln!("default-bind target def={def:?} ty={ty:?}");
                }
                self.local_types.insert(*def, ty);
            }
            PolyPat::As(inner, def) => {
                if def.0 == 711 {
                    eprintln!("default-bind target as def={def:?} ty={ty:?}");
                }
                self.local_types.insert(*def, ty.clone());
                self.constrain_pat_defaults(*inner, ty)?;
            }
            PolyPat::Tuple(items) => {
                if let Type::Tuple(item_types) = ty {
                    for (item, item_ty) in items.iter().zip(item_types) {
                        self.constrain_pat_defaults(*item, item_ty)?;
                    }
                }
            }
            PolyPat::List {
                prefix,
                spread,
                suffix,
            } => {
                let item_ty = list_item_type(&ty).unwrap_or_else(|| self.fresh_value_slot());
                for item in prefix.iter().chain(suffix) {
                    self.constrain_pat_defaults(*item, item_ty.clone())?;
                }
                if let Some(spread) = spread {
                    self.constrain_pat_defaults(*spread, ty)?;
                }
            }
            PolyPat::Record { fields, spread } => {
                self.constrain_record_pat_defaults(fields, spread, ty)?;
            }
            PolyPat::PolyVariant(tag, payloads) => {
                if let Type::PolyVariant(variants) = ty
                    && let Some(variant) = variants.iter().find(|variant| {
                        variant.name == *tag && variant.payloads.len() == payloads.len()
                    })
                {
                    for (payload, payload_ty) in payloads.iter().zip(&variant.payloads) {
                        self.constrain_pat_defaults(*payload, payload_ty.clone())?;
                    }
                }
            }
            PolyPat::Con(_, payloads) => {
                for payload in payloads {
                    let payload_ty = self.fresh_value_slot();
                    self.constrain_pat_defaults(*payload, payload_ty)?;
                }
            }
            PolyPat::Or(left, right) => {
                self.constrain_pat_defaults(*left, ty.clone())?;
                self.constrain_pat_defaults(*right, ty)?;
            }
        }
        Ok(())
    }

    fn constrain_record_pat_defaults(
        &mut self,
        fields: &[poly_expr::RecordPatField],
        spread: &poly_expr::RecordSpread<poly_expr::DefId>,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        let Type::Record(record_fields) = ty else {
            for field in fields {
                let field_ty = self.fresh_value_slot();
                self.constrain_default_expr(field.default, field_ty.clone())?;
                self.constrain_pat_defaults(field.pat, field_ty)?;
            }
            if let Some(def) = record_spread_def(spread) {
                let spread_ty = self.fresh_value_slot();
                self.local_types.insert(def, spread_ty);
            }
            return Ok(());
        };

        for field in fields {
            let field_ty = record_field_type(&record_fields, &field.name)
                .map(|field| field.value.clone())
                .unwrap_or_else(|| self.fresh_value_slot());
            self.constrain_default_expr(field.default, field_ty.clone())?;
            self.constrain_pat_defaults(field.pat, field_ty)?;
        }
        if let Some(def) = record_spread_def(spread) {
            let captured = record_fields
                .into_iter()
                .filter(|field| !fields.iter().any(|pattern| pattern.name == field.name))
                .collect::<Vec<_>>();
            self.local_types.insert(def, Type::Record(captured));
        }
        Ok(())
    }

    fn constrain_default_expr(
        &mut self,
        default: Option<poly_expr::ExprId>,
        expected: Type,
    ) -> Result<(), SpecializeError> {
        let Some(default) = default else {
            return Ok(());
        };
        let actual = self.infer_expr(default, Some(expected.clone()))?;
        self.constrain_expr_boundary(actual, expected)
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

    fn var_type(
        &mut self,
        ref_id: poly_expr::RefId,
        expected: Option<&Type>,
    ) -> Result<Type, SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        if let Some(local_ty) = self.local_types.get(&def).cloned() {
            if def.0 == 711 {
                eprintln!("var target local def={def:?} ty={local_ty:?}");
            }
            return Ok(local_ty);
        }
        if let Some(active_ty) = self.constraining_def_types.get(&def).cloned() {
            if def.0 == 711 {
                eprintln!("var target active def={def:?} ty={active_ty:?}");
            }
            return Ok(active_ty);
        }
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                body,
                ..
            }) => {
                let ty = match expected {
                    Some(expected) => {
                        self.instantiate_scheme_with_expected(def, scheme, expected)?
                    }
                    None => self.instantiate_scheme(def, scheme)?,
                };
                if let Some(body) = body {
                    self.constrain_instantiated_def_body(def, *body, ty.clone())?;
                }
                Ok(ty)
            }
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

    fn constrain_instantiated_def_body(
        &mut self,
        def: poly_expr::DefId,
        body: poly_expr::ExprId,
        ty: Type,
    ) -> Result<(), SpecializeError> {
        if self.constraining_def_types.contains_key(&def) {
            return Ok(());
        }

        let local_types = self.local_types.clone();
        let plan = std::mem::take(&mut self.plan);
        self.constraining_def_types.insert(def, ty.clone());
        let result = self.expr(body, Some(ty)).map(|_| ());
        self.constraining_def_types.remove(&def);
        self.local_types = local_types;
        self.plan = plan;
        result
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

    fn instantiate_monomorphic_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let instantiated = types::instantiate_monomorphic_scheme_with_fresh_and_roles(
            self.arena,
            def,
            scheme,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.fresh_value_slot(),
                types::SchemeQuantifierKind::Effect => self.fresh_effect_slot(),
            },
        )?;
        self.graph.add_role_demands(instantiated.role_predicates);
        self.graph
            .constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    fn instantiate_scheme_with_expected(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
        expected: &Type,
    ) -> Result<Type, SpecializeError> {
        let instantiated = types::instantiate_scheme_with_expected_fresh_and_roles(
            self.arena,
            def,
            scheme,
            expected,
            |kind| match kind {
                types::SchemeQuantifierKind::Value => self.fresh_value_slot(),
                types::SchemeQuantifierKind::Effect => self.fresh_effect_slot(),
            },
        )?;
        self.graph.add_role_demands(instantiated.role_predicates);
        self.graph
            .constrain_recursive_bounds(instantiated.recursive_bounds)?;
        Ok(instantiated.ty)
    }

    fn instantiate_scheme_type_only(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let instantiated =
            types::instantiate_scheme_with_fresh_and_roles(self.arena, def, scheme, |kind| {
                match kind {
                    types::SchemeQuantifierKind::Value => self.fresh_value_slot(),
                    types::SchemeQuantifierKind::Effect => self.fresh_effect_slot(),
                }
            })?;
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum TypeSlotKind {
    Value,
    Effect,
}

struct CatchOperationTypes {
    payload: Type,
    continuation_input: Type,
    effect: Type,
    residual_effect: Type,
}

struct CallArgument {
    value: Type,
    effect: Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum MethodDemandMode {
    Emit,
    DeferWithoutExpected,
}

struct ConstraintGraph<'a> {
    arena: &'a poly_expr::Arena,
    slots: Vec<TypeSlot>,
    role_demands: Vec<types::InstantiatedRolePredicate>,
    pending: VecDeque<SubtypeConstraint>,
}

impl<'a> ConstraintGraph<'a> {
    fn new(arena: &'a poly_expr::Arena) -> Self {
        Self {
            arena,
            slots: Vec::new(),
            role_demands: Vec::new(),
            pending: VecDeque::new(),
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
            self.solve_constraints()?;
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

    #[track_caller]
    fn constrain_subtype(&mut self, lower: Type, upper: Type) -> Result<(), SpecializeError> {
        if type_mentions_ref_update_unit(&lower) || type_mentions_ref_update_unit(&upper) {
            let location = std::panic::Location::caller();
            eprintln!(
                "ref_update_unit constraint at {}:{} lower={lower:?} upper={upper:?}",
                location.file(),
                location.line()
            );
        }
        if lower != upper {
            self.pending.push_back(SubtypeConstraint { lower, upper });
        }
        Ok(())
    }

    fn solve_constraints(&mut self) -> Result<(), SpecializeError> {
        while let Some(constraint) = self.pending.pop_front() {
            self.process_subtype(constraint.lower, constraint.upper)?;
        }
        Ok(())
    }

    fn solve_type_graph(&self) -> Result<GraphSolution, SpecializeError> {
        let mut solution = GraphSolution::new(self.slots.len());
        loop {
            let mut progressed = false;
            for slot in 0..self.slots.len() {
                if solution.slots[slot].is_some() {
                    continue;
                }
                let mut resolver = TypeResolver::with_solution(self, &solution);
                if let Some(ty) = resolver.try_slot_solution(slot as u32)? {
                    solution.slots[slot] = Some(ty);
                    progressed = true;
                }
            }
            if !progressed {
                return Ok(solution);
            }
        }
    }

    fn process_subtype(&mut self, lower: Type, upper: Type) -> Result<(), SpecializeError> {
        if lower == upper {
            return Ok(());
        }
        match (lower, upper) {
            (Type::Never, _) | (_, Type::Any) => Ok(()),
            (Type::OpenVar(lower), Type::OpenVar(upper)) => self.add_edge(lower, upper),
            (Type::Thunk { value, .. }, Type::OpenVar(slot)) if self.slot_is_value(slot) => {
                self.constrain_subtype(*value, Type::OpenVar(slot))
            }
            (
                Type::OpenVar(slot),
                Type::Thunk {
                    effect: upper_effect,
                    value: upper_value,
                },
            ) if self.slot_is_value(slot) => {
                self.constrain_subtype(Type::OpenVar(slot), *upper_value)?;
                self.constrain_subtype(Type::pure_effect(), *upper_effect)
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct SubtypeConstraint {
    lower: Type,
    upper: Type,
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

#[derive(Debug, Clone)]
struct GraphSolution {
    slots: Vec<Option<Type>>,
}

impl GraphSolution {
    fn new(slot_count: usize) -> Self {
        Self {
            slots: vec![None; slot_count],
        }
    }

    fn get(&self, slot: u32) -> Result<Option<&Type>, SpecializeError> {
        self.slots
            .get(slot as usize)
            .map(Option::as_ref)
            .ok_or(SpecializeError::InvalidTypeSlot { slot })
    }
}

struct TypeResolver<'graph, 'arena, 'solution> {
    graph: &'graph ConstraintGraph<'arena>,
    solution: Option<&'solution GraphSolution>,
    lazy_solutions: HashMap<u32, Type>,
    resolving: HashSet<u32>,
}

impl<'graph, 'arena, 'solution> TypeResolver<'graph, 'arena, 'solution> {
    fn new(graph: &'graph ConstraintGraph<'arena>) -> Self {
        Self {
            graph,
            solution: None,
            lazy_solutions: HashMap::new(),
            resolving: HashSet::new(),
        }
    }

    fn with_solution(
        graph: &'graph ConstraintGraph<'arena>,
        solution: &'solution GraphSolution,
    ) -> Self {
        Self {
            graph,
            solution: Some(solution),
            lazy_solutions: HashMap::new(),
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
            Type::EffectRow(items) => self.resolve_effect_row(items),
            Type::Stack { inner, weight } => Ok(types::simplify_stack_type(
                self.resolve(inner)?,
                weight.clone(),
            )),
            Type::Union(left, right) => self.resolve_union(left, right),
            Type::Intersection(left, right) => self.resolve_intersection(left, right),
            Type::OpenVar(slot) => self.slot_solution(*slot),
        }
    }

    fn resolve_all(&mut self, tys: &[Type]) -> Result<Vec<Type>, SpecializeError> {
        tys.iter().map(|ty| self.resolve(ty)).collect()
    }

    fn resolve_effect_row(&mut self, items: &[Type]) -> Result<Type, SpecializeError> {
        Ok(types::simplify_type(Type::EffectRow(
            items
                .iter()
                .map(|item| self.resolve_effect_item(item))
                .collect::<Result<Vec<_>, _>>()?,
        )))
    }

    fn resolve_effect_item(&mut self, item: &Type) -> Result<Type, SpecializeError> {
        let Type::Con { path, args } = item else {
            return self.resolve(item);
        };
        Ok(Type::Con {
            path: path.clone(),
            args: args
                .iter()
                .map(|arg| match self.resolve(arg) {
                    Ok(arg) => Ok(arg),
                    Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(Type::unit()),
                    Err(error) => Err(error),
                })
                .collect::<Result<Vec<_>, _>>()?,
        })
    }

    fn resolve_erased_effectful_actual(
        &mut self,
        actual: &Type,
        expected: Option<&Type>,
    ) -> Option<Type> {
        if let (
            Type::OpenVar(_),
            Some(Type::Thunk {
                effect,
                value: expected_value,
            }),
        ) = (actual, expected)
            && actual == expected_value.as_ref()
            && type_contains_open_var(expected_value)
        {
            let effect = self.resolve(effect).ok()?;
            return Some(Type::Thunk {
                effect: Box::new(effect),
                value: Box::new(Type::unit()),
            });
        }
        let Type::Thunk {
            effect,
            value: actual_value,
        } = actual
        else {
            return None;
        };
        let expected_matches_value = match expected {
            Some(Type::Thunk {
                value: expected_value,
                ..
            }) => actual_value == expected_value,
            Some(expected) => expected == actual_value.as_ref(),
            None => false,
        };
        if !expected_matches_value || !type_contains_open_var(actual_value) {
            return None;
        }
        let effect = self.resolve(effect).ok()?;
        Some(Type::Thunk {
            effect: Box::new(effect),
            value: Box::new(Type::unit()),
        })
    }

    fn slot_solution(&mut self, slot: u32) -> Result<Type, SpecializeError> {
        if let Some(solution) = self.solution {
            return match solution.get(slot)?.cloned() {
                Some(solution) => Ok(solution),
                None => {
                    if slot != 106 {
                        return Err(SpecializeError::UndeterminedTypeSlot { slot });
                    }
                    if let Ok(slot_data) = self.graph.slot(slot) {
                        eprintln!(
                            "undetermined slot {slot} kind={:?} lower={:?} upper={:?} succ={:?} pred={:?}",
                            slot_data.kind,
                            slot_data.lower,
                            slot_data.upper,
                            slot_data.successors,
                            slot_data.predecessors
                        );
                    }
                    Err(SpecializeError::UndeterminedTypeSlot { slot })
                }
            };
        }
        if let Some(solution) = self.lazy_solutions.get(&slot) {
            return Ok(solution.clone());
        }
        let solution = self
            .try_slot_solution(slot)?
            .ok_or(SpecializeError::UndeterminedTypeSlot { slot })?;
        self.lazy_solutions.insert(slot, solution.clone());
        Ok(solution)
    }

    fn try_slot_solution(&mut self, slot: u32) -> Result<Option<Type>, SpecializeError> {
        let slot_data = self.graph.slot(slot)?;
        let slot_kind = slot_data.kind;
        let lower_bounds = slot_data.lower.clone();
        let upper_bounds = slot_data.upper.clone();
        if !self.resolving.insert(slot) {
            return Ok(None);
        }
        let solution = self.compute_slot_solution(slot, slot_kind, &lower_bounds, &upper_bounds)?;
        self.resolving.remove(&slot);
        Ok(solution)
    }

    fn compute_slot_solution(
        &mut self,
        slot: u32,
        slot_kind: TypeSlotKind,
        lower_bounds: &[Type],
        upper_bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let lower = self.join_candidates(slot, slot_kind, lower_bounds)?;
        let upper = self.meet_candidates(slot, slot_kind, upper_bounds)?;
        let solution = match (lower, upper) {
            (Some(lower), Some(upper)) if type_candidates_equivalent(&lower, &upper) => lower,
            (Some(lower), Some(upper)) if type_candidate_subtype(self.graph, &lower, &upper) => {
                lower
            }
            (Some(lower), Some(upper))
                if slot_kind == TypeSlotKind::Effect
                    && self.effect_lower_filtered_by_upper_bounds(
                        &lower,
                        upper_bounds,
                        &upper,
                    )? =>
            {
                upper
            }
            (Some(lower), Some(upper)) => {
                eprintln!(
                    "slot {slot} conflict lower_bounds={lower_bounds:?} upper_bounds={upper_bounds:?} lower={lower:?} upper={upper:?}"
                );
                for (index, slot) in self.graph.slots.iter().enumerate() {
                    if !slot.lower.is_empty() || !slot.upper.is_empty() {
                        eprintln!(
                            "slot {index} kind={:?} lower={:?} upper={:?} succ={:?} pred={:?}",
                            slot.kind, slot.lower, slot.upper, slot.successors, slot.predecessors
                        );
                    }
                }
                return Err(SpecializeError::ConflictingTypeCandidates {
                    slot,
                    existing: lower,
                    incoming: upper,
                });
            }
            (Some(lower), None) => lower,
            (None, Some(_)) if slot_kind == TypeSlotKind::Effect => Type::pure_effect(),
            (None, Some(upper)) => upper,
            (None, None) if slot_kind == TypeSlotKind::Effect => Type::pure_effect(),
            (None, None) => return Ok(None),
        };
        Ok(Some(solution))
    }

    fn join_candidates(
        &mut self,
        slot: u32,
        slot_kind: TypeSlotKind,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut candidate: Option<Type> = None;
        for bound in bounds {
            if is_self_stack_bound(slot, bound) {
                continue;
            }
            let Some(resolved) = self.resolve_candidate_bound(bound)? else {
                continue;
            };
            let resolved = effect_slot_candidate(slot_kind, resolved);
            candidate = Some(match candidate {
                Some(existing) if slot_kind == TypeSlotKind::Effect => {
                    join_effect_type_candidates(existing, resolved)
                }
                Some(existing) => {
                    match join_type_candidates(self.graph, slot, existing.clone(), resolved.clone())
                    {
                        Ok(joined) => joined,
                        Err(error) => {
                            eprintln!(
                                "join slot {slot} conflict bounds={bounds:?} existing={existing:?} incoming={resolved:?}"
                            );
                            for (index, slot) in self.graph.slots.iter().enumerate() {
                                if !slot.lower.is_empty() || !slot.upper.is_empty() {
                                    eprintln!(
                                        "slot {index} kind={:?} lower={:?} upper={:?} succ={:?} pred={:?}",
                                        slot.kind,
                                        slot.lower,
                                        slot.upper,
                                        slot.successors,
                                        slot.predecessors
                                    );
                                }
                            }
                            return Err(error);
                        }
                    }
                }
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
            if is_self_stack_bound(slot, bound) {
                continue;
            }
            let Some(resolved) = self.resolve_candidate_bound(bound)? else {
                continue;
            };
            let resolved = effect_slot_candidate(slot_kind, resolved);
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

    fn resolve_candidate_bound(&mut self, bound: &Type) -> Result<Option<Type>, SpecializeError> {
        match self.resolve(bound) {
            Ok(ty) => Ok(Some(ty)),
            Err(SpecializeError::UndeterminedTypeSlot { .. }) => Ok(None),
            Err(error) => Err(error),
        }
    }

    fn effect_lower_filtered_by_upper_bounds(
        &mut self,
        lower: &Type,
        upper_bounds: &[Type],
        upper: &Type,
    ) -> Result<bool, SpecializeError> {
        for bound in upper_bounds {
            if self.effect_lower_filtered_by_upper_bound(lower, bound, upper)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn effect_lower_filtered_by_upper_bound(
        &mut self,
        lower: &Type,
        bound: &Type,
        upper: &Type,
    ) -> Result<bool, SpecializeError> {
        match bound {
            Type::Stack { weight, .. } => {
                let filtered = types::simplify_stack_type(lower.clone(), weight.clone());
                Ok(type_candidates_equivalent(&filtered, upper))
            }
            Type::EffectRow(items) => {
                for item in items {
                    if self.effect_lower_filtered_by_upper_bound(lower, item, upper)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Type::Union(left, right) | Type::Intersection(left, right) => Ok(self
                .effect_lower_filtered_by_upper_bound(lower, left, upper)?
                || self.effect_lower_filtered_by_upper_bound(lower, right, upper)?),
            Type::OpenVar(slot) => {
                let Some(solution) = self.try_slot_solution(*slot)? else {
                    return Ok(false);
                };
                self.effect_lower_filtered_by_upper_bound(lower, &solution, upper)
            }
            _ => Ok(false),
        }
    }

    fn resolve_union(&mut self, left: &Type, right: &Type) -> Result<Type, SpecializeError> {
        match (self.resolve_branch(left)?, self.resolve_branch(right)?) {
            (ResolvedBranch::Type(left), ResolvedBranch::Type(right)) => {
                Ok(simplify_resolved_union(self.graph, left, right))
            }
            (ResolvedBranch::Type(ty), ResolvedBranch::Undetermined(_))
            | (ResolvedBranch::Undetermined(_), ResolvedBranch::Type(ty)) => Ok(ty),
            (ResolvedBranch::Undetermined(slot), ResolvedBranch::Undetermined(_)) => {
                Err(SpecializeError::UndeterminedTypeSlot { slot })
            }
        }
    }

    fn resolve_intersection(&mut self, left: &Type, right: &Type) -> Result<Type, SpecializeError> {
        match (self.resolve_branch(left)?, self.resolve_branch(right)?) {
            (ResolvedBranch::Type(left), ResolvedBranch::Type(right)) => {
                Ok(simplify_resolved_intersection(self.graph, left, right))
            }
            (ResolvedBranch::Type(ty), ResolvedBranch::Undetermined(_))
            | (ResolvedBranch::Undetermined(_), ResolvedBranch::Type(ty)) => Ok(ty),
            (ResolvedBranch::Undetermined(slot), ResolvedBranch::Undetermined(_)) => {
                Err(SpecializeError::UndeterminedTypeSlot { slot })
            }
        }
    }

    fn resolve_branch(&mut self, ty: &Type) -> Result<ResolvedBranch, SpecializeError> {
        match self.resolve(ty) {
            Ok(ty) => Ok(ResolvedBranch::Type(ty)),
            Err(SpecializeError::UndeterminedTypeSlot { slot }) => {
                Ok(ResolvedBranch::Undetermined(slot))
            }
            Err(error) => Err(error),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ResolvedBranch {
    Type(Type),
    Undetermined(u32),
}

fn simplify_resolved_union(graph: &ConstraintGraph<'_>, left: Type, right: Type) -> Type {
    if type_candidates_equivalent(&left, &right) || type_candidate_subtype(graph, &right, &left) {
        return left;
    }
    if type_candidate_subtype(graph, &left, &right) {
        return right;
    }
    types::simplify_type(Type::Union(Box::new(left), Box::new(right)))
}

fn simplify_resolved_intersection(graph: &ConstraintGraph<'_>, left: Type, right: Type) -> Type {
    if type_candidates_equivalent(&left, &right) || type_candidate_subtype(graph, &left, &right) {
        return left;
    }
    if type_candidate_subtype(graph, &right, &left) {
        return right;
    }
    types::simplify_type(Type::Intersection(Box::new(left), Box::new(right)))
}

fn effect_slot_candidate(slot_kind: TypeSlotKind, ty: Type) -> Type {
    if slot_kind != TypeSlotKind::Effect || matches!(ty, Type::EffectRow(_)) {
        return ty;
    }
    Type::EffectRow(vec![ty])
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
            types::simplify_type(Type::EffectRow(left))
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
    match (&left, &right) {
        (Type::Record(_), Type::Record(_)) => {
            return join_record_type_candidates(graph, slot, left, right);
        }
        (Type::PolyVariant(_), Type::PolyVariant(_)) => {
            return join_poly_variant_type_candidates(graph, slot, left, right);
        }
        _ => {}
    }
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
    match (&left, &right) {
        (Type::Record(_), Type::Record(_)) => {
            return meet_record_type_candidates(graph, slot, left, right);
        }
        (Type::PolyVariant(_), Type::PolyVariant(_)) => {
            return meet_poly_variant_type_candidates(graph, slot, left, right);
        }
        _ => {}
    }
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

fn join_record_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::Record(left_fields), Type::Record(right_fields)) = (left, right) else {
        unreachable!("record candidates checked by caller");
    };
    merge_record_type_candidates(graph, slot, left_fields, right_fields, RecordMerge::Join)
        .map(Type::Record)
}

fn meet_record_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::Record(left_fields), Type::Record(right_fields)) = (left, right) else {
        unreachable!("record candidates checked by caller");
    };
    merge_record_type_candidates(graph, slot, left_fields, right_fields, RecordMerge::Meet)
        .map(Type::Record)
}

fn merge_record_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left_fields: Vec<TypeField>,
    right_fields: Vec<TypeField>,
    merge: RecordMerge,
) -> Result<Vec<TypeField>, SpecializeError> {
    let mut out = Vec::new();
    for left in &left_fields {
        match record_field_type(&right_fields, &left.name) {
            Some(right) => {
                let value = match merge {
                    RecordMerge::Join => {
                        join_type_candidates(graph, slot, left.value.clone(), right.value.clone())?
                    }
                    RecordMerge::Meet => {
                        meet_type_candidates(graph, slot, left.value.clone(), right.value.clone())?
                    }
                };
                out.push(TypeField {
                    name: left.name.clone(),
                    value,
                    optional: match merge {
                        RecordMerge::Join => left.optional || right.optional,
                        RecordMerge::Meet => left.optional && right.optional,
                    },
                });
            }
            None => out.push(TypeField {
                name: left.name.clone(),
                value: left.value.clone(),
                optional: match merge {
                    RecordMerge::Join => true,
                    RecordMerge::Meet => left.optional,
                },
            }),
        }
    }
    for right in right_fields {
        if left_fields.iter().any(|left| left.name == right.name) {
            continue;
        }
        out.push(TypeField {
            name: right.name,
            value: right.value,
            optional: match merge {
                RecordMerge::Join => true,
                RecordMerge::Meet => right.optional,
            },
        });
    }
    Ok(out)
}

fn join_poly_variant_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::PolyVariant(left_variants), Type::PolyVariant(right_variants)) = (left, right)
    else {
        unreachable!("poly variant candidates checked by caller");
    };
    let variants = merge_poly_variant_type_candidates(
        graph,
        slot,
        left_variants,
        right_variants,
        VariantMerge::Join,
    )?;
    Ok(Type::PolyVariant(variants))
}

fn meet_poly_variant_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left: Type,
    right: Type,
) -> Result<Type, SpecializeError> {
    let (Type::PolyVariant(left_variants), Type::PolyVariant(right_variants)) = (left, right)
    else {
        unreachable!("poly variant candidates checked by caller");
    };
    let variants = merge_poly_variant_type_candidates(
        graph,
        slot,
        left_variants,
        right_variants,
        VariantMerge::Meet,
    )?;
    if variants.is_empty() {
        return Ok(Type::Never);
    }
    Ok(Type::PolyVariant(variants))
}

fn merge_poly_variant_type_candidates(
    graph: &ConstraintGraph<'_>,
    slot: u32,
    left_variants: Vec<TypeVariant>,
    right_variants: Vec<TypeVariant>,
    merge: VariantMerge,
) -> Result<Vec<TypeVariant>, SpecializeError> {
    let mut out = Vec::new();
    for left in &left_variants {
        match matching_variant(&right_variants, left) {
            Some(right) => {
                let payloads = left
                    .payloads
                    .iter()
                    .cloned()
                    .zip(right.payloads.iter().cloned())
                    .map(|(left, right)| match merge {
                        VariantMerge::Join => join_type_candidates(graph, slot, left, right),
                        VariantMerge::Meet => meet_type_candidates(graph, slot, left, right),
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                out.push(TypeVariant {
                    name: left.name.clone(),
                    payloads,
                });
            }
            None if merge == VariantMerge::Join => out.push(left.clone()),
            None => {}
        }
    }
    if merge == VariantMerge::Join {
        for right in right_variants {
            if left_variants
                .iter()
                .any(|left| variants_match(left, &right))
            {
                continue;
            }
            out.push(right);
        }
    }
    Ok(out)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RecordMerge {
    Join,
    Meet,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VariantMerge {
    Join,
    Meet,
}

fn type_candidates_equivalent(left: &Type, right: &Type) -> bool {
    if left == right || left.is_pure_effect() && right.is_pure_effect() {
        return true;
    }
    let (Type::EffectRow(left_items), Type::EffectRow(right_items)) = (left, right) else {
        return false;
    };
    effect_row_candidates_equivalent(left_items, right_items)
}

fn type_contains_open_var(ty: &Type) -> bool {
    match ty {
        Type::OpenVar(_) => true,
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_contains_open_var(arg)
                || type_contains_open_var(arg_effect)
                || type_contains_open_var(ret_effect)
                || type_contains_open_var(ret)
        }
        Type::Thunk { effect, value } => {
            type_contains_open_var(effect) || type_contains_open_var(value)
        }
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(type_contains_open_var)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_contains_open_var(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_contains_open_var)),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_contains_open_var(left) || type_contains_open_var(right)
        }
        Type::Stack { inner, .. } => type_contains_open_var(inner),
        Type::Any | Type::Never => false,
    }
}

fn type_mentions_ref_update_unit(ty: &Type) -> bool {
    match ty {
        Type::Con { path, args } => {
            path.as_slice()
                == ["std", "control", "var", "ref_update", "update"]
                    .map(str::to_string)
                    .as_slice()
                || (path.as_slice()
                    == ["std", "control", "var", "ref_update"]
                        .map(str::to_string)
                        .as_slice()
                    && args.as_slice() == [Type::unit()])
                || args.iter().any(type_mentions_ref_update_unit)
        }
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_mentions_ref_update_unit(arg)
                || type_mentions_ref_update_unit(arg_effect)
                || type_mentions_ref_update_unit(ret_effect)
                || type_mentions_ref_update_unit(ret)
        }
        Type::Thunk { effect, value } => {
            type_mentions_ref_update_unit(effect) || type_mentions_ref_update_unit(value)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_mentions_ref_update_unit(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .any(|variant| variant.payloads.iter().any(type_mentions_ref_update_unit)),
        Type::Tuple(items) | Type::EffectRow(items) => {
            items.iter().any(type_mentions_ref_update_unit)
        }
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_mentions_ref_update_unit(left) || type_mentions_ref_update_unit(right)
        }
        Type::Stack { inner, .. } => type_mentions_ref_update_unit(inner),
        Type::OpenVar(_) | Type::Any | Type::Never => false,
    }
}

fn expr_kind_label(expr: &poly_expr::Expr) -> &'static str {
    match expr {
        poly_expr::Expr::Lit(_) => "lit",
        poly_expr::Expr::PrimitiveOp(_) => "primitive",
        poly_expr::Expr::Var(_) => "var",
        poly_expr::Expr::App(_, _) => "app",
        poly_expr::Expr::RefSet(_, _) => "ref-set",
        poly_expr::Expr::Lambda(_, _) => "lambda",
        poly_expr::Expr::Tuple(_) => "tuple",
        poly_expr::Expr::Record { .. } => "record",
        poly_expr::Expr::PolyVariant(_, _) => "poly-variant",
        poly_expr::Expr::Select(_, _) => "select",
        poly_expr::Expr::Case(_, _) => "case",
        poly_expr::Expr::Catch(_, _) => "catch",
        poly_expr::Expr::Block(_, _) => "block",
    }
}

fn debug_expr_tree(arena: &poly_expr::Arena, expr: poly_expr::ExprId, depth: usize) -> String {
    if depth == 0 {
        return format!("{expr:?}:...");
    }
    match arena.expr(expr) {
        poly_expr::Expr::Lit(_) => format!("{expr:?}:lit"),
        poly_expr::Expr::PrimitiveOp(op) => format!("{expr:?}:primitive({op:?})"),
        poly_expr::Expr::Var(ref_id) => {
            let target = arena.ref_target(*ref_id);
            let operation = target.and_then(|def| arena.effect_operations.get(&def));
            format!(
                "{expr:?}:var(ref={ref_id:?}, target={target:?}, op={:?})",
                operation.map(|operation| &operation.path)
            )
        }
        poly_expr::Expr::App(callee, arg) => format!(
            "{expr:?}:app({}, {})",
            debug_expr_tree(arena, *callee, depth - 1),
            debug_expr_tree(arena, *arg, depth - 1)
        ),
        poly_expr::Expr::RefSet(reference, value) => format!(
            "{expr:?}:ref-set({}, {})",
            debug_expr_tree(arena, *reference, depth - 1),
            debug_expr_tree(arena, *value, depth - 1)
        ),
        poly_expr::Expr::Lambda(param, body) => {
            format!(
                "{expr:?}:lambda({param:?} -> {})",
                debug_expr_tree(arena, *body, depth - 1)
            )
        }
        poly_expr::Expr::Tuple(items) => format!(
            "{expr:?}:tuple({})",
            items
                .iter()
                .map(|item| debug_expr_tree(arena, *item, depth - 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        poly_expr::Expr::Record { fields, spread } => format!(
            "{expr:?}:record({}; spread={})",
            fields
                .iter()
                .map(|(name, value)| format!(
                    "{name}:{}",
                    debug_expr_tree(arena, *value, depth - 1)
                ))
                .collect::<Vec<_>>()
                .join(", "),
            debug_record_spread(arena, spread, depth - 1)
        ),
        poly_expr::Expr::PolyVariant(tag, payloads) => format!(
            "{expr:?}:variant({tag}, {})",
            payloads
                .iter()
                .map(|payload| debug_expr_tree(arena, *payload, depth - 1))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        poly_expr::Expr::Select(base, select) => {
            let select = arena.select(*select);
            format!(
                "{expr:?}:select({}, name={}, resolution={:?})",
                debug_expr_tree(arena, *base, depth - 1),
                select.name,
                select.resolution
            )
        }
        poly_expr::Expr::Case(scrutinee, arms) => format!(
            "{expr:?}:case({}, arms={})",
            debug_expr_tree(arena, *scrutinee, depth - 1),
            arms.len()
        ),
        poly_expr::Expr::Catch(body, arms) => format!(
            "{expr:?}:catch({}, arms={})",
            debug_expr_tree(arena, *body, depth - 1),
            arms.len()
        ),
        poly_expr::Expr::Block(stmts, tail) => format!(
            "{expr:?}:block(stmts={}, tail={})",
            stmts.len(),
            tail.map(|tail| debug_expr_tree(arena, tail, depth - 1))
                .unwrap_or_else(|| "none".to_string())
        ),
    }
}

fn debug_record_spread(
    arena: &poly_expr::Arena,
    spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
    depth: usize,
) -> String {
    match spread {
        poly_expr::RecordSpread::None => "none".to_string(),
        poly_expr::RecordSpread::Head(expr) => {
            format!("head({})", debug_expr_tree(arena, *expr, depth))
        }
        poly_expr::RecordSpread::Tail(expr) => {
            format!("tail({})", debug_expr_tree(arena, *expr, depth))
        }
    }
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
            effect_row_candidate_subtype(graph, lower_items, upper_items)
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

fn effect_row_candidates_equivalent(left_items: &[Type], right_items: &[Type]) -> bool {
    if left_items.len() != right_items.len() {
        return false;
    }
    let mut matched_right = vec![false; right_items.len()];
    for left in left_items {
        let Some(right_index) = right_items.iter().enumerate().find_map(|(index, right)| {
            (!matched_right[index]
                && same_effect_row_family(left, right)
                && type_candidates_equivalent(left, right))
            .then_some(index)
        }) else {
            return false;
        };
        matched_right[right_index] = true;
    }
    true
}

fn effect_row_candidate_subtype(
    graph: &ConstraintGraph<'_>,
    lower_items: &[Type],
    upper_items: &[Type],
) -> bool {
    if lower_items.is_empty() {
        return true;
    }
    if lower_items.len() != upper_items.len() {
        return false;
    }
    let mut matched_upper = vec![false; upper_items.len()];
    for lower in lower_items {
        let Some(upper_index) = upper_items.iter().enumerate().find_map(|(index, upper)| {
            (!matched_upper[index]
                && same_effect_row_family(lower, upper)
                && type_candidate_subtype(graph, lower, upper))
            .then_some(index)
        }) else {
            return false;
        };
        matched_upper[upper_index] = true;
    }
    true
}

fn resolve_role_arg_exact_type(
    graph: &ConstraintGraph<'_>,
    resolver: &mut TypeResolver<'_, '_, '_>,
    arg: &types::InstantiatedRoleArg,
) -> Result<Option<Type>, SpecializeError> {
    let lower = resolve_role_arg_bound(resolver, &arg.lower, RoleArgBound::Lower)?;
    let upper = resolve_role_arg_bound(resolver, &arg.upper, RoleArgBound::Upper)?;
    Ok(choose_resolved_role_arg_exact_type(graph, lower, upper))
}

fn resolve_role_arg_bound(
    resolver: &mut TypeResolver<'_, '_, '_>,
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

fn matching_variant<'a>(
    variants: &'a [TypeVariant],
    target: &TypeVariant,
) -> Option<&'a TypeVariant> {
    variants
        .iter()
        .find(|variant| variants_match(variant, target))
}

fn variants_match(left: &TypeVariant, right: &TypeVariant) -> bool {
    left.name == right.name && left.payloads.len() == right.payloads.len()
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

fn runtime_value_is_never(ty: &Type) -> bool {
    matches!(runtime_value_shape(ty), Type::Never)
}

fn value_argument_narrows_polyvariant(declared: &Type, actual: &Type) -> bool {
    let Type::PolyVariant(declared_variants) = runtime_value_shape(declared) else {
        return false;
    };
    let Type::PolyVariant(actual_variants) = runtime_value_shape(actual) else {
        return false;
    };
    actual_variants.len() < declared_variants.len()
        && actual_variants.iter().all(|actual| {
            declared_variants.iter().any(|declared| {
                declared.name == actual.name && declared.payloads.len() == actual.payloads.len()
            })
        })
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

fn catch_residual_effect(scrutinee_effect: Type, handled_effects: &[Type]) -> Type {
    if handled_effects.is_empty() || scrutinee_effect.is_pure_effect() {
        return scrutinee_effect;
    }
    let handled_items = handled_effects
        .iter()
        .flat_map(effect_row_items)
        .cloned()
        .collect::<Vec<_>>();
    residual_effect_after_handling(scrutinee_effect, &handled_items)
}

fn effect_row_items(effect: &Type) -> &[Type] {
    match effect {
        Type::EffectRow(items) => items,
        _ => std::slice::from_ref(effect),
    }
}

fn residual_effect_after_handling(effect: Type, handled_items: &[Type]) -> Type {
    if effect.is_pure_effect() {
        return Type::pure_effect();
    }
    match effect {
        Type::EffectRow(items) => residual_effect_row_after_handling(items, handled_items),
        Type::Con { .. } if effect_item_is_handled(&effect, handled_items) => Type::pure_effect(),
        Type::Con { .. } => Type::EffectRow(vec![effect]),
        Type::Union(left, right) => types::simplify_type(Type::Union(
            Box::new(residual_effect_after_handling(*left, handled_items)),
            Box::new(residual_effect_after_handling(*right, handled_items)),
        )),
        Type::Intersection(left, right) => {
            residual_intersection_after_handling(*left, *right, handled_items)
        }
        Type::Stack { .. } | Type::OpenVar(_) => symbolic_residual_effect(effect, handled_items),
        Type::Any | Type::Never => effect,
        Type::Fun { .. }
        | Type::Thunk { .. }
        | Type::Record(_)
        | Type::PolyVariant(_)
        | Type::Tuple(_) => symbolic_residual_effect(effect, handled_items),
    }
}

fn residual_intersection_after_handling(left: Type, right: Type, handled_items: &[Type]) -> Type {
    if let Some(residual) = residual_row_tail_from_intersection(&left, &right, handled_items) {
        return residual;
    }
    if let Some(residual) = residual_row_tail_from_intersection(&right, &left, handled_items) {
        return residual;
    }
    symbolic_residual_effect(
        Type::Intersection(Box::new(left), Box::new(right)),
        handled_items,
    )
}

fn residual_row_tail_from_intersection(
    row_side: &Type,
    other_side: &Type,
    handled_items: &[Type],
) -> Option<Type> {
    let Type::EffectRow(items) = row_side else {
        return None;
    };
    let tail = items.last()?;
    if !effect_row_mentions_handled(items, handled_items) || !type_contains_type(other_side, tail) {
        return None;
    }
    Some(symbolic_residual_effect(tail.clone(), handled_items))
}

fn residual_effect_row_after_handling(items: Vec<Type>, handled_items: &[Type]) -> Type {
    let mut residual = Vec::new();
    for item in items {
        if effect_item_is_handled(&item, handled_items) {
            continue;
        }
        if effect_item_needs_symbolic_residual(&item) {
            residual.push(symbolic_residual_effect(item, handled_items));
        } else {
            residual.push(item);
        }
    }
    types::simplify_type(Type::EffectRow(residual))
}

fn effect_row_mentions_handled(items: &[Type], handled_items: &[Type]) -> bool {
    items
        .iter()
        .any(|item| effect_item_is_handled(item, handled_items))
}

fn effect_item_is_handled(item: &Type, handled_items: &[Type]) -> bool {
    handled_items
        .iter()
        .any(|handled| same_effect_row_family(item, handled))
}

fn effect_item_needs_symbolic_residual(item: &Type) -> bool {
    matches!(
        item,
        Type::OpenVar(_)
            | Type::Stack { .. }
            | Type::Union(_, _)
            | Type::Intersection(_, _)
            | Type::Any
    )
}

fn symbolic_residual_effect(effect: Type, handled_items: &[Type]) -> Type {
    let Some(weight) = residual_stack_weight(handled_items) else {
        return effect;
    };
    types::simplify_type(Type::Stack {
        inner: Box::new(effect),
        weight,
    })
}

fn residual_stack_weight(handled_items: &[Type]) -> Option<StackWeight> {
    let families = handled_items
        .iter()
        .filter_map(effect_family_from_item)
        .collect::<Vec<_>>();
    (!families.is_empty()).then_some(StackWeight {
        entries: vec![StackWeightEntry {
            id: 0,
            pops: 0,
            floor: vec![EffectFamilies::AllExcept(families)],
            stack: Vec::new(),
        }],
    })
}

fn effect_family_from_item(item: &Type) -> Option<EffectFamily> {
    let Type::Con { path, args } = item else {
        return None;
    };
    Some(EffectFamily {
        path: path.clone(),
        args: args.clone(),
    })
}

fn type_contains_type(ty: &Type, needle: &Type) -> bool {
    if ty == needle {
        return true;
    }
    match ty {
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            type_contains_type(arg, needle)
                || type_contains_type(arg_effect, needle)
                || type_contains_type(ret_effect, needle)
                || type_contains_type(ret, needle)
        }
        Type::Thunk { effect, value } => {
            type_contains_type(effect, needle) || type_contains_type(value, needle)
        }
        Type::Con { args, .. } | Type::Tuple(args) | Type::EffectRow(args) => {
            args.iter().any(|arg| type_contains_type(arg, needle))
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| type_contains_type(&field.value, needle)),
        Type::PolyVariant(variants) => variants.iter().any(|variant| {
            variant
                .payloads
                .iter()
                .any(|payload| type_contains_type(payload, needle))
        }),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            type_contains_type(left, needle) || type_contains_type(right, needle)
        }
        Type::Stack { inner, .. } => type_contains_type(inner, needle),
        Type::Any | Type::Never | Type::OpenVar(_) => false,
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

fn is_self_stack_bound(slot: u32, ty: &Type) -> bool {
    let Type::Stack { inner, .. } = ty else {
        return false;
    };
    matches!(inner.as_ref(), Type::OpenVar(candidate) if *candidate == slot)
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
    fn tuple_expression_constrains_open_expected_slot() {
        let lowering = lower_source("my id x = x\nid((1, 2))\n");
        let arena = &lowering.session.poly;
        let root = arena.root_exprs[0];

        let plan = solve_expr(arena, root, None).expect("tuple argument should solve");

        assert_eq!(
            mono::dump::dump_type(plan.actual_type_of(root).unwrap()),
            "(int, int)"
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
        graph
            .solve_constraints()
            .expect("worklist should saturate effect row residual");

        let mut resolver = TypeResolver::new(&graph);
        assert_eq!(
            mono::dump::dump_type(&resolver.resolve(&tail).unwrap()),
            "[nondet]"
        );
    }

    #[test]
    fn constraint_worklist_saturates_structural_constraints_before_resolution() {
        let arena = poly::expr::Arena::new();
        let mut graph = ConstraintGraph::new(&arena);
        let slot = graph.fresh_slot(TypeSlotKind::Value);

        graph
            .constrain_subtype(
                Type::Tuple(vec![int_type()]),
                Type::Tuple(vec![slot.clone()]),
            )
            .expect("tuple constraint should enqueue");
        graph
            .solve_constraints()
            .expect("worklist should saturate tuple children");

        let mut resolver = TypeResolver::new(&graph);
        assert_eq!(
            mono::dump::dump_type(&resolver.resolve(&slot).unwrap()),
            "int"
        );
    }

    #[test]
    fn recursive_slot_resolution_does_not_default_to_unit() {
        let arena = poly::expr::Arena::new();
        let mut graph = ConstraintGraph::new(&arena);
        let slot = graph.fresh_slot(TypeSlotKind::Value);

        graph
            .constrain_subtype(slot.clone(), Type::Tuple(vec![slot.clone()]))
            .expect("recursive constraint should enqueue");
        graph
            .solve_constraints()
            .expect("worklist should store recursive upper bound");

        let mut resolver = TypeResolver::new(&graph);
        assert!(matches!(
            resolver.resolve(&slot),
            Err(crate::SpecializeError::UndeterminedTypeSlot { .. })
        ));
    }

    #[test]
    fn concrete_branch_resolution_prunes_unresolved_union_residue() {
        let arena = poly::expr::Arena::new();
        let mut graph = ConstraintGraph::new(&arena);
        let residue = graph.fresh_slot(TypeSlotKind::Value);
        let mut resolver = TypeResolver::new(&graph);

        let ty = resolver
            .resolve(&Type::Union(Box::new(residue), Box::new(int_type())))
            .expect("concrete union branch should resolve");

        assert_eq!(mono::dump::dump_type(&ty), "int");
    }

    #[test]
    fn concrete_branch_resolution_prunes_unresolved_intersection_residue() {
        let arena = poly::expr::Arena::new();
        let mut graph = ConstraintGraph::new(&arena);
        let residue = graph.fresh_slot(TypeSlotKind::Value);
        let mut resolver = TypeResolver::new(&graph);

        let ty = resolver
            .resolve(&Type::Intersection(Box::new(residue), Box::new(int_type())))
            .expect("concrete intersection branch should resolve");

        assert_eq!(mono::dump::dump_type(&ty), "int");
    }

    #[test]
    fn concrete_branch_resolution_absorbs_intersection_with_union_member() {
        let arena = poly::expr::Arena::new();
        let graph = ConstraintGraph::new(&arena);
        let local = Type::Con {
            path: vec!["local".into()],
            args: vec![int_type()],
        };
        let std_var = Type::Con {
            path: vec!["std".into(), "control".into(), "var".into(), "var".into()],
            args: vec![int_type()],
        };
        let union = Type::Union(Box::new(local.clone()), Box::new(std_var));
        let mut resolver = TypeResolver::new(&graph);

        let ty = resolver
            .resolve(&Type::EffectRow(vec![Type::Intersection(
                Box::new(union),
                Box::new(local.clone()),
            )]))
            .expect("intersection with a union member should resolve");

        assert_eq!(ty, Type::EffectRow(vec![local]));
    }

    #[test]
    fn concrete_candidate_selection_ignores_recursive_non_concrete_bound() {
        let arena = poly::expr::Arena::new();
        let mut graph = ConstraintGraph::new(&arena);
        let slot = graph.fresh_slot(TypeSlotKind::Value);
        let weight = mono::StackWeight {
            entries: vec![mono::StackWeightEntry {
                id: 0,
                pops: 1,
                floor: Vec::new(),
                stack: Vec::new(),
            }],
        };

        graph
            .constrain_subtype(int_type(), slot.clone())
            .expect("lower concrete bound should enqueue");
        graph
            .constrain_subtype(
                slot.clone(),
                Type::Union(
                    Box::new(Type::Stack {
                        inner: Box::new(slot.clone()),
                        weight,
                    }),
                    Box::new(int_type()),
                ),
            )
            .expect("recursive upper bound should enqueue");
        graph
            .solve_constraints()
            .expect("worklist should store candidate bounds");

        let mut resolver = TypeResolver::new(&graph);
        assert_eq!(
            mono::dump::dump_type(&resolver.resolve(&slot).unwrap()),
            "int"
        );
    }

    #[test]
    fn effect_row_candidate_comparison_ignores_item_order() {
        let arena = poly::expr::Arena::new();
        let mut graph = ConstraintGraph::new(&arena);
        let slot = graph.fresh_slot(TypeSlotKind::Effect);
        let sub_int = Type::Con {
            path: vec!["sub".to_string()],
            args: vec![int_type()],
        };

        graph
            .constrain_subtype(
                Type::EffectRow(vec![effect_item("nondet"), sub_int.clone()]),
                slot.clone(),
            )
            .expect("lower effect row should constrain");
        graph
            .constrain_subtype(
                slot.clone(),
                Type::EffectRow(vec![sub_int, effect_item("nondet")]),
            )
            .expect("upper effect row should constrain");
        graph
            .solve_constraints()
            .expect("worklist should saturate effect row bounds");

        let mut resolver = TypeResolver::new(&graph);
        assert_eq!(
            mono::dump::dump_type(&resolver.resolve(&slot).unwrap()),
            "[nondet, sub(int)]"
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
            "unit -> unit"
        );
        assert_eq!(plan.actual_type_of(*resume_value), Some(&unit_type()));
        assert_eq!(
            mono::dump::dump_type(plan.boundary(arms[0].body).unwrap().actual),
            "unit"
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
            "int -> int"
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
