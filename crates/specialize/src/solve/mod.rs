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

mod candidate;
mod constraint_graph;
mod effect;
mod expr_solver;
mod primitive;
#[cfg(test)]
mod tests;
mod type_resolver;

use candidate::*;
use constraint_graph::{GraphSolution, SubtypeConstraint, TypeSlot};
use effect::*;
use primitive::*;

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

    fn refine_actual(&mut self, expr: poly_expr::ExprId, ty: Type) -> Result<(), SpecializeError> {
        self.types.entry(expr).or_default().actual = Some(ty);
        Ok(())
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

fn merge_open_candidate_shape(left: &Type, right: &Type) -> Option<Type> {
    if left == right {
        return Some(left.clone());
    }
    match (left, right) {
        (Type::OpenVar(_), right) => Some(right.clone()),
        (left, Type::OpenVar(_)) => Some(left.clone()),
        (
            Type::Con {
                path: left_path,
                args: left_args,
            },
            Type::Con {
                path: right_path,
                args: right_args,
            },
        ) if left_path == right_path && left_args.len() == right_args.len() => {
            let args = left_args
                .iter()
                .zip(right_args)
                .map(|(left, right)| merge_open_candidate_shape(left, right))
                .collect::<Option<Vec<_>>>()?;
            Some(Type::Con {
                path: left_path.clone(),
                args,
            })
        }
        (Type::Tuple(left_items), Type::Tuple(right_items))
            if left_items.len() == right_items.len() =>
        {
            Some(Type::Tuple(
                left_items
                    .iter()
                    .zip(right_items)
                    .map(|(left, right)| merge_open_candidate_shape(left, right))
                    .collect::<Option<Vec<_>>>()?,
            ))
        }
        (
            Type::Thunk {
                effect: left_effect,
                value: left_value,
            },
            Type::Thunk {
                effect: right_effect,
                value: right_value,
            },
        ) => Some(Type::Thunk {
            effect: Box::new(merge_open_candidate_shape(left_effect, right_effect)?),
            value: Box::new(merge_open_candidate_shape(left_value, right_value)?),
        }),
        _ => None,
    }
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

struct TypeResolver<'graph, 'arena, 'solution> {
    graph: &'graph ConstraintGraph<'arena>,
    solution: Option<&'solution GraphSolution>,
    lazy_solutions: HashMap<u32, Type>,
    resolving: HashSet<u32>,
}

enum ResolvedBranch {
    Type(Type),
    Undetermined(u32),
}
