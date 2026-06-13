//! `mono` instance 内で erased expression に型を割り当てる作業状態。
//!
//! `poly` は式 node ごとの型を保持しない。ここでは instance/root ごとに主型と erased IR から
//! use-site の concrete 型を再構成し、mono IR へ写す段階が参照する plan だけを残す。

use std::collections::{HashMap, HashSet};

use mono::Type;
use poly::expr as poly_expr;

use crate::{ExprTypeRole, SpecializeError, convert_def, def_kind, lit_type, types};

#[derive(Debug, Clone, Default)]
pub(crate) struct ExprTypePlan {
    types: HashMap<poly_expr::ExprId, ExprTypes>,
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

    fn actual(&self, expr: poly_expr::ExprId) -> Option<&Type> {
        self.types
            .get(&expr)
            .and_then(|types| types.actual.as_ref())
    }

    fn finalize(&self, graph: &ConstraintGraph<'_>) -> Result<Self, SpecializeError> {
        let mut resolver = TypeResolver::new(graph);
        let mut out = Self::default();
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
                self.graph.constrain_subtype(actual.clone(), expected)?;
                return Ok(actual);
            }
            let actual = self.infer_expr(expr, Some(expected.clone()))?;
            self.graph.constrain_subtype(actual.clone(), expected)?;
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
            PolyExpr::PrimitiveOp(_) => Ok(expected.unwrap_or_else(|| self.fresh_value_slot())),
            PolyExpr::Var(ref_id) => self.var_type(*ref_id),
            PolyExpr::App(callee, arg) => self.apply_type(*callee, *arg, expected),
            PolyExpr::RefSet(reference, value) => {
                self.expr(*reference, None)?;
                self.expr(*value, None)?;
                Ok(Type::unit())
            }
            PolyExpr::Lambda(param, body) => self.lambda_type(*param, *body, expected),
            PolyExpr::Tuple(items) => self.tuple_type(items, expected.as_ref()),
            PolyExpr::Record { fields, spread } => {
                for (_, value) in fields {
                    self.expr(*value, None)?;
                }
                self.record_spread(spread)?;
                Ok(expected.unwrap_or_else(|| self.fresh_value_slot()))
            }
            PolyExpr::PolyVariant(_, payloads) => {
                for payload in payloads {
                    self.expr(*payload, None)?;
                }
                Ok(expected.unwrap_or_else(|| self.fresh_value_slot()))
            }
            PolyExpr::Select(base, _) => {
                self.expr(*base, None)?;
                Ok(expected.unwrap_or_else(|| self.fresh_value_slot()))
            }
            PolyExpr::Case(scrutinee, arms) => {
                self.expr(*scrutinee, None)?;
                let result = expected.unwrap_or_else(|| self.fresh_value_slot());
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.expr(guard, Some(bool_type()))?;
                    }
                    self.expr(arm.body, Some(result.clone()))?;
                }
                Ok(result)
            }
            PolyExpr::Catch(body, arms) => {
                let result = expected.unwrap_or_else(|| self.fresh_value_slot());
                self.expr(*body, Some(result.clone()))?;
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.expr(guard, Some(bool_type()))?;
                    }
                    self.expr(arm.body, Some(result.clone()))?;
                }
                Ok(result)
            }
            PolyExpr::Block(stmts, tail) => self.block_type(stmts, *tail, expected),
        }
    }

    fn apply_type(
        &mut self,
        callee: poly_expr::ExprId,
        arg: poly_expr::ExprId,
        expected: Option<Type>,
    ) -> Result<Type, SpecializeError> {
        let arg_ty = self.expr(arg, None)?;
        let ret_ty = expected.unwrap_or_else(|| self.fresh_value_slot());
        let callee_expected = types::pure_function_type(arg_ty.clone(), ret_ty.clone());
        let callee_ty = self.expr(callee, Some(callee_expected.clone()))?;
        self.graph.constrain_subtype(callee_ty, callee_expected)?;
        self.expr(arg, Some(arg_ty))?;
        Ok(ret_ty)
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

    fn record_spread(
        &mut self,
        spread: &poly_expr::RecordSpread<poly_expr::ExprId>,
    ) -> Result<(), SpecializeError> {
        match spread {
            poly_expr::RecordSpread::Head(expr) | poly_expr::RecordSpread::Tail(expr) => {
                self.expr(*expr, None)?;
            }
            poly_expr::RecordSpread::None => {}
        }
        Ok(())
    }

    fn bind_pat(&mut self, pat: poly_expr::PatId, ty: Type) -> Result<(), SpecializeError> {
        use poly_expr::Pat as PolyPat;
        match self.arena.pat(pat) {
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
            _ => {}
        }
        Ok(())
    }

    fn var_type(&mut self, ref_id: poly_expr::RefId) -> Result<Type, SpecializeError> {
        let Some(def) = self.arena.ref_target(ref_id) else {
            return Err(SpecializeError::UnresolvedRef { ref_id: ref_id.0 });
        };
        match self.arena.defs.get(def) {
            Some(poly_expr::Def::Let {
                scheme: Some(scheme),
                ..
            }) => self.instantiate_scheme(def, scheme),
            Some(poly_expr::Def::Arg) | Some(poly_expr::Def::Let { body: None, .. }) => Ok(self
                .local_types
                .get(&def)
                .cloned()
                .unwrap_or_else(|| self.fresh_value_slot())),
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
        let ty = types::instantiate_scheme_with_fresh(self.arena, def, scheme, |kind| {
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
        Ok(ty)
    }

    fn fresh_value_slot(&mut self) -> Type {
        self.graph.fresh_slot(TypeSlotKind::Value)
    }

    fn fresh_effect_slot(&mut self) -> Type {
        self.graph.fresh_slot(TypeSlotKind::Effect)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeSlotKind {
    Value,
    Effect,
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
}

impl<'a> ConstraintGraph<'a> {
    fn new(arena: &'a poly_expr::Arena) -> Self {
        Self {
            arena,
            slots: Vec::new(),
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

    fn slot(&self, slot: u32) -> Result<&TypeSlot, SpecializeError> {
        self.slots
            .get(slot as usize)
            .ok_or(SpecializeError::InvalidTypeSlot { slot })
    }

    fn constrain_subtype(&mut self, lower: Type, upper: Type) -> Result<(), SpecializeError> {
        if lower == upper {
            return Ok(());
        }
        match (lower, upper) {
            (Type::Never, _) | (_, Type::Any) => Ok(()),
            (Type::OpenVar(lower), Type::OpenVar(upper)) => self.add_edge(lower, upper),
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
            (Type::EffectRow(lower_items), Type::EffectRow(upper_items))
                if lower_items.len() == upper_items.len() =>
            {
                for (lower, upper) in lower_items.into_iter().zip(upper_items) {
                    self.constrain_subtype(lower, upper)?;
                }
                Ok(())
            }
            (Type::Stack { inner: lower, .. }, Type::Stack { inner: upper, .. }) => {
                self.constrain_subtype(*lower, *upper)
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

    fn instantiate_cast_scheme(
        &mut self,
        def: poly_expr::DefId,
        scheme: &poly::types::Scheme,
    ) -> Result<Type, SpecializeError> {
        let arena = self.arena;
        types::instantiate_scheme_with_fresh(arena, def, scheme, |kind| match kind {
            types::SchemeQuantifierKind::Value => self.fresh_slot(TypeSlotKind::Value),
            types::SchemeQuantifierKind::Effect => self.fresh_slot(TypeSlotKind::Effect),
        })
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
            Type::EffectRow(items) => self.resolve_all(items).map(Type::EffectRow),
            Type::Stack { inner, weight } => Ok(Type::Stack {
                inner: Box::new(self.resolve(inner)?),
                weight: weight.clone(),
            }),
            Type::Union(left, right) => Ok(Type::Union(
                Box::new(self.resolve(left)?),
                Box::new(self.resolve(right)?),
            )),
            Type::Intersection(left, right) => Ok(Type::Intersection(
                Box::new(self.resolve(left)?),
                Box::new(self.resolve(right)?),
            )),
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
        let lower = self.join_candidates(slot, &lower_bounds)?;
        let upper = self.meet_candidates(slot, &upper_bounds)?;
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
            (None, None) => return Err(SpecializeError::UndeterminedTypeSlot { slot }),
        };
        self.resolving.remove(&slot);
        self.solutions.insert(slot, solution.clone());
        Ok(solution)
    }

    fn join_candidates(
        &mut self,
        slot: u32,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut candidate: Option<Type> = None;
        for bound in bounds {
            let resolved = self.resolve(bound)?;
            candidate = Some(match candidate {
                Some(existing) => join_type_candidates(self.graph, slot, existing, resolved)?,
                None => resolved,
            });
        }
        Ok(candidate)
    }

    fn meet_candidates(
        &mut self,
        slot: u32,
        bounds: &[Type],
    ) -> Result<Option<Type>, SpecializeError> {
        let mut candidate: Option<Type> = None;
        for bound in bounds {
            let resolved = self.resolve(bound)?;
            candidate = Some(match candidate {
                Some(existing) => meet_type_candidates(self.graph, slot, existing, resolved)?,
                None => resolved,
            });
        }
        Ok(candidate)
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
        _ => false,
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

fn bool_type() -> Type {
    Type::Con {
        path: vec!["bool".to_string()],
        args: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use mono::Type;

    use super::solve_expr;

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
