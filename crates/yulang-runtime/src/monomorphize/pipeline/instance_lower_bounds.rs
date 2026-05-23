//! Propagate lower bounds inside already monomorphized function instances.
//!
//! The pass treats each monomorphic binding body as a closed local constraint
//! problem.  Call sites split callee, argument, and result slots explicitly;
//! variable references only point at their binding slot.

use super::total_substitute::{
    apply_runtime_function_param_lower, apply_runtime_function_result_lower,
    merge_runtime_open_or_default_slots_with_lower, runtime_function_lower_parts_for_substitute,
};
use super::*;
use crate::types::{hir_type_has_vars, runtime_core_type};

pub(super) fn apply_instance_lower_bounds(mut module: Module) -> Module {
    for _ in 0..8 {
        let binding_lowers = monomorphic_binding_lowers(&module);
        let mut pass = InstanceLowerBounds {
            binding_lowers,
            locals: Vec::new(),
            changed: 0,
        };
        for binding in &mut module.bindings {
            pass.binding(binding);
        }
        if pass.changed == 0 {
            break;
        }
    }
    module
}

struct InstanceLowerBounds {
    binding_lowers: Vec<(typed_ir::Path, RuntimeType)>,
    locals: Vec<LocalLower>,
    changed: usize,
}

#[derive(Clone)]
struct LocalLower {
    path: typed_ir::Path,
    lower: RuntimeType,
}

impl InstanceLowerBounds {
    fn binding(&mut self, binding: &mut Binding) {
        if !binding.type_params.is_empty() {
            return;
        }
        let base = self.locals.len();
        self.expr(&mut binding.body);
        self.locals.truncate(base);
        let body = runtime_core_type(&binding.body.ty);
        self.record_core_change(&mut binding.scheme.body, body);
    }

    fn expr(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::Lambda { param, body, .. } => {
                let param_path = typed_ir::Path::from_name(param.clone());
                let param_lower = runtime_function_lower_parts_for_substitute(&expr.ty)
                    .map(|(param, _)| param)
                    .unwrap_or(RuntimeType::Unknown);
                let local_index = self.push_local(param_path, param_lower);
                self.expr(body);
                let local_lower = self.locals[local_index].lower.clone();
                if runtime_type_is_meaningful_instance_lower(&local_lower) {
                    apply_runtime_function_param_lower(
                        &mut expr.ty,
                        &local_lower,
                        &mut self.changed,
                    );
                }
                if runtime_type_is_meaningful_instance_lower(&body.ty) {
                    apply_runtime_function_result_lower(&mut expr.ty, &body.ty, &mut self.changed);
                }
                if let Some((param, result)) = runtime_function_lower_parts_for_substitute(&expr.ty)
                {
                    self.merge_local(local_index, &param);
                    self.merge_runtime_type(&mut body.ty, &result);
                }
                self.locals.truncate(local_index);
            }
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                ..
            } => {
                self.expr(callee);
                self.expr(arg);
                self.propagate_apply(callee, arg, &mut expr.ty);
                if let Some(evidence) = evidence {
                    self.materialize_apply_evidence(evidence, &callee.ty, &arg.ty, &expr.ty);
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.expr(cond);
                self.expr(then_branch);
                self.expr(else_branch);
                self.merge_runtime_type(&mut then_branch.ty, &expr.ty);
                self.merge_runtime_type(&mut else_branch.ty, &expr.ty);
                if runtime_type_is_meaningful_instance_lower(&then_branch.ty) {
                    self.merge_runtime_type(&mut expr.ty, &then_branch.ty);
                }
                if runtime_type_is_meaningful_instance_lower(&else_branch.ty) {
                    self.merge_runtime_type(&mut expr.ty, &else_branch.ty);
                }
            }
            ExprKind::Tuple(items) => {
                self.propagate_tuple_lower_to_items(&expr.ty, items);
                for item in items.iter_mut() {
                    self.expr(item);
                }
                self.propagate_tuple_items_to_lower(&mut expr.ty, items);
            }
            ExprKind::Record { fields, spread } => {
                for field in fields {
                    self.expr(&mut field.value);
                }
                self.record_spread_expr(spread);
            }
            ExprKind::Variant { value, .. } => {
                if let Some(value) = value {
                    self.expr(value);
                }
            }
            ExprKind::Select { base, .. } => self.expr(base),
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                self.expr(scrutinee);
                for arm in arms {
                    let base = self.locals.len();
                    self.pattern(&mut arm.pattern, &scrutinee.ty);
                    if let Some(guard) = &mut arm.guard {
                        self.expr(guard);
                    }
                    self.expr(&mut arm.body);
                    self.merge_runtime_type(&mut arm.body.ty, &expr.ty);
                    if runtime_type_is_meaningful_instance_lower(&arm.body.ty) {
                        self.merge_runtime_type(&mut expr.ty, &arm.body.ty);
                    }
                    self.locals.truncate(base);
                }
            }
            ExprKind::Block { stmts, tail } => self.block(stmts, tail, &mut expr.ty),
            ExprKind::Handle { body, arms, .. } => {
                self.expr(body);
                for arm in arms {
                    let base = self.locals.len();
                    self.pattern(&mut arm.payload, &RuntimeType::Core(typed_ir::Type::Any));
                    if let Some(resume) = &mut arm.resume {
                        self.push_local(
                            typed_ir::Path::from_name(resume.name.clone()),
                            resume.ty.clone(),
                        );
                    }
                    if let Some(guard) = &mut arm.guard {
                        self.expr(guard);
                    }
                    self.expr(&mut arm.body);
                    self.locals.truncate(base);
                }
            }
            ExprKind::BindHere { expr }
            | ExprKind::LocalPushId { body: expr, .. }
            | ExprKind::Coerce { expr, .. }
            | ExprKind::Pack { expr, .. } => self.expr(expr),
            ExprKind::Thunk {
                expr: body,
                effect,
                value,
            } => {
                if let RuntimeType::Thunk {
                    effect: ty_effect,
                    value: ty_value,
                } = &expr.ty
                {
                    if effect != ty_effect {
                        *effect = ty_effect.clone();
                        self.changed += 1;
                    }
                    if value != ty_value.as_ref() {
                        *value = ty_value.as_ref().clone();
                        self.changed += 1;
                    }
                    self.merge_runtime_type(&mut body.ty, ty_value);
                }
                self.expr(body);
                if runtime_type_is_meaningful_instance_lower(&body.ty) {
                    let next = RuntimeType::thunk(effect.clone(), body.ty.clone());
                    self.merge_runtime_type(&mut expr.ty, &next);
                }
            }
            ExprKind::AddId { thunk, .. } => self.expr(thunk),
            ExprKind::Var(path) => {
                let path = path.clone();
                self.var(expr, &path);
            }
            ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => {}
        }
        self.sync_wrapper(expr);
    }

    fn block(
        &mut self,
        stmts: &mut [Stmt],
        tail: &mut Option<Box<Expr>>,
        block_ty: &mut RuntimeType,
    ) {
        let base = self.locals.len();
        for stmt in stmts.iter_mut() {
            self.stmt(stmt);
        }
        if let Some(tail) = tail {
            self.expr(tail);
            if runtime_type_is_meaningful_instance_lower(&tail.ty) {
                self.merge_runtime_type(block_ty, &tail.ty);
            }
            self.merge_runtime_type(&mut tail.ty, block_ty);
        }
        for stmt in stmts.iter_mut() {
            if let Stmt::Let { pattern, .. } = stmt {
                self.materialize_pattern_from_locals(pattern, base);
            }
        }
        self.locals.truncate(base);
    }

    fn stmt(&mut self, stmt: &mut Stmt) {
        match stmt {
            Stmt::Let { pattern, value } => {
                self.expr(value);
                self.pattern(pattern, &value.ty);
            }
            Stmt::Expr(expr) => self.expr(expr),
            Stmt::Module { def, body } => {
                let index = self.push_local(def.clone(), body.ty.clone());
                self.expr(body);
                self.merge_local(index, &body.ty);
            }
        }
    }

    fn pattern(&mut self, pattern: &mut Pattern, expected: &RuntimeType) {
        let ty = pattern_runtime_type_mut(pattern);
        self.merge_runtime_type(ty, expected);
        match pattern {
            Pattern::Bind { name, ty } => {
                self.push_local(typed_ir::Path::from_name(name.clone()), ty.clone());
            }
            Pattern::Tuple { items, ty } => {
                if let RuntimeType::Core(typed_ir::Type::Tuple(item_tys)) = ty {
                    for (item, item_ty) in items.iter_mut().zip(item_tys.iter()) {
                        self.pattern(item, &RuntimeType::Core(item_ty.clone()));
                    }
                } else {
                    for item in items {
                        self.pattern(item, expected);
                    }
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    self.pattern(&mut field.pattern, expected);
                    if let Some(default) = &mut field.default {
                        self.expr(default);
                    }
                }
            }
            Pattern::Variant { value, .. } | Pattern::List { spread: value, .. } => {
                if let Some(value) = value {
                    self.pattern(value, expected);
                }
            }
            Pattern::Or { left, right, .. } => {
                self.pattern(left, expected);
                self.pattern(right, expected);
            }
            Pattern::As { pattern, name, ty } => {
                self.pattern(pattern, expected);
                self.push_local(typed_ir::Path::from_name(name.clone()), ty.clone());
            }
            Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
        }
    }

    fn materialize_pattern_from_locals(&mut self, pattern: &mut Pattern, base: usize) {
        match pattern {
            Pattern::Bind { name, ty } | Pattern::As { name, ty, .. } => {
                let path = typed_ir::Path::from_name(name.clone());
                if let Some(lower) = self.local_lower_since(&path, base) {
                    self.merge_runtime_type(ty, &lower);
                }
                if let Pattern::As { pattern, .. } = pattern {
                    self.materialize_pattern_from_locals(pattern, base);
                }
            }
            Pattern::Tuple { items, .. } => {
                for item in items {
                    self.materialize_pattern_from_locals(item, base);
                }
            }
            Pattern::List {
                prefix,
                spread,
                suffix,
                ..
            } => {
                for item in prefix.iter_mut().chain(suffix.iter_mut()) {
                    self.materialize_pattern_from_locals(item, base);
                }
                if let Some(spread) = spread {
                    self.materialize_pattern_from_locals(spread, base);
                }
            }
            Pattern::Record { fields, .. } => {
                for field in fields {
                    self.materialize_pattern_from_locals(&mut field.pattern, base);
                }
            }
            Pattern::Variant { value, .. } => {
                if let Some(value) = value {
                    self.materialize_pattern_from_locals(value, base);
                }
            }
            Pattern::Or { left, right, .. } => {
                self.materialize_pattern_from_locals(left, base);
                self.materialize_pattern_from_locals(right, base);
            }
            Pattern::Wildcard { .. } | Pattern::Lit { .. } => {}
        }
    }

    fn record_spread_expr(&mut self, spread: &mut Option<RecordSpreadExpr>) {
        if let Some(spread) = spread {
            match spread {
                RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => self.expr(expr),
            }
        }
    }

    fn var(&mut self, expr: &mut Expr, path: &typed_ir::Path) {
        if let Some(index) = self.local_index(path) {
            let lower = self.locals[index].lower.clone();
            self.merge_runtime_type(&mut expr.ty, &lower);
            self.merge_local(index, &expr.ty);
            return;
        }
        if let Some(lower) = self.binding_lower(path) {
            self.merge_runtime_type(&mut expr.ty, &lower);
        }
    }

    fn propagate_apply(&mut self, callee: &mut Expr, arg: &mut Expr, result: &mut RuntimeType) {
        if runtime_type_is_meaningful_instance_lower(&arg.ty) {
            apply_runtime_function_param_lower(&mut callee.ty, &arg.ty, &mut self.changed);
        }
        if runtime_function_lower_parts_for_substitute(result).is_some() {
            apply_runtime_function_result_lower(&mut callee.ty, result, &mut self.changed);
        }
        if let Some((param, ret)) = runtime_function_lower_parts_for_substitute(&callee.ty) {
            self.merge_runtime_type(&mut arg.ty, &param);
            self.merge_runtime_type(result, &ret);
        }
    }

    fn materialize_apply_evidence(
        &mut self,
        evidence: &mut typed_ir::ApplyEvidence,
        callee: &RuntimeType,
        arg: &RuntimeType,
        result: &RuntimeType,
    ) {
        self.materialize_bounds_from_runtime(&mut evidence.callee, callee);
        let arg_bounds = evidence.expected_arg.as_mut().unwrap_or(&mut evidence.arg);
        self.materialize_bounds_from_runtime(arg_bounds, arg);
        let _ = result;
    }

    fn materialize_bounds_from_runtime(
        &mut self,
        bounds: &mut typed_ir::TypeBounds,
        lower: &RuntimeType,
    ) {
        let lower = runtime_core_type(lower);
        if !core_type_is_meaningful_instance_lower(&lower) || !bounds_has_open_or_default(bounds) {
            return;
        }
        let next = typed_ir::TypeBounds::exact(lower);
        if *bounds != next {
            *bounds = next;
            self.changed += 1;
        }
    }

    fn propagate_tuple_lower_to_items(&mut self, ty: &RuntimeType, items: &mut [Expr]) {
        let RuntimeType::Core(typed_ir::Type::Tuple(item_tys)) = ty else {
            return;
        };
        if item_tys.len() != items.len() {
            return;
        }
        for (item, item_ty) in items.iter_mut().zip(item_tys) {
            self.merge_runtime_type(&mut item.ty, &RuntimeType::Core(item_ty.clone()));
        }
    }

    fn propagate_tuple_items_to_lower(&mut self, ty: &mut RuntimeType, items: &[Expr]) {
        if !items
            .iter()
            .all(|item| runtime_type_is_meaningful_instance_lower(&item.ty))
        {
            return;
        }
        let lower = RuntimeType::Core(typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| runtime_core_type(&item.ty))
                .collect(),
        ));
        self.merge_runtime_type(ty, &lower);
    }

    fn push_local(&mut self, path: typed_ir::Path, lower: RuntimeType) -> usize {
        let index = self.locals.len();
        self.locals.push(LocalLower { path, lower });
        index
    }

    fn local_index(&self, path: &typed_ir::Path) -> Option<usize> {
        self.locals.iter().rposition(|local| local.path == *path)
    }

    fn local_lower_since(&self, path: &typed_ir::Path, base: usize) -> Option<RuntimeType> {
        self.locals
            .iter()
            .enumerate()
            .rev()
            .find(|(index, local)| *index >= base && local.path == *path)
            .map(|(_, local)| local.lower.clone())
    }

    fn merge_local(&mut self, index: usize, lower: &RuntimeType) {
        let mut current = self.locals[index].lower.clone();
        self.merge_runtime_type(&mut current, lower);
        self.locals[index].lower = current;
    }

    fn binding_lower(&self, path: &typed_ir::Path) -> Option<RuntimeType> {
        self.binding_lowers
            .iter()
            .rev()
            .find(|(binding, _)| binding == path)
            .map(|(_, ty)| ty.clone())
    }

    fn merge_runtime_type(&mut self, current: &mut RuntimeType, lower: &RuntimeType) {
        if !runtime_type_is_meaningful_instance_lower(lower) {
            return;
        }
        let next = merge_runtime_open_or_default_slots_with_lower(current, lower);
        if *current != next {
            *current = next;
            self.changed += 1;
        }
    }

    fn record_core_change(&mut self, current: &mut typed_ir::Type, next: typed_ir::Type) {
        if *current != next {
            *current = next;
            self.changed += 1;
        }
    }

    fn sync_wrapper(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::AddId { thunk, .. } | ExprKind::LocalPushId { body: thunk, .. } => {
                let next = merge_runtime_open_or_default_slots_with_lower(&thunk.ty, &expr.ty);
                if thunk.ty != next {
                    thunk.ty = next;
                    self.changed += 1;
                }
            }
            _ => {}
        }
    }
}

fn monomorphic_binding_lowers(module: &Module) -> Vec<(typed_ir::Path, RuntimeType)> {
    module
        .bindings
        .iter()
        .filter(|binding| binding.type_params.is_empty())
        .map(|binding| (binding.name.clone(), binding.body.ty.clone()))
        .collect()
}

fn pattern_runtime_type_mut(pattern: &mut Pattern) -> &mut RuntimeType {
    match pattern {
        Pattern::Wildcard { ty }
        | Pattern::Bind { ty, .. }
        | Pattern::Lit { ty, .. }
        | Pattern::Tuple { ty, .. }
        | Pattern::List { ty, .. }
        | Pattern::Record { ty, .. }
        | Pattern::Variant { ty, .. }
        | Pattern::Or { ty, .. }
        | Pattern::As { ty, .. } => ty,
    }
}

fn runtime_type_is_meaningful_instance_lower(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => false,
        RuntimeType::Core(ty) => core_type_is_meaningful_instance_lower(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_is_meaningful_instance_lower(param)
                || runtime_type_is_meaningful_instance_lower(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_is_meaningful_instance_lower(effect)
                || runtime_type_is_meaningful_instance_lower(value)
        }
    }
}

fn core_type_is_meaningful_instance_lower(ty: &typed_ir::Type) -> bool {
    !core_type_is_bottom_like_instance_lower(ty) && !core_type_is_default_unit_shape(ty)
}

fn core_type_is_bottom_like_instance_lower(ty: &typed_ir::Type) -> bool {
    matches!(
        ty,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Never
    )
}

fn bounds_has_open_or_default(bounds: &typed_ir::TypeBounds) -> bool {
    bounds
        .lower
        .as_deref()
        .is_none_or(core_type_has_open_or_default)
        || bounds
            .upper
            .as_deref()
            .is_none_or(core_type_has_open_or_default)
}

fn core_type_has_open_or_default(ty: &typed_ir::Type) -> bool {
    core_type_is_default_unit_shape(ty)
        || hir_type_has_vars(&RuntimeType::Core(ty.clone()))
        || matches!(ty, typed_ir::Type::Unknown | typed_ir::Type::Any)
}

fn core_type_is_default_unit_shape(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Tuple(items) => items.is_empty(),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_is_default_unit_shape(param)
                && effect_is_empty(param_effect)
                && effect_is_empty(ret_effect)
                && core_type_is_default_unit_shape(ret)
        }
        _ => false,
    }
}
