use super::type_graph::{
    TypeGraph, TypeGraphBuildReport, TypeGraphLowerSnapshotReport, TypeGraphLowerSolution,
    TypeGraphSlotKind, TypeGraphTypeVarLowerReport, TypeGraphTypeVarLowerSolution,
    TypeGraphTypeVarScope, TypeGraphUpperSupplementReport, build_type_graph,
};
use super::*;
use crate::types::{
    BoundsChoice, choose_bounds_type, substitute_apply_evidence, substitute_hir_type,
    substitute_type,
};
use std::collections::BTreeMap;
use std::mem;

#[derive(Debug, Clone, Default)]
pub(super) struct TotalSubstituteReport {
    pub(super) graph: TypeGraphBuildReport,
    pub(super) lower_snapshot: TypeGraphLowerSnapshotReport,
    pub(super) upper_supplement: TypeGraphUpperSupplementReport,
    pub(super) type_vars: TypeGraphTypeVarLowerReport,
    pub(super) final_defaults: FillHolesReport,
    pub(super) applied_slots: usize,
    pub(super) upper_supplemented_slots: usize,
}

pub(super) fn total_substitute_module_preview(module: &Module) -> TotalSubstituteReport {
    let (type_graph, graph) = build_type_graph(module);
    let lower_solution = type_graph.solve_lower_snapshot();
    let upper_solution = type_graph.solve_upper_supplements(&lower_solution);
    let upper_supplemented_slots = upper_solution.candidate_count();
    let final_defaults = type_graph.solve_final_defaults(&lower_solution, &upper_solution);
    let upper_supplement = upper_solution.report;
    let applied_slots = lower_solution.candidate_count();
    let lower_snapshot = lower_solution.report.clone();
    let type_var_solution = type_graph.solve_type_var_lowers();
    let _recursive_lower_substitutions = type_var_solution.substitution_count();
    let type_vars = type_var_solution.report;
    TotalSubstituteReport {
        graph,
        lower_snapshot,
        upper_supplement,
        type_vars,
        final_defaults,
        applied_slots,
        upper_supplemented_slots,
    }
}

pub(super) fn total_substitute_module(mut module: Module) -> (Module, TotalSubstituteReport) {
    let mut total_applied_slots = 0;
    let mut last = None;
    for _ in 0..8 {
        let (type_graph, graph) = build_type_graph(&module);
        let lower_solution = type_graph.solve_lower_snapshot();
        let upper_solution = type_graph.solve_upper_supplements(&lower_solution);
        let upper_supplemented_slots = upper_solution.candidate_count();
        let final_defaults = type_graph.solve_final_defaults(&lower_solution, &upper_solution);
        let upper_supplement = upper_solution.report;
        let lower_snapshot = lower_solution.report.clone();
        let type_var_solution = type_graph.solve_type_var_lowers();
        let type_vars = type_var_solution.report.clone();
        let mut application = TypeVarLowerApplication {
            graph: &type_graph,
            lower_solution: &lower_solution,
            solution: &type_var_solution,
            next_slot: 0,
            next_scope: 0,
            applied_slots: 0,
        };
        application.module(&mut module);
        total_applied_slots += application.applied_slots;
        let applied_slots = total_applied_slots;
        last = Some(TotalSubstituteReport {
            graph,
            lower_snapshot,
            upper_supplement,
            type_vars,
            final_defaults,
            applied_slots,
            upper_supplemented_slots,
        });
        if application.applied_slots == 0 {
            break;
        }
    }
    let Some(report) = last else {
        return (module, TotalSubstituteReport::default());
    };
    (module, report)
}

struct TypeVarLowerApplication<'a> {
    graph: &'a TypeGraph,
    lower_solution: &'a TypeGraphLowerSolution,
    solution: &'a TypeGraphTypeVarLowerSolution,
    next_slot: usize,
    next_scope: usize,
    applied_slots: usize,
}

impl TypeVarLowerApplication<'_> {
    fn module(&mut self, module: &mut Module) {
        for binding in &mut module.bindings {
            self.binding(binding);
        }
        for (index, expr) in module.root_exprs.iter_mut().enumerate() {
            self.expr(expr, true);
            self.apply_slot_runtime_type(TypeGraphSlotKind::RootExpr { index }, &mut expr.ty, true);
        }
    }

    fn binding(&mut self, binding: &mut Binding) {
        self.scheme_requirements(&binding.scheme);
        self.consume_slot(TypeGraphSlotKind::BindingScheme {
            binding: binding.name.clone(),
        });
        let active = binding.type_params.is_empty();
        self.apply_slot_runtime_type(
            TypeGraphSlotKind::BindingBody {
                binding: binding.name.clone(),
            },
            &mut binding.body.ty,
            active,
        );
        self.expr(&mut binding.body, active);
        if active {
            if let Some(lower) = local_var_runtime_lower(&binding.body, &binding.name) {
                let next = merge_runtime_open_or_default_slots_with_lower(&binding.body.ty, &lower);
                self.record_core_change(&mut binding.body.ty, next);
            }
            let body = binding.body.ty.clone();
            apply_local_var_runtime_lower(
                &mut binding.body,
                &binding.name,
                &body,
                &mut self.applied_slots,
            );
            let scheme_body = runtime_core_type(&binding.body.ty);
            self.record_core_change(&mut binding.scheme.body, scheme_body);
        }
    }

    fn scheme_requirements(&mut self, scheme: &typed_ir::Scheme) {
        for _requirement in &scheme.requirements {
            self.consume_type_var_scope();
        }
    }

    fn expr(&mut self, expr: &mut Expr, active: bool) {
        self.apply_slot_runtime_type(TypeGraphSlotKind::Expr, &mut expr.ty, active);
        match &mut expr.kind {
            ExprKind::Lambda { param, body, .. } => {
                if runtime_function_parts_for_substitute(&expr.ty).is_some() {
                    self.consume_slot(TypeGraphSlotKind::LambdaParam {
                        name: param.clone(),
                    });
                    self.consume_slot(TypeGraphSlotKind::LambdaResult {
                        name: param.clone(),
                    });
                }
                self.expr(body, active);
                if active && runtime_type_is_usable_lower_for_substitute(&body.ty) {
                    apply_runtime_function_result_lower(
                        &mut expr.ty,
                        &body.ty,
                        &mut self.applied_slots,
                    );
                }
                if active {
                    let local = typed_ir::Path::from_name(param.clone());
                    if let Some(lower) = local_var_runtime_lower(body, &local) {
                        apply_runtime_function_param_lower(
                            &mut expr.ty,
                            &lower,
                            &mut self.applied_slots,
                        );
                    }
                    if let Some(param_ty) = runtime_function_param_for_substitute(&expr.ty) {
                        apply_local_var_runtime_lower(
                            body,
                            &local,
                            &param_ty,
                            &mut self.applied_slots,
                        );
                    }
                }
            }
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                self.expr(callee, active);
                self.expr(arg, active);
                self.apply_slot_runtime_type(
                    TypeGraphSlotKind::ApplyCallee,
                    &mut callee.ty,
                    active,
                );
                self.apply_slot_runtime_type(TypeGraphSlotKind::ApplyArg, &mut arg.ty, active);
                self.apply_slot_runtime_type(TypeGraphSlotKind::ApplyResult, &mut expr.ty, active);
                self.apply_function_shape_slots(&mut callee.ty, &arg.ty, &expr.ty, active);
                self.sync_redundant_node_type_fields(callee);
                if let Some(evidence) = evidence {
                    self.apply_apply_evidence_slots(evidence, active);
                    let substitutions = self.next_scope_substitutions().cloned();
                    if active && let Some(substitutions) = substitutions.as_ref() {
                        self.apply_apply_lower_scope(
                            &mut callee.ty,
                            &mut arg.ty,
                            &mut expr.ty,
                            Some(evidence),
                            substitutions,
                        );
                    }
                }
                if let Some(instantiation) = instantiation {
                    let substitutions = self.next_scope_substitutions().cloned();
                    if active && let Some(substitutions) = substitutions.as_ref() {
                        self.apply_apply_lower_scope(
                            &mut callee.ty,
                            &mut arg.ty,
                            &mut expr.ty,
                            evidence.as_mut(),
                            substitutions,
                        );
                        self.apply_type_instantiation(instantiation, substitutions);
                    }
                }
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                evidence,
            } => {
                self.expr(cond, active);
                self.expr(then_branch, active);
                self.expr(else_branch, active);
                let _ = evidence;
            }
            ExprKind::Tuple(items) => {
                for item in items {
                    self.expr(item, active);
                }
            }
            ExprKind::Record { fields, spread } => {
                for field in fields {
                    self.expr(&mut field.value, active);
                }
                self.record_spread_expr(spread, active);
            }
            ExprKind::Variant { value, .. } => {
                if let Some(value) = value {
                    self.expr(value, active);
                }
            }
            ExprKind::Select { base, .. } => self.expr(base, active),
            ExprKind::Match {
                scrutinee,
                arms,
                evidence,
            } => {
                self.expr(scrutinee, active);
                for arm in arms {
                    self.pattern(&mut arm.pattern, active);
                    if let Some(guard) = &mut arm.guard {
                        self.expr(guard, active);
                    }
                    self.expr(&mut arm.body, active);
                }
                let _ = evidence;
            }
            ExprKind::Block { stmts, tail } => {
                for stmt in stmts {
                    self.stmt(stmt, active);
                }
                if let Some(tail) = tail {
                    self.expr(tail, active);
                }
            }
            ExprKind::Handle {
                body,
                arms,
                evidence,
                handler,
            } => {
                self.expr(body, active);
                for arm in arms {
                    self.pattern(&mut arm.payload, active);
                    if let Some(resume) = &mut arm.resume {
                        self.apply_slot_runtime_type(
                            TypeGraphSlotKind::Pattern,
                            &mut resume.ty,
                            active,
                        );
                    }
                    if let Some(guard) = &mut arm.guard {
                        self.expr(guard, active);
                    }
                    self.expr(&mut arm.body, active);
                }
                let _ = (evidence, handler);
            }
            ExprKind::BindHere { expr }
            | ExprKind::LocalPushId { body: expr, .. }
            | ExprKind::Coerce { expr, .. }
            | ExprKind::Pack { expr, .. } => {
                self.expr(expr, active);
            }
            ExprKind::Thunk { expr, .. } => {
                self.expr(expr, active);
            }
            ExprKind::AddId { thunk, .. } => {
                self.expr(thunk, active);
            }
            ExprKind::Var(_)
            | ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => {}
        }
        self.sync_redundant_node_type_fields(expr);
    }

    fn stmt(&mut self, stmt: &mut Stmt, active: bool) {
        match stmt {
            Stmt::Let { pattern, value } => {
                self.expr(value, active);
                self.pattern(pattern, active);
                self.apply_slot_runtime_type(TypeGraphSlotKind::LetValue, &mut value.ty, active);
                self.apply_slot_runtime_type(
                    TypeGraphSlotKind::LetPattern,
                    pattern_runtime_type_mut_for_substitute(pattern),
                    active,
                );
            }
            Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => self.expr(expr, active),
        }
    }

    fn pattern(&mut self, pattern: &mut Pattern, active: bool) {
        self.apply_slot_runtime_type(
            TypeGraphSlotKind::Pattern,
            pattern_runtime_type_mut_for_substitute(pattern),
            active,
        );
        match pattern {
            Pattern::Tuple { items, .. } => {
                for item in items {
                    self.pattern(item, active);
                }
            }
            Pattern::List {
                prefix,
                spread,
                suffix,
                ..
            } => {
                for item in prefix {
                    self.pattern(item, active);
                }
                if let Some(spread) = spread {
                    self.pattern(spread, active);
                }
                for item in suffix {
                    self.pattern(item, active);
                }
            }
            Pattern::Record { fields, spread, .. } => {
                for field in fields {
                    self.pattern(&mut field.pattern, active);
                    if let Some(default) = &mut field.default {
                        self.expr(default, active);
                    }
                }
                if let Some(spread) = spread {
                    match spread {
                        RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                            self.pattern(pattern, active)
                        }
                    }
                }
            }
            Pattern::Variant { value, .. } => {
                if let Some(value) = value {
                    self.pattern(value, active);
                }
            }
            Pattern::Or { left, right, .. } => {
                self.pattern(left, active);
                self.pattern(right, active);
            }
            Pattern::As { pattern, .. } => self.pattern(pattern, active),
            Pattern::Wildcard { .. } | Pattern::Bind { .. } | Pattern::Lit { .. } => {}
        }
    }

    fn record_spread_expr(&mut self, spread: &mut Option<RecordSpreadExpr>, active: bool) {
        if let Some(spread) = spread {
            match spread {
                RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                    self.expr(expr, active);
                }
            }
        }
    }

    fn consume_type_var_scope(&mut self) {
        self.next_scope += 1;
    }

    fn consume_slot(&mut self, expected: TypeGraphSlotKind) {
        let _ = self.next_slot(expected);
    }

    fn apply_slot_runtime_type(
        &mut self,
        expected: TypeGraphSlotKind,
        ty: &mut RuntimeType,
        active: bool,
    ) {
        let candidate = self
            .next_slot(expected)
            .and_then(|slot| self.lower_solution.candidate(slot).cloned());
        if active && let Some(candidate) = candidate {
            self.apply_runtime_lower_candidate(ty, &candidate);
        }
    }

    fn next_slot(
        &mut self,
        expected: TypeGraphSlotKind,
    ) -> Option<super::type_graph::TypeGraphSlotId> {
        let slot = self
            .graph
            .slot_at(self.next_slot)
            .unwrap_or_else(|| panic!("type graph application missing slot {expected:?}"));
        debug_assert_eq!(
            mem::discriminant(&slot.kind),
            mem::discriminant(&expected),
            "type graph application order diverged: expected {expected:?}, got {:?}",
            slot.kind
        );
        self.next_slot += 1;
        Some(slot.id)
    }

    fn next_scope_substitutions(&mut self) -> Option<&BTreeMap<typed_ir::TypeVar, typed_ir::Type>> {
        let scope = TypeGraphTypeVarScope::from_index(self.next_scope);
        self.next_scope += 1;
        self.solution.substitutions_for_scope(scope)
    }

    fn apply_apply_lower_scope(
        &mut self,
        callee_ty: &mut RuntimeType,
        arg_ty: &mut RuntimeType,
        result_ty: &mut RuntimeType,
        evidence: Option<&mut typed_ir::ApplyEvidence>,
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ) {
        self.apply_runtime_type(callee_ty, substitutions);
        self.apply_runtime_type(arg_ty, substitutions);
        self.apply_runtime_type(result_ty, substitutions);
        if let Some(evidence) = evidence {
            self.apply_apply_evidence(evidence, substitutions);
        }
    }

    fn apply_function_shape_slots(
        &mut self,
        callee_ty: &mut RuntimeType,
        arg_ty: &RuntimeType,
        result_ty: &RuntimeType,
        active: bool,
    ) {
        if runtime_function_parts_for_substitute(callee_ty).is_none() {
            return;
        }
        let param = self
            .next_slot(TypeGraphSlotKind::FunctionParam)
            .and_then(|slot| self.lower_solution.candidate(slot).cloned());
        let result = self
            .next_slot(TypeGraphSlotKind::FunctionResult)
            .and_then(|slot| self.lower_solution.candidate(slot).cloned());
        if !active {
            return;
        }
        if let Some(param) = param {
            apply_runtime_function_param_lower(callee_ty, &param, &mut self.applied_slots);
        }
        if runtime_type_is_usable_lower_for_substitute(arg_ty) {
            apply_runtime_function_param_lower(callee_ty, arg_ty, &mut self.applied_slots);
        }
        if let Some(result) = result {
            apply_runtime_function_result_lower(callee_ty, &result, &mut self.applied_slots);
        }
        if runtime_type_is_usable_lower_for_substitute(result_ty) {
            apply_runtime_function_result_lower(callee_ty, result_ty, &mut self.applied_slots);
        }
    }

    fn apply_apply_evidence_slots(&mut self, evidence: &mut typed_ir::ApplyEvidence, active: bool) {
        if choose_bounds_runtime_type_for_substitute(&evidence.callee).is_some() {
            self.apply_slot_type_bounds(
                TypeGraphSlotKind::ApplyEvidenceCallee,
                &mut evidence.callee,
                active,
            );
        }
        let arg_bounds = evidence.expected_arg.as_mut().unwrap_or(&mut evidence.arg);
        if choose_bounds_runtime_type_for_substitute(arg_bounds).is_some() {
            self.apply_slot_type_bounds(TypeGraphSlotKind::ApplyEvidenceArg, arg_bounds, active);
        }
        if choose_bounds_runtime_type_for_substitute(&evidence.result).is_some() {
            self.apply_slot_type_bounds(
                TypeGraphSlotKind::ApplyEvidenceResult,
                &mut evidence.result,
                active,
            );
        }
    }

    fn apply_slot_type_bounds(
        &mut self,
        expected: TypeGraphSlotKind,
        bounds: &mut typed_ir::TypeBounds,
        active: bool,
    ) {
        let candidate = self
            .next_slot(expected)
            .and_then(|slot| self.lower_solution.candidate(slot).cloned());
        if !active {
            return;
        }
        let Some(candidate) = candidate else {
            return;
        };
        let candidate = runtime_core_type(&candidate);
        if type_bounds_contains_open_slot(bounds) {
            let next = typed_ir::TypeBounds::exact(candidate);
            self.record_core_change(bounds, next);
        }
    }

    fn apply_type_instantiation(
        &mut self,
        instantiation: &mut TypeInstantiation,
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ) {
        for substitution in &mut instantiation.args {
            self.apply_core_type(&mut substitution.ty, substitutions);
        }
    }

    fn apply_apply_evidence(
        &mut self,
        evidence: &mut typed_ir::ApplyEvidence,
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ) {
        let next = substitute_apply_evidence(evidence.clone(), substitutions);
        self.record_core_change(evidence, next);
    }

    fn apply_runtime_type(
        &mut self,
        ty: &mut RuntimeType,
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ) {
        if substitutions.is_empty() {
            return;
        }
        let next = substitute_hir_type(ty, substitutions);
        self.record_core_change(ty, next);
    }

    fn apply_runtime_lower_candidate(&mut self, ty: &mut RuntimeType, candidate: &RuntimeType) {
        if !runtime_type_contains_open_slot_for_substitute(ty) {
            return;
        }
        let next = merge_runtime_open_slots_with_lower(ty, candidate);
        self.record_core_change(ty, next);
    }

    fn apply_core_type(
        &mut self,
        ty: &mut typed_ir::Type,
        substitutions: &BTreeMap<typed_ir::TypeVar, typed_ir::Type>,
    ) {
        if substitutions.is_empty() {
            return;
        }
        let next = substitute_type(ty, substitutions);
        self.record_core_change(ty, next);
    }

    fn record_core_change<T>(&mut self, target: &mut T, next: T)
    where
        T: PartialEq,
    {
        if *target != next {
            *target = next;
            self.applied_slots += 1;
        }
    }

    fn sync_redundant_node_type_fields(&mut self, expr: &mut Expr) {
        match &mut expr.kind {
            ExprKind::AddId { thunk, .. } | ExprKind::LocalPushId { body: thunk, .. } => {
                let next = merge_runtime_open_or_default_slots_with_lower(&thunk.ty, &expr.ty);
                self.record_core_change(&mut thunk.ty, next);
            }
            _ => {}
        }
        if let (
            ExprKind::Thunk { effect, value, .. },
            RuntimeType::Thunk {
                effect: ty_effect,
                value: ty_value,
            },
        ) = (&mut expr.kind, &expr.ty)
        {
            if effect != ty_effect {
                *effect = ty_effect.clone();
                self.applied_slots += 1;
            }
            if value != ty_value.as_ref() {
                *value = ty_value.as_ref().clone();
                self.applied_slots += 1;
            }
        }
    }
}

fn pattern_runtime_type_mut_for_substitute(pattern: &mut Pattern) -> &mut RuntimeType {
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

fn local_var_runtime_lower(expr: &Expr, local: &typed_ir::Path) -> Option<RuntimeType> {
    let mut lower = None;
    collect_local_var_runtime_lower(expr, local, &mut lower);
    lower
}

fn collect_local_var_runtime_lower(
    expr: &Expr,
    local: &typed_ir::Path,
    lower: &mut Option<RuntimeType>,
) {
    if let ExprKind::Var(path) = &expr.kind
        && path == local
        && runtime_type_is_usable_lower_for_substitute(&expr.ty)
    {
        merge_optional_runtime_lower(lower, expr.ty.clone());
    }
    match &expr.kind {
        ExprKind::Lambda { param, body, .. } => {
            if typed_ir::Path::from_name(param.clone()) != *local {
                collect_local_var_runtime_lower(body, local, lower);
            }
        }
        ExprKind::Apply { callee, arg, .. } => {
            collect_local_var_runtime_lower(callee, local, lower);
            collect_local_var_runtime_lower(arg, local, lower);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_local_var_runtime_lower(cond, local, lower);
            collect_local_var_runtime_lower(then_branch, local, lower);
            collect_local_var_runtime_lower(else_branch, local, lower);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_local_var_runtime_lower(item, local, lower);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_local_var_runtime_lower(&field.value, local, lower);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        collect_local_var_runtime_lower(expr, local, lower);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_local_var_runtime_lower(value, local, lower);
            }
        }
        ExprKind::Select { base, .. } => collect_local_var_runtime_lower(base, local, lower),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_local_var_runtime_lower(scrutinee, local, lower);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_local_var_runtime_lower(guard, local, lower);
                }
                collect_local_var_runtime_lower(&arm.body, local, lower);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_local_var_runtime_lower_from_stmt(stmt, local, lower);
            }
            if let Some(tail) = tail {
                collect_local_var_runtime_lower(tail, local, lower);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_local_var_runtime_lower(body, local, lower);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_local_var_runtime_lower(guard, local, lower);
                }
                collect_local_var_runtime_lower(&arm.body, local, lower);
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::LocalPushId { body: expr, .. }
        | ExprKind::AddId { thunk: expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => {
            collect_local_var_runtime_lower(expr, local, lower);
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_local_var_runtime_lower_from_stmt(
    stmt: &Stmt,
    local: &typed_ir::Path,
    lower: &mut Option<RuntimeType>,
) {
    match stmt {
        Stmt::Let { value, .. } => collect_local_var_runtime_lower(value, local, lower),
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => {
            collect_local_var_runtime_lower(expr, local, lower)
        }
    }
}

fn apply_local_var_runtime_lower(
    expr: &mut Expr,
    local: &typed_ir::Path,
    lower: &RuntimeType,
    applied_slots: &mut usize,
) {
    if let ExprKind::Var(path) = &expr.kind
        && path == local
    {
        let next = merge_runtime_open_or_default_slots_with_lower(&expr.ty, lower);
        if expr.ty != next {
            expr.ty = next;
            *applied_slots += 1;
        }
    }
    match &mut expr.kind {
        ExprKind::Lambda { param, body, .. } => {
            if typed_ir::Path::from_name(param.clone()) != *local {
                apply_local_var_runtime_lower(body, local, lower, applied_slots);
            }
        }
        ExprKind::Apply { callee, arg, .. } => {
            apply_local_var_runtime_lower(callee, local, lower, applied_slots);
            apply_local_var_runtime_lower(arg, local, lower, applied_slots);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            apply_local_var_runtime_lower(cond, local, lower, applied_slots);
            apply_local_var_runtime_lower(then_branch, local, lower, applied_slots);
            apply_local_var_runtime_lower(else_branch, local, lower, applied_slots);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                apply_local_var_runtime_lower(item, local, lower, applied_slots);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                apply_local_var_runtime_lower(&mut field.value, local, lower, applied_slots);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        apply_local_var_runtime_lower(expr, local, lower, applied_slots);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                apply_local_var_runtime_lower(value, local, lower, applied_slots);
            }
        }
        ExprKind::Select { base, .. } => {
            apply_local_var_runtime_lower(base, local, lower, applied_slots)
        }
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            apply_local_var_runtime_lower(scrutinee, local, lower, applied_slots);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    apply_local_var_runtime_lower(guard, local, lower, applied_slots);
                }
                apply_local_var_runtime_lower(&mut arm.body, local, lower, applied_slots);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                apply_local_var_runtime_lower_to_stmt(stmt, local, lower, applied_slots);
            }
            if let Some(tail) = tail {
                apply_local_var_runtime_lower(tail, local, lower, applied_slots);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            apply_local_var_runtime_lower(body, local, lower, applied_slots);
            for arm in arms {
                if let Some(guard) = &mut arm.guard {
                    apply_local_var_runtime_lower(guard, local, lower, applied_slots);
                }
                apply_local_var_runtime_lower(&mut arm.body, local, lower, applied_slots);
            }
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::LocalPushId { body: expr, .. }
        | ExprKind::AddId { thunk: expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => {
            apply_local_var_runtime_lower(expr, local, lower, applied_slots);
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn apply_local_var_runtime_lower_to_stmt(
    stmt: &mut Stmt,
    local: &typed_ir::Path,
    lower: &RuntimeType,
    applied_slots: &mut usize,
) {
    match stmt {
        Stmt::Let { value, .. } => {
            apply_local_var_runtime_lower(value, local, lower, applied_slots);
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => {
            apply_local_var_runtime_lower(expr, local, lower, applied_slots);
        }
    }
}

fn merge_optional_runtime_lower(target: &mut Option<RuntimeType>, lower: RuntimeType) {
    match target {
        Some(current) => {
            let next = merge_runtime_open_or_default_slots_with_lower(current, &lower);
            if &next != current {
                *current = next;
            }
        }
        None => *target = Some(lower),
    }
}

fn choose_bounds_runtime_type_for_substitute(bounds: &typed_ir::TypeBounds) -> Option<RuntimeType> {
    choose_bounds_type(bounds, BoundsChoice::VisiblePrincipal).map(RuntimeType::core)
}

fn runtime_function_parts_for_substitute(ty: &RuntimeType) -> Option<(&RuntimeType, &RuntimeType)> {
    match ty {
        RuntimeType::Fun { param, ret } => Some((param, ret)),
        RuntimeType::Core(typed_ir::Type::Fun { .. }) => Some((ty, ty)),
        RuntimeType::Thunk { value, .. } => runtime_function_parts_for_substitute(value),
        RuntimeType::Unknown | RuntimeType::Core(_) => None,
    }
}

fn runtime_function_lower_parts_for_substitute(
    ty: &RuntimeType,
) -> Option<(RuntimeType, RuntimeType)> {
    match ty {
        RuntimeType::Fun { param, ret } => Some((param.as_ref().clone(), ret.as_ref().clone())),
        RuntimeType::Core(typed_ir::Type::Fun { param, ret, .. }) => Some((
            RuntimeType::core(param.as_ref().clone()),
            RuntimeType::core(ret.as_ref().clone()),
        )),
        RuntimeType::Thunk { value, .. } => runtime_function_lower_parts_for_substitute(value),
        RuntimeType::Unknown | RuntimeType::Core(_) => None,
    }
}

fn runtime_function_param_for_substitute(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(param.as_ref().clone()),
        RuntimeType::Core(typed_ir::Type::Fun { param, .. }) => {
            Some(RuntimeType::core(param.as_ref().clone()))
        }
        RuntimeType::Thunk { value, .. } => runtime_function_param_for_substitute(value),
        RuntimeType::Unknown | RuntimeType::Core(_) => None,
    }
}

fn apply_runtime_function_param_lower(
    ty: &mut RuntimeType,
    candidate: &RuntimeType,
    applied_slots: &mut usize,
) {
    match ty {
        RuntimeType::Fun { param, .. } => {
            let next = merge_runtime_open_or_default_slots_with_lower(param, candidate);
            if **param != next {
                **param = next;
                *applied_slots += 1;
            }
        }
        RuntimeType::Core(typed_ir::Type::Fun { param, .. }) => {
            let candidate = runtime_core_type(candidate);
            let next = merge_core_open_or_default_slots_with_lower(param, &candidate);
            if param.as_ref() != &next {
                *param = Box::new(next);
                *applied_slots += 1;
            }
        }
        RuntimeType::Thunk { value, .. } => {
            apply_runtime_function_param_lower(value, candidate, applied_slots);
        }
        RuntimeType::Unknown | RuntimeType::Core(_) => {}
    }
}

fn apply_runtime_function_result_lower(
    ty: &mut RuntimeType,
    candidate: &RuntimeType,
    applied_slots: &mut usize,
) {
    match ty {
        RuntimeType::Fun { ret, .. } => {
            let next = merge_runtime_open_or_default_slots_with_lower(ret, candidate);
            if **ret != next {
                **ret = next;
                *applied_slots += 1;
            }
        }
        RuntimeType::Core(typed_ir::Type::Fun { ret, .. }) => {
            let candidate = runtime_core_type(candidate);
            let next = merge_core_open_or_default_slots_with_lower(ret, &candidate);
            if ret.as_ref() != &next {
                *ret = Box::new(next);
                *applied_slots += 1;
            }
        }
        RuntimeType::Thunk { value, .. } => {
            apply_runtime_function_result_lower(value, candidate, applied_slots);
        }
        RuntimeType::Unknown | RuntimeType::Core(_) => {}
    }
}

fn merge_runtime_open_slots_with_lower(current: &RuntimeType, lower: &RuntimeType) -> RuntimeType {
    match current {
        RuntimeType::Unknown => lower.clone(),
        RuntimeType::Core(current) => RuntimeType::core(merge_core_open_slots_with_lower(
            current,
            &runtime_core_type(lower),
        )),
        RuntimeType::Fun { param, ret } => {
            let Some((lower_param, lower_ret)) = runtime_function_lower_parts_for_substitute(lower)
            else {
                return current.clone();
            };
            RuntimeType::fun(
                merge_runtime_open_slots_with_lower(param, &lower_param),
                merge_runtime_open_slots_with_lower(ret, &lower_ret),
            )
        }
        RuntimeType::Thunk { effect, value } => {
            let RuntimeType::Thunk {
                effect: lower_effect,
                value: lower_value,
            } = lower
            else {
                return RuntimeType::thunk(
                    merge_core_open_slots_with_lower(effect, &runtime_core_type(lower)),
                    value.as_ref().clone(),
                );
            };
            RuntimeType::thunk(
                merge_core_open_slots_with_lower(effect, lower_effect),
                merge_runtime_open_slots_with_lower(value, lower_value),
            )
        }
    }
}

fn merge_runtime_open_or_default_slots_with_lower(
    current: &RuntimeType,
    lower: &RuntimeType,
) -> RuntimeType {
    match current {
        RuntimeType::Unknown => lower.clone(),
        RuntimeType::Core(current) => RuntimeType::core(
            merge_core_open_or_default_slots_with_lower(current, &runtime_core_type(lower)),
        ),
        RuntimeType::Fun { param, ret } => {
            let Some((lower_param, lower_ret)) = runtime_function_lower_parts_for_substitute(lower)
            else {
                return current.clone();
            };
            RuntimeType::fun(
                merge_runtime_open_or_default_slots_with_lower(param, &lower_param),
                merge_runtime_open_or_default_slots_with_lower(ret, &lower_ret),
            )
        }
        RuntimeType::Thunk { effect, value } => {
            let RuntimeType::Thunk {
                effect: lower_effect,
                value: lower_value,
            } = lower
            else {
                return RuntimeType::thunk(
                    merge_core_open_or_default_slots_with_lower(effect, &runtime_core_type(lower)),
                    value.as_ref().clone(),
                );
            };
            RuntimeType::thunk(
                merge_core_open_or_default_slots_with_lower(effect, lower_effect),
                merge_runtime_open_or_default_slots_with_lower(value, lower_value),
            )
        }
    }
}

fn merge_core_open_slots_with_lower(
    current: &typed_ir::Type,
    lower: &typed_ir::Type,
) -> typed_ir::Type {
    match current {
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => lower.clone(),
        typed_ir::Type::Named { path, args } => {
            let typed_ir::Type::Named {
                path: lower_path,
                args: lower_args,
            } = lower
            else {
                return current.clone();
            };
            if path != lower_path || args.len() != lower_args.len() {
                return current.clone();
            }
            typed_ir::Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .zip(lower_args)
                    .map(|(current, lower)| merge_type_arg_open_slots_with_lower(current, lower))
                    .collect(),
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            let typed_ir::Type::Fun {
                param: lower_param,
                param_effect: lower_param_effect,
                ret_effect: lower_ret_effect,
                ret: lower_ret,
            } = lower
            else {
                return current.clone();
            };
            typed_ir::Type::Fun {
                param: Box::new(merge_core_open_slots_with_lower(param, lower_param)),
                param_effect: Box::new(merge_core_open_slots_with_lower(
                    param_effect,
                    lower_param_effect,
                )),
                ret_effect: Box::new(merge_core_open_slots_with_lower(
                    ret_effect,
                    lower_ret_effect,
                )),
                ret: Box::new(merge_core_open_slots_with_lower(ret, lower_ret)),
            }
        }
        typed_ir::Type::Tuple(items) => {
            let typed_ir::Type::Tuple(lower_items) = lower else {
                return current.clone();
            };
            if items.len() != lower_items.len() {
                return current.clone();
            }
            typed_ir::Type::Tuple(
                items
                    .iter()
                    .zip(lower_items)
                    .map(|(current, lower)| merge_core_open_slots_with_lower(current, lower))
                    .collect(),
            )
        }
        typed_ir::Type::Record(record) => {
            let typed_ir::Type::Record(lower_record) = lower else {
                return current.clone();
            };
            if record.fields.len() != lower_record.fields.len() {
                return current.clone();
            }
            typed_ir::Type::Record(typed_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .zip(&lower_record.fields)
                    .map(|(field, lower_field)| typed_ir::RecordField {
                        name: field.name.clone(),
                        value: merge_core_open_slots_with_lower(&field.value, &lower_field.value),
                        optional: field.optional,
                    })
                    .collect(),
                spread: merge_record_spread_open_slots_with_lower(
                    record.spread.as_ref(),
                    lower_record.spread.as_ref(),
                ),
            })
        }
        typed_ir::Type::Variant(variant) => {
            let typed_ir::Type::Variant(lower_variant) = lower else {
                return current.clone();
            };
            if variant.cases.len() != lower_variant.cases.len() {
                return current.clone();
            }
            typed_ir::Type::Variant(typed_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .zip(&lower_variant.cases)
                    .map(|(case, lower_case)| typed_ir::VariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .zip(&lower_case.payloads)
                            .map(|(current, lower)| {
                                merge_core_open_slots_with_lower(current, lower)
                            })
                            .collect(),
                    })
                    .collect(),
                tail: match (variant.tail.as_deref(), lower_variant.tail.as_deref()) {
                    (Some(tail), Some(lower_tail)) => {
                        Some(Box::new(merge_core_open_slots_with_lower(tail, lower_tail)))
                    }
                    _ => variant.tail.clone(),
                },
            })
        }
        typed_ir::Type::Row { items, tail } => {
            let typed_ir::Type::Row {
                items: lower_items,
                tail: lower_tail,
            } = lower
            else {
                return current.clone();
            };
            if items.len() != lower_items.len() {
                return current.clone();
            }
            typed_ir::Type::Row {
                items: items
                    .iter()
                    .zip(lower_items)
                    .map(|(current, lower)| merge_core_open_slots_with_lower(current, lower))
                    .collect(),
                tail: Box::new(merge_core_open_slots_with_lower(tail, lower_tail)),
            }
        }
        typed_ir::Type::Union(items) => {
            merge_core_choice_open_slots_with_lower(items, lower, |items| {
                typed_ir::Type::Union(items)
            })
        }
        typed_ir::Type::Inter(items) => {
            merge_core_choice_open_slots_with_lower(items, lower, |items| {
                typed_ir::Type::Inter(items)
            })
        }
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(merge_core_open_slots_with_lower(body, lower)),
        },
        typed_ir::Type::Never => current.clone(),
    }
}

fn merge_core_open_or_default_slots_with_lower(
    current: &typed_ir::Type,
    lower: &typed_ir::Type,
) -> typed_ir::Type {
    if core_type_is_default_unit_for_substitute(current)
        && !core_type_is_default_unit_for_substitute(lower)
        && !core_type_contains_open_slot_for_substitute(lower)
        && !core_type_is_bottom_like_for_substitute(lower)
    {
        return lower.clone();
    }
    match current {
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => lower.clone(),
        typed_ir::Type::Named { path, args } => {
            let typed_ir::Type::Named {
                path: lower_path,
                args: lower_args,
            } = lower
            else {
                return current.clone();
            };
            if path != lower_path || args.len() != lower_args.len() {
                return current.clone();
            }
            typed_ir::Type::Named {
                path: path.clone(),
                args: args
                    .iter()
                    .zip(lower_args)
                    .map(|(current, lower)| {
                        merge_type_arg_open_or_default_slots_with_lower(current, lower)
                    })
                    .collect(),
            }
        }
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            let typed_ir::Type::Fun {
                param: lower_param,
                param_effect: lower_param_effect,
                ret_effect: lower_ret_effect,
                ret: lower_ret,
            } = lower
            else {
                return current.clone();
            };
            typed_ir::Type::Fun {
                param: Box::new(merge_core_open_or_default_slots_with_lower(
                    param,
                    lower_param,
                )),
                param_effect: Box::new(merge_core_open_or_default_slots_with_lower(
                    param_effect,
                    lower_param_effect,
                )),
                ret_effect: Box::new(merge_core_open_or_default_slots_with_lower(
                    ret_effect,
                    lower_ret_effect,
                )),
                ret: Box::new(merge_core_open_or_default_slots_with_lower(ret, lower_ret)),
            }
        }
        typed_ir::Type::Tuple(items) => {
            let typed_ir::Type::Tuple(lower_items) = lower else {
                return current.clone();
            };
            if items.len() != lower_items.len() {
                return current.clone();
            }
            typed_ir::Type::Tuple(
                items
                    .iter()
                    .zip(lower_items)
                    .map(|(current, lower)| {
                        merge_core_open_or_default_slots_with_lower(current, lower)
                    })
                    .collect(),
            )
        }
        typed_ir::Type::Record(record) => {
            let typed_ir::Type::Record(lower_record) = lower else {
                return current.clone();
            };
            if record.fields.len() != lower_record.fields.len() {
                return current.clone();
            }
            typed_ir::Type::Record(typed_ir::RecordType {
                fields: record
                    .fields
                    .iter()
                    .zip(&lower_record.fields)
                    .map(|(field, lower_field)| typed_ir::RecordField {
                        name: field.name.clone(),
                        value: merge_core_open_or_default_slots_with_lower(
                            &field.value,
                            &lower_field.value,
                        ),
                        optional: field.optional,
                    })
                    .collect(),
                spread: merge_record_spread_open_or_default_slots_with_lower(
                    record.spread.as_ref(),
                    lower_record.spread.as_ref(),
                ),
            })
        }
        typed_ir::Type::Variant(variant) => {
            let typed_ir::Type::Variant(lower_variant) = lower else {
                return current.clone();
            };
            if variant.cases.len() != lower_variant.cases.len() {
                return current.clone();
            }
            typed_ir::Type::Variant(typed_ir::VariantType {
                cases: variant
                    .cases
                    .iter()
                    .zip(&lower_variant.cases)
                    .map(|(case, lower_case)| typed_ir::VariantCase {
                        name: case.name.clone(),
                        payloads: case
                            .payloads
                            .iter()
                            .zip(&lower_case.payloads)
                            .map(|(current, lower)| {
                                merge_core_open_or_default_slots_with_lower(current, lower)
                            })
                            .collect(),
                    })
                    .collect(),
                tail: match (variant.tail.as_deref(), lower_variant.tail.as_deref()) {
                    (Some(tail), Some(lower_tail)) => Some(Box::new(
                        merge_core_open_or_default_slots_with_lower(tail, lower_tail),
                    )),
                    _ => variant.tail.clone(),
                },
            })
        }
        typed_ir::Type::Row { items, tail } => {
            let typed_ir::Type::Row {
                items: lower_items,
                tail: lower_tail,
            } = lower
            else {
                return current.clone();
            };
            if items.len() != lower_items.len() {
                return current.clone();
            }
            typed_ir::Type::Row {
                items: items
                    .iter()
                    .zip(lower_items)
                    .map(|(current, lower)| {
                        merge_core_open_or_default_slots_with_lower(current, lower)
                    })
                    .collect(),
                tail: Box::new(merge_core_open_or_default_slots_with_lower(
                    tail, lower_tail,
                )),
            }
        }
        typed_ir::Type::Union(items) => {
            merge_core_choice_open_or_default_slots_with_lower(items, lower, |items| {
                typed_ir::Type::Union(items)
            })
        }
        typed_ir::Type::Inter(items) => {
            merge_core_choice_open_or_default_slots_with_lower(items, lower, |items| {
                typed_ir::Type::Inter(items)
            })
        }
        typed_ir::Type::Recursive { var, body } => typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(merge_core_open_or_default_slots_with_lower(body, lower)),
        },
        typed_ir::Type::Never => current.clone(),
    }
}

fn merge_type_arg_open_slots_with_lower(
    current: &typed_ir::TypeArg,
    lower: &typed_ir::TypeArg,
) -> typed_ir::TypeArg {
    match (current, lower) {
        (typed_ir::TypeArg::Type(current), typed_ir::TypeArg::Type(lower)) => {
            typed_ir::TypeArg::Type(merge_core_open_slots_with_lower(current, lower))
        }
        (typed_ir::TypeArg::Bounds(current), typed_ir::TypeArg::Bounds(lower)) => {
            typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                lower: merge_optional_core_open_slots_with_lower(
                    current.lower.as_deref(),
                    lower.lower.as_deref(),
                )
                .map(Box::new),
                upper: merge_optional_core_open_slots_with_lower(
                    current.upper.as_deref(),
                    lower.upper.as_deref(),
                )
                .map(Box::new),
            })
        }
        _ => current.clone(),
    }
}

fn merge_type_arg_open_or_default_slots_with_lower(
    current: &typed_ir::TypeArg,
    lower: &typed_ir::TypeArg,
) -> typed_ir::TypeArg {
    match (current, lower) {
        (typed_ir::TypeArg::Type(current), typed_ir::TypeArg::Type(lower)) => {
            typed_ir::TypeArg::Type(merge_core_open_or_default_slots_with_lower(current, lower))
        }
        (typed_ir::TypeArg::Bounds(current), typed_ir::TypeArg::Bounds(lower)) => {
            typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                lower: merge_optional_core_open_or_default_slots_with_lower(
                    current.lower.as_deref(),
                    lower.lower.as_deref(),
                )
                .map(Box::new),
                upper: merge_optional_core_open_or_default_slots_with_lower(
                    current.upper.as_deref(),
                    lower.upper.as_deref(),
                )
                .map(Box::new),
            })
        }
        _ => current.clone(),
    }
}

fn merge_optional_core_open_slots_with_lower(
    current: Option<&typed_ir::Type>,
    lower: Option<&typed_ir::Type>,
) -> Option<typed_ir::Type> {
    match (current, lower) {
        (Some(current), Some(lower)) => Some(merge_core_open_slots_with_lower(current, lower)),
        (None, Some(lower)) if core_type_contains_open_slot_for_substitute(lower) => {
            Some(lower.clone())
        }
        (Some(current), None) => Some(current.clone()),
        (None, _) => None,
    }
}

fn merge_optional_core_open_or_default_slots_with_lower(
    current: Option<&typed_ir::Type>,
    lower: Option<&typed_ir::Type>,
) -> Option<typed_ir::Type> {
    match (current, lower) {
        (Some(current), Some(lower)) => {
            Some(merge_core_open_or_default_slots_with_lower(current, lower))
        }
        (None, Some(lower)) if core_type_contains_open_slot_for_substitute(lower) => {
            Some(lower.clone())
        }
        (Some(current), None) => Some(current.clone()),
        (None, _) => None,
    }
}

fn merge_record_spread_open_slots_with_lower(
    current: Option<&typed_ir::RecordSpread>,
    lower: Option<&typed_ir::RecordSpread>,
) -> Option<typed_ir::RecordSpread> {
    match (current, lower) {
        (
            Some(typed_ir::RecordSpread::Head(current)),
            Some(typed_ir::RecordSpread::Head(lower)),
        ) => Some(typed_ir::RecordSpread::Head(Box::new(
            merge_core_open_slots_with_lower(current, lower),
        ))),
        (
            Some(typed_ir::RecordSpread::Tail(current)),
            Some(typed_ir::RecordSpread::Tail(lower)),
        ) => Some(typed_ir::RecordSpread::Tail(Box::new(
            merge_core_open_slots_with_lower(current, lower),
        ))),
        (Some(current), _) => Some(current.clone()),
        (None, _) => None,
    }
}

fn merge_record_spread_open_or_default_slots_with_lower(
    current: Option<&typed_ir::RecordSpread>,
    lower: Option<&typed_ir::RecordSpread>,
) -> Option<typed_ir::RecordSpread> {
    match (current, lower) {
        (
            Some(typed_ir::RecordSpread::Head(current)),
            Some(typed_ir::RecordSpread::Head(lower)),
        ) => Some(typed_ir::RecordSpread::Head(Box::new(
            merge_core_open_or_default_slots_with_lower(current, lower),
        ))),
        (
            Some(typed_ir::RecordSpread::Tail(current)),
            Some(typed_ir::RecordSpread::Tail(lower)),
        ) => Some(typed_ir::RecordSpread::Tail(Box::new(
            merge_core_open_or_default_slots_with_lower(current, lower),
        ))),
        (Some(current), _) => Some(current.clone()),
        (None, _) => None,
    }
}

fn merge_core_choice_open_slots_with_lower(
    items: &[typed_ir::Type],
    lower: &typed_ir::Type,
    rebuild: impl FnOnce(Vec<typed_ir::Type>) -> typed_ir::Type,
) -> typed_ir::Type {
    let lower_items = match lower {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => items,
        _ => return rebuild(items.to_vec()),
    };
    if items.len() != lower_items.len() {
        return rebuild(items.to_vec());
    }
    rebuild(
        items
            .iter()
            .zip(lower_items)
            .map(|(current, lower)| merge_core_open_slots_with_lower(current, lower))
            .collect(),
    )
}

fn merge_core_choice_open_or_default_slots_with_lower(
    items: &[typed_ir::Type],
    lower: &typed_ir::Type,
    rebuild: impl FnOnce(Vec<typed_ir::Type>) -> typed_ir::Type,
) -> typed_ir::Type {
    let lower_items = match lower {
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => items,
        _ => return rebuild(items.to_vec()),
    };
    if items.len() != lower_items.len() {
        return rebuild(items.to_vec());
    }
    rebuild(
        items
            .iter()
            .zip(lower_items)
            .map(|(current, lower)| merge_core_open_or_default_slots_with_lower(current, lower))
            .collect(),
    )
}

fn runtime_type_is_usable_lower_for_substitute(ty: &RuntimeType) -> bool {
    !matches!(ty, RuntimeType::Unknown)
        && !runtime_type_contains_open_slot_for_substitute(ty)
        && !runtime_type_is_bottom_like_for_substitute(ty)
}

fn runtime_type_is_bottom_like_for_substitute(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_is_bottom_like_for_substitute(ty),
        RuntimeType::Fun { .. } => false,
        RuntimeType::Thunk { value, .. } => runtime_type_is_bottom_like_for_substitute(value),
    }
}

fn core_type_is_bottom_like_for_substitute(ty: &typed_ir::Type) -> bool {
    matches!(
        ty,
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Never
    )
}

fn core_type_is_default_unit_for_substitute(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Tuple(items) if items.is_empty())
}

fn runtime_type_contains_open_slot_for_substitute(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Unknown => true,
        RuntimeType::Core(ty) => core_type_contains_open_slot_for_substitute(ty),
        RuntimeType::Fun { param, ret } => {
            runtime_type_contains_open_slot_for_substitute(param)
                || runtime_type_contains_open_slot_for_substitute(ret)
        }
        RuntimeType::Thunk { effect, value } => {
            core_type_contains_open_slot_for_substitute(effect)
                || runtime_type_contains_open_slot_for_substitute(value)
        }
    }
}

fn core_type_contains_open_slot_for_substitute(ty: &typed_ir::Type) -> bool {
    match ty {
        typed_ir::Type::Unknown | typed_ir::Type::Any | typed_ir::Type::Var(_) => true,
        typed_ir::Type::Named { args, .. } => args.iter().any(type_arg_contains_open_slot),
        typed_ir::Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            core_type_contains_open_slot_for_substitute(param)
                || core_type_contains_open_slot_for_substitute(param_effect)
                || core_type_contains_open_slot_for_substitute(ret_effect)
                || core_type_contains_open_slot_for_substitute(ret)
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => items
            .iter()
            .any(core_type_contains_open_slot_for_substitute),
        typed_ir::Type::Record(record) => {
            record
                .fields
                .iter()
                .any(|field| core_type_contains_open_slot_for_substitute(&field.value))
                || record.spread.as_ref().is_some_and(|spread| match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        core_type_contains_open_slot_for_substitute(ty)
                    }
                })
        }
        typed_ir::Type::Variant(variant) => {
            variant.cases.iter().any(|case| {
                case.payloads
                    .iter()
                    .any(core_type_contains_open_slot_for_substitute)
            }) || variant
                .tail
                .as_deref()
                .is_some_and(core_type_contains_open_slot_for_substitute)
        }
        typed_ir::Type::Row { items, tail } => {
            items
                .iter()
                .any(core_type_contains_open_slot_for_substitute)
                || core_type_contains_open_slot_for_substitute(tail)
        }
        typed_ir::Type::Recursive { body, .. } => core_type_contains_open_slot_for_substitute(body),
        typed_ir::Type::Never => false,
    }
}

fn type_arg_contains_open_slot(arg: &typed_ir::TypeArg) -> bool {
    match arg {
        typed_ir::TypeArg::Type(ty) => core_type_contains_open_slot_for_substitute(ty),
        typed_ir::TypeArg::Bounds(bounds) => type_bounds_contains_open_slot(bounds),
    }
}

fn type_bounds_contains_open_slot(bounds: &typed_ir::TypeBounds) -> bool {
    bounds
        .lower
        .as_deref()
        .is_some_and(core_type_contains_open_slot_for_substitute)
        || bounds
            .upper
            .as_deref()
            .is_some_and(core_type_contains_open_slot_for_substitute)
}
