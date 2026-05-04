use std::collections::{HashMap, HashSet};

use super::*;
use crate::ir::{Binding, Expr, ExprKind, Module, RecordSpreadExpr, Root, Stmt};
use crate::types::{core_type_has_vars, hir_type_has_vars};

#[derive(Debug, Clone)]
pub struct DemandCollector {
    generic_bindings: HashSet<core_ir::Path>,
    generic_role_impls: HashMap<core_ir::Name, Vec<RoleImplCollectCandidate>>,
    enclosing_thunk_effects: Vec<DemandEffect>,
    expected_signatures: Vec<DemandSignature>,
    queue: DemandQueue,
}

impl DemandCollector {
    pub fn from_module(module: &Module) -> Self {
        let generic_bindings = module
            .bindings
            .iter()
            .filter(|binding| binding_needs_demand_monomorphization(binding))
            .map(|binding| binding.name.clone())
            .collect();
        let generic_role_impls = generic_role_impls(module);
        Self {
            generic_bindings,
            generic_role_impls,
            enclosing_thunk_effects: Vec::new(),
            expected_signatures: Vec::new(),
            queue: DemandQueue::default(),
        }
    }

    pub fn collect_module(&mut self, module: &Module) {
        for expr in &module.root_exprs {
            self.collect_expr(expr);
        }
        for binding in reachable_collectable_bindings(module) {
            self.collect_expr(&binding.body);
        }
    }

    pub fn queue(&self) -> &DemandQueue {
        &self.queue
    }

    pub fn into_queue(self) -> DemandQueue {
        self.queue
    }

    fn collect_expr(&mut self, expr: &Expr) {
        let expected_signature = self.expected_signatures.pop();
        match &expr.kind {
            ExprKind::Apply {
                callee,
                arg,
                evidence: _,
                instantiation: _,
            } => {
                if let Some((target, head, args)) = applied_call_with_head(expr) {
                    let demand_target = collect_demand_call_target(target);
                    if self.generic_bindings.contains(&demand_target) {
                        let expected = curried_call_type(&args, expr.ty.clone());
                        let principal_hints =
                            applied_call_principal_signature_hints(expr, args.len());
                        let (arg_signatures, ret) = self.call_signatures_from_head(
                            &demand_target,
                            head,
                            &args,
                            expr,
                            expected_signature.clone(),
                            principal_hints,
                        );
                        self.queue.push_signature(
                            demand_target,
                            expected,
                            curried_signatures(&arg_signatures, ret),
                        );
                        for arg in args {
                            self.collect_expr(arg);
                        }
                        return;
                    }
                }
                if let Some((target, head, args)) = applied_call_with_head(expr)
                    && is_role_method_path(target)
                    && let Some(method) = target.segments.last()
                    && let Some(candidates) = self.generic_role_impls.get(method)
                {
                    let expected = curried_call_type(&args, expr.ty.clone());
                    let principal_hints = applied_call_principal_signature_hints(expr, args.len());
                    let (arg_signatures, ret) =
                        call_signatures_from_head(head, &args, expr, principal_hints);
                    let ret = expected_signature.clone().unwrap_or(ret);
                    let signature = curried_signatures(&arg_signatures, ret);
                    let impl_signature = role_impl_demand_signature(&signature);
                    for candidate in candidates {
                        if !role_impl_candidate_accepts(&candidate.signature, &signature) {
                            continue;
                        }
                        self.queue.push_signature(
                            candidate.path.clone(),
                            expected.clone(),
                            impl_signature.clone(),
                        );
                    }
                    for arg in args {
                        self.collect_expr(arg);
                    }
                    return;
                }
                self.collect_expr(callee);
                self.collect_expr(arg);
            }
            ExprKind::Lambda { body, .. }
            | ExprKind::LocalPushId { body, .. }
            | ExprKind::AddId { thunk: body, .. }
            | ExprKind::Coerce { expr: body, .. }
            | ExprKind::Pack { expr: body, .. } => self.collect_expr(body),
            ExprKind::BindHere { expr: inner } => {
                let effect = self.observed_bind_here_effect(inner);
                if demand_effect_is_empty(&effect) {
                    self.collect_expr(inner);
                } else {
                    let value = expected_signature
                        .clone()
                        .unwrap_or_else(|| expr_signature(expr));
                    self.collect_expr_with_expected(
                        inner,
                        DemandSignature::Thunk {
                            effect,
                            value: Box::new(value),
                        },
                    );
                }
            }
            ExprKind::Thunk {
                effect, expr: body, ..
            } => {
                self.enclosing_thunk_effects
                    .push(DemandEffect::from_core_type(effect));
                self.collect_expr(body);
                self.enclosing_thunk_effects.pop();
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_expr_with_expected(
                    cond,
                    DemandSignature::Core(DemandCoreType::Named {
                        path: core_ir::Path::from_name(core_ir::Name("bool".to_string())),
                        args: Vec::new(),
                    }),
                );
                if let Some(expected) = expected_signature {
                    self.collect_expr_with_expected(then_branch, expected.clone());
                    self.collect_expr_with_expected(else_branch, expected);
                } else {
                    self.collect_expr(then_branch);
                    self.collect_expr(else_branch);
                }
            }
            ExprKind::Tuple(items) => {
                for item in items {
                    self.collect_expr(item);
                }
            }
            ExprKind::Record { fields, spread } => {
                for field in fields {
                    self.collect_expr(&field.value);
                }
                if let Some(spread) = spread {
                    match spread {
                        crate::ir::RecordSpreadExpr::Head(expr)
                        | crate::ir::RecordSpreadExpr::Tail(expr) => self.collect_expr(expr),
                    }
                }
            }
            ExprKind::Variant { value, .. } => {
                if let Some(value) = value {
                    self.collect_expr(value);
                }
            }
            ExprKind::Select { base, .. } => self.collect_expr(base),
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                self.collect_expr(scrutinee);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.body);
                }
            }
            ExprKind::Block { stmts, tail } => {
                for stmt in stmts {
                    self.collect_stmt(stmt);
                }
                if let Some(tail) = tail {
                    if let Some(expected) = expected_signature {
                        self.collect_expr_with_expected(tail, expected);
                    } else {
                        self.collect_expr(tail);
                    }
                }
            }
            ExprKind::Handle { body, arms, .. } => {
                self.collect_expr(body);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        self.collect_expr(guard);
                    }
                    self.collect_expr(&arm.body);
                }
            }
            ExprKind::Var(_)
            | ExprKind::EffectOp(_)
            | ExprKind::PrimitiveOp(_)
            | ExprKind::Lit(_)
            | ExprKind::PeekId
            | ExprKind::FindId { .. } => {}
        }
    }

    fn collect_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
                self.collect_expr(value);
            }
        }
    }

    fn collect_expr_with_expected(&mut self, expr: &Expr, expected: DemandSignature) {
        let depth = self.expected_signatures.len();
        self.expected_signatures.push(expected);
        self.collect_expr(expr);
        self.expected_signatures.truncate(depth);
    }

    fn call_signatures_from_head(
        &self,
        target: &core_ir::Path,
        head: &Expr,
        args: &[&Expr],
        expr: &Expr,
        expected: Option<DemandSignature>,
        principal_hints: Option<(Vec<DemandSignature>, DemandSignature)>,
    ) -> (Vec<DemandSignature>, DemandSignature) {
        let (arg_signatures, ret) = call_signatures_from_head(head, args, expr, principal_hints);
        let ret = expected
            .unwrap_or_else(|| self.lift_known_handler_return_to_enclosing_effect(target, ret));
        let (arg_signatures, ret) =
            closed_collect_call_signature(target, arg_signatures, ret, args.len());
        let arg_signatures = strengthen_handler_arg_signatures(target, arg_signatures, &ret);
        (arg_signatures, ret)
    }

    fn lift_known_handler_return_to_enclosing_effect(
        &self,
        target: &core_ir::Path,
        ret: DemandSignature,
    ) -> DemandSignature {
        let consumed = known_consumed_effects_for_target(target);
        if consumed.is_empty() {
            return ret;
        }
        let Some(effect) = self.enclosing_thunk_effects.last().cloned() else {
            return ret;
        };
        if demand_effect_is_empty(&effect) {
            return ret;
        }
        if let DemandSignature::Thunk {
            effect: ret_effect,
            value,
        } = ret
        {
            if demand_effect_is_consumed_by(&ret_effect, &consumed) {
                return DemandSignature::Thunk { effect, value };
            }
            return DemandSignature::Thunk {
                effect: ret_effect,
                value,
            };
        }
        DemandSignature::Thunk {
            effect,
            value: Box::new(ret),
        }
    }

    fn observed_bind_here_effect(&self, inner: &Expr) -> DemandEffect {
        let annotated =
            thunk_effect_signature(&inner.ty).filter(|effect| !demand_effect_is_empty(effect));
        let enclosing = self
            .enclosing_thunk_effects
            .last()
            .cloned()
            .filter(|effect| !demand_effect_is_empty(effect));
        match (annotated, enclosing) {
            (Some(annotated), Some(enclosing)) => merge_demand_effects(annotated, enclosing),
            (Some(effect), None) | (None, Some(effect)) => effect,
            (None, None) => DemandEffect::Empty,
        }
    }
}

fn reachable_collectable_bindings(module: &Module) -> Vec<&Binding> {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), binding))
        .collect::<HashMap<_, _>>();
    let mut out = Vec::new();
    let mut stack = Vec::new();
    for root in &module.roots {
        if let Root::Binding(path) = root {
            stack.push(path.clone());
        }
    }
    for expr in &module.root_exprs {
        collect_expr_refs(expr, &mut stack);
    }
    let mut seen = HashSet::new();
    while let Some(path) = stack.pop() {
        if !seen.insert(path.clone()) {
            continue;
        }
        let Some(binding) = bindings.get(&path) else {
            continue;
        };
        if !collectable_binding_body(binding) {
            continue;
        }
        out.push(*binding);
        collect_expr_refs(&binding.body, &mut stack);
    }
    out
}

fn collectable_binding_body(binding: &Binding) -> bool {
    !binding_needs_demand_monomorphization(binding)
        || is_materialized_specialization_binding(&binding.name)
}

pub(super) fn binding_needs_demand_monomorphization(binding: &Binding) -> bool {
    !binding.type_params.is_empty()
        || hir_type_has_vars(&binding.body.ty)
        || core_type_has_vars(&binding.scheme.body)
        || binding
            .scheme
            .requirements
            .iter()
            .any(role_requirement_has_vars)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct RoleImplCollectCandidate {
    path: core_ir::Path,
    signature: DemandSignature,
}

fn generic_role_impls(module: &Module) -> HashMap<core_ir::Name, Vec<RoleImplCollectCandidate>> {
    let mut generic_role_impls: HashMap<core_ir::Name, Vec<RoleImplCollectCandidate>> =
        HashMap::new();
    for binding in &module.bindings {
        if !is_impl_method_path(&binding.name) {
            continue;
        }
        let Some(method) = binding.name.segments.last() else {
            continue;
        };
        generic_role_impls
            .entry(method.clone())
            .or_default()
            .push(RoleImplCollectCandidate {
                path: binding.name.clone(),
                signature: DemandSignature::from_runtime_type(&binding.body.ty)
                    .canonicalize_holes(),
            });
    }
    for candidates in generic_role_impls.values_mut() {
        candidates.sort_by_key(|candidate| path_key(&candidate.path));
    }
    generic_role_impls
}

fn role_impl_candidate_accepts(candidate: &DemandSignature, call: &DemandSignature) -> bool {
    let (candidate_args, _) = uncurried_collect_signatures(candidate.clone());
    if candidate_args.is_empty() {
        return true;
    }
    let (call_args, _) = uncurried_collect_signatures(call.clone());
    let Some((candidate_receiver, call_receiver)) = candidate_args.first().zip(call_args.first())
    else {
        return false;
    };
    let candidate_receiver = signature_value(candidate_receiver);
    let call_receiver = signature_value(call_receiver);
    DemandUnifier::new()
        .unify_signature(&candidate_receiver, &call_receiver)
        .is_ok()
        || DemandUnifier::new()
            .unify_signature(&call_receiver, &candidate_receiver)
            .is_ok()
}

fn role_impl_demand_signature(call: &DemandSignature) -> DemandSignature {
    let (args, ret) = uncurried_collect_signatures(call.clone());
    let args = args
        .into_iter()
        .map(|arg| signature_value(&arg))
        .collect::<Vec<_>>();
    curried_signatures(&args, ret)
}

fn uncurried_collect_signatures(
    signature: DemandSignature,
) -> (Vec<DemandSignature>, DemandSignature) {
    let mut args = Vec::new();
    let mut current = signature;
    loop {
        match current {
            DemandSignature::Fun { param, ret } => {
                args.push(*param);
                current = *ret;
            }
            ret => return (args, ret),
        }
    }
}

fn role_requirement_has_vars(requirement: &core_ir::RoleRequirement) -> bool {
    requirement.args.iter().any(|arg| match arg {
        core_ir::RoleRequirementArg::Input(bounds)
        | core_ir::RoleRequirementArg::Associated { bounds, .. } => type_bounds_have_vars(bounds),
    })
}

fn type_bounds_have_vars(bounds: &core_ir::TypeBounds) -> bool {
    bounds.lower.as_deref().is_some_and(core_type_has_vars)
        || bounds.upper.as_deref().is_some_and(core_type_has_vars)
}

pub(super) fn is_role_method_path(path: &core_ir::Path) -> bool {
    let Some(role) = path.segments.iter().rev().nth(1) else {
        return false;
    };
    role.0.chars().next().is_some_and(char::is_uppercase)
}

pub(super) fn is_impl_method_path(path: &core_ir::Path) -> bool {
    path.segments
        .iter()
        .any(|segment| segment.0.starts_with("&impl#"))
}

fn is_materialized_specialization_binding(path: &core_ir::Path) -> bool {
    let Some(name) = path.segments.last().map(|name| name.0.as_str()) else {
        return false;
    };
    generated_suffix_index(name, "__ddmono").is_some()
        || generated_suffix_index(name, "__mono").is_some()
}

fn collect_demand_call_target(path: &core_ir::Path) -> core_ir::Path {
    if (std::env::var_os("YULANG_SUBST_SPECIALIZE").is_some()
        || std::env::var_os("YULANG_PRINCIPAL_ELABORATE").is_some())
        && generated_path_has_suffix(path, "__mono")
    {
        return path.clone();
    }
    demand_call_target(path)
}

fn generated_path_has_suffix(path: &core_ir::Path, marker: &str) -> bool {
    path.segments
        .last()
        .is_some_and(|name| generated_suffix_index(&name.0, marker).is_some())
}

fn generated_suffix_index(name: &str, marker: &str) -> Option<usize> {
    let (_, suffix) = name.rsplit_once(marker)?;
    suffix
        .chars()
        .all(|ch| ch.is_ascii_digit())
        .then(|| suffix.parse().ok())
        .flatten()
}

fn path_key(path: &core_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

fn applied_call_with_head(expr: &Expr) -> Option<(&core_ir::Path, &Expr, Vec<&Expr>)> {
    let mut head = expr;
    let mut args = Vec::new();
    loop {
        match &head.kind {
            ExprKind::Apply {
                callee: next, arg, ..
            } => {
                args.push(arg.as_ref());
                head = next;
            }
            ExprKind::Var(target) => {
                args.reverse();
                return Some((target, head, args));
            }
            _ => return None,
        }
    }
}

pub(super) fn curried_call_type(args: &[&Expr], ret: RuntimeType) -> RuntimeType {
    args.iter()
        .rev()
        .fold(ret, |ret, arg| RuntimeType::fun(arg.ty.clone(), ret))
}

fn call_signatures_from_head(
    head: &Expr,
    args: &[&Expr],
    expr: &Expr,
    principal_hints: Option<(Vec<DemandSignature>, DemandSignature)>,
) -> (Vec<DemandSignature>, DemandSignature) {
    let fallback_args = args
        .iter()
        .map(|arg| expr_signature(arg))
        .collect::<Vec<_>>();
    let fallback_ret = expr_signature(expr);
    let Some((hints, ret_hint)) = principal_hints
        .filter(|(hints, _)| hints.len() == args.len())
        .or_else(|| curried_signatures_from_type(&head.ty, args.len()))
    else {
        return (fallback_args, fallback_ret);
    };
    let mut unifier = DemandUnifier::new();
    let mut failed_args = vec![false; hints.len()];
    for (index, (hint, actual)) in hints.iter().zip(&fallback_args).enumerate() {
        if unifier.unify(hint, actual).is_err() {
            failed_args[index] = true;
        }
    }
    let _ = unifier.unify(&ret_hint, &fallback_ret);
    let substitutions = unifier.finish();
    let args = hints
        .iter()
        .zip(&fallback_args)
        .zip(failed_args)
        .map(|((hint, actual), failed)| {
            let hint = substitutions.apply_signature(hint);
            if failed {
                merge_effects_from_actual(hint, actual)
            } else {
                hint
            }
        })
        .collect();
    let ret = return_effect_from_args(substitutions.apply_signature(&ret_hint), &fallback_args);
    (args, ret)
}

fn applied_call_principal_signature_hints(
    expr: &Expr,
    arity: usize,
) -> Option<(Vec<DemandSignature>, DemandSignature)> {
    let mut head = expr;
    let mut principal = None;
    loop {
        head = transparent_call_head(head);
        let ExprKind::Apply {
            callee, evidence, ..
        } = &head.kind
        else {
            break;
        };
        if let Some(signature) = evidence
            .as_ref()
            .and_then(apply_evidence_substituted_callee_signature)
        {
            principal = Some(signature);
        }
        head = callee;
    }

    let (params, ret) = uncurried_collect_signatures(principal?);
    if params.len() < arity {
        return None;
    }
    let ret = if params.len() == arity {
        ret
    } else {
        curried_signatures(&params[arity..], ret)
    };
    Some((params.into_iter().take(arity).collect(), ret))
}

fn transparent_call_head(mut expr: &Expr) -> &Expr {
    loop {
        match &expr.kind {
            ExprKind::BindHere { expr: inner }
            | ExprKind::Coerce { expr: inner, .. }
            | ExprKind::Pack { expr: inner, .. } => expr = inner,
            _ => return expr,
        }
    }
}

fn strengthen_handler_arg_signatures(
    target: &core_ir::Path,
    mut args: Vec<DemandSignature>,
    ret: &DemandSignature,
) -> Vec<DemandSignature> {
    if known_consumed_effects_for_target(target).is_empty() {
        return args;
    }
    let Some(first) = args.first_mut() else {
        return args;
    };
    let DemandSignature::Thunk {
        effect: consumed_effect,
        ..
    } = first
    else {
        return args;
    };
    let DemandSignature::Thunk {
        effect: ret_effect,
        value: ret_value,
    } = ret
    else {
        return args;
    };
    *first = DemandSignature::Thunk {
        effect: merge_demand_effects(consumed_effect.clone(), ret_effect.clone()),
        value: ret_value.clone(),
    };
    args
}

fn closed_collect_call_signature(
    target: &core_ir::Path,
    args: Vec<DemandSignature>,
    ret: DemandSignature,
    arity: usize,
) -> (Vec<DemandSignature>, DemandSignature) {
    let closed =
        close_known_associated_type_signature(target, curried_signatures(&args, ret.clone()));
    let closed = close_default_effect_holes(closed);
    let closed = close_known_associated_type_signature(target, closed);
    let (closed_args, closed_ret) = uncurried_collect_signatures(closed);
    if closed_args.len() == arity {
        return (closed_args, closed_ret);
    }
    (args, ret)
}

fn known_consumed_effects_for_target(target: &core_ir::Path) -> Vec<core_ir::Path> {
    if let Some(effect) = local_ref_run_effect_path(target) {
        return vec![effect];
    }
    if path_ends_with(target, &["std", "undet", "undet", "once"])
        || path_ends_with(target, &["std", "undet", "undet", "list"])
        || path_ends_with(target, &["std", "undet", "undet", "logic"])
    {
        return vec![path_segments(&["std", "undet", "undet"])];
    }
    if path_ends_with(target, &["std", "flow", "sub", "sub"])
        || path_ends_with(target, &["std", "sub", "sub"])
    {
        return vec![path_segments(&["std", "flow", "sub"])];
    }
    if path_ends_with(target, &["std", "fold", "Fold", "find"]) {
        return vec![path_segments(&["std", "flow", "sub"])];
    }
    if path_ends_with(target, &["std", "junction", "junction", "junction"]) {
        return vec![path_segments(&["std", "junction", "junction"])];
    }
    if path_ends_with(target, &["std", "flow", "loop", "last", "sub"]) {
        return vec![path_segments(&["std", "flow", "loop", "last"])];
    }
    if path_ends_with(target, &["std", "flow", "loop", "next", "sub"]) {
        return vec![path_segments(&["std", "flow", "loop", "next"])];
    }
    if path_ends_with(target, &["std", "flow", "loop", "redo", "judge"]) {
        return vec![path_segments(&["std", "flow", "loop", "redo"])];
    }
    if path_ends_with(target, &["std", "flow", "label_loop", "last", "sub"]) {
        return vec![path_segments(&["std", "flow", "label_loop", "last"])];
    }
    if path_ends_with(target, &["std", "flow", "label_loop", "next", "sub"]) {
        return vec![path_segments(&["std", "flow", "label_loop", "next"])];
    }
    if path_ends_with(target, &["std", "flow", "label_loop", "redo", "judge"]) {
        return vec![path_segments(&["std", "flow", "label_loop", "redo"])];
    }
    Vec::new()
}

fn local_ref_run_effect_path(target: &core_ir::Path) -> Option<core_ir::Path> {
    let [namespace, name] = target.segments.as_slice() else {
        return None;
    };
    (name.0 == "run" && namespace.0.starts_with('&')).then(|| core_ir::Path {
        segments: vec![namespace.clone()],
    })
}

fn demand_effect_is_empty(effect: &DemandEffect) -> bool {
    match effect {
        DemandEffect::Empty => true,
        DemandEffect::Row(items) => items.iter().all(demand_effect_is_empty),
        DemandEffect::Hole(_) | DemandEffect::Atom(_) => false,
    }
}

fn demand_effect_is_consumed_by(effect: &DemandEffect, consumed: &[core_ir::Path]) -> bool {
    match effect {
        DemandEffect::Empty | DemandEffect::Hole(_) => false,
        DemandEffect::Atom(ty) => demand_effect_path(ty).is_some_and(|path| {
            consumed
                .iter()
                .any(|effect| effect_paths_match(effect, path))
        }),
        DemandEffect::Row(items) => items
            .iter()
            .any(|item| demand_effect_is_consumed_by(item, consumed)),
    }
}

fn demand_effect_path(ty: &DemandCoreType) -> Option<&core_ir::Path> {
    match ty {
        DemandCoreType::Named { path, .. } => Some(path),
        _ => None,
    }
}

fn effect_paths_match(left: &core_ir::Path, right: &core_ir::Path) -> bool {
    left == right
        || left.segments.ends_with(right.segments.as_slice())
        || right.segments.ends_with(left.segments.as_slice())
}

fn thunk_effect_signature(ty: &RuntimeType) -> Option<DemandEffect> {
    match ty {
        RuntimeType::Thunk { effect, .. } => Some(DemandEffect::from_core_type(effect)),
        _ => None,
    }
}

fn path_ends_with(path: &core_ir::Path, suffix: &[&str]) -> bool {
    path.segments.len() >= suffix.len()
        && path
            .segments
            .iter()
            .rev()
            .zip(suffix.iter().rev())
            .all(|(segment, expected)| segment.0 == *expected)
}

fn path_segments(segments: &[&str]) -> core_ir::Path {
    core_ir::Path {
        segments: segments
            .iter()
            .map(|segment| core_ir::Name((*segment).to_string()))
            .collect(),
    }
}

fn curried_signatures_from_type(
    ty: &RuntimeType,
    arity: usize,
) -> Option<(Vec<DemandSignature>, DemandSignature)> {
    let mut out = Vec::with_capacity(arity);
    let mut current = DemandSignature::from_runtime_type(ty);
    for _ in 0..arity {
        match current {
            DemandSignature::Fun { param, ret } => {
                out.push(*param);
                current = *ret;
            }
            DemandSignature::Core(DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            }) => {
                out.push(effected_core_signature(*param, *param_effect));
                current = effected_core_signature(*ret, *ret_effect);
            }
            _ => return None,
        }
    }
    Some((out, current))
}

fn merge_effects_from_actual(hint: DemandSignature, actual: &DemandSignature) -> DemandSignature {
    match (hint, actual) {
        (
            DemandSignature::Fun { param, ret },
            DemandSignature::Fun {
                param: actual_param,
                ret: actual_ret,
            },
        ) => DemandSignature::Fun {
            param: Box::new(merge_effects_from_actual(*param, actual_param)),
            ret: Box::new(merge_effects_from_actual(*ret, actual_ret)),
        },
        (
            DemandSignature::Thunk { effect, value },
            DemandSignature::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
        ) => DemandSignature::Thunk {
            effect: merge_empty_effect(effect, actual_effect),
            value: Box::new(merge_effects_from_actual(*value, actual_value)),
        },
        (DemandSignature::Core(hint), actual) => {
            let actual = signature_core_value(actual);
            DemandSignature::Core(merge_core_effects_from_actual(hint, &actual))
        }
        (hint, _) => hint,
    }
}

fn merge_core_effects_from_actual(hint: DemandCoreType, actual: &DemandCoreType) -> DemandCoreType {
    match (hint, actual) {
        (
            DemandCoreType::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            },
            DemandCoreType::Fun {
                param: actual_param,
                param_effect: actual_param_effect,
                ret_effect: actual_ret_effect,
                ret: actual_ret,
            },
        ) => DemandCoreType::Fun {
            param: Box::new(merge_core_effects_from_actual(*param, actual_param)),
            param_effect: Box::new(merge_empty_effect(*param_effect, actual_param_effect)),
            ret_effect: Box::new(merge_empty_effect(*ret_effect, actual_ret_effect)),
            ret: Box::new(merge_core_effects_from_actual(*ret, actual_ret)),
        },
        (hint, _) => hint,
    }
}

fn merge_empty_effect(hint: DemandEffect, actual: &DemandEffect) -> DemandEffect {
    match (&hint, actual) {
        (DemandEffect::Empty, actual) if !matches!(actual, DemandEffect::Empty) => actual.clone(),
        _ => hint,
    }
}

fn expr_signature(expr: &Expr) -> DemandSignature {
    match &expr.kind {
        ExprKind::Lambda { body, .. } => {
            let body = expr_signature(body);
            match DemandSignature::from_runtime_type(&expr.ty) {
                DemandSignature::Fun { param, .. } => DemandSignature::Fun {
                    param,
                    ret: Box::new(body),
                },
                DemandSignature::Core(DemandCoreType::Fun {
                    param,
                    param_effect,
                    ..
                }) => {
                    let (ret, ret_effect) = signature_effected_core_value(&body);
                    DemandSignature::Core(DemandCoreType::Fun {
                        param,
                        param_effect,
                        ret_effect: Box::new(ret_effect),
                        ret: Box::new(ret),
                    })
                }
                other => other,
            }
        }
        ExprKind::Apply { callee, arg, .. } if matches!(callee.kind, ExprKind::EffectOp(_)) => {
            let ExprKind::EffectOp(path) = &callee.kind else {
                unreachable!();
            };
            let value = signature_core_value(&DemandSignature::from_runtime_type(&expr.ty));
            let payload = signature_core_value(&expr_signature(arg));
            effected_core_signature(value, effect_operation_signature(path, payload))
        }
        ExprKind::Apply {
            evidence: Some(evidence),
            ..
        } => {
            let fallback = DemandSignature::from_runtime_type(&expr.ty);
            let merged = apply_evidence_merged_signature(evidence, fallback.clone());
            match (&merged, &fallback) {
                (evidence, DemandSignature::Thunk { .. })
                    if !matches!(evidence, DemandSignature::Thunk { .. }) =>
                {
                    fallback
                }
                _ => merged,
            }
        }
        ExprKind::BindHere { expr } => signature_value(&expr_signature(expr)),
        ExprKind::LocalPushId { body: expr, .. }
        | ExprKind::AddId { thunk: expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => expr_signature(expr),
        ExprKind::Block {
            tail: Some(tail), ..
        } => expr_signature(tail),
        ExprKind::Record {
            fields,
            spread: None,
        } => DemandSignature::Core(DemandCoreType::Record(
            fields
                .iter()
                .map(|field| DemandRecordField {
                    name: field.name.clone(),
                    value: signature_core_value(&expr_signature(&field.value)),
                    optional: false,
                })
                .collect(),
        )),
        _ => DemandSignature::from_runtime_type(&expr.ty),
    }
}

fn effect_operation_signature(path: &core_ir::Path, payload: DemandCoreType) -> DemandEffect {
    let effect_path = core_ir::Path {
        segments: path
            .segments
            .iter()
            .take(path.segments.len().saturating_sub(1))
            .cloned()
            .collect(),
    };
    if effect_path.segments.is_empty() {
        return DemandEffect::Empty;
    }
    let args = if is_unit_or_hole(&payload) {
        Vec::new()
    } else {
        vec![DemandTypeArg::Type(payload)]
    };
    DemandEffect::Atom(DemandCoreType::Named {
        path: effect_path,
        args,
    })
}

fn collect_expr_refs(expr: &Expr, out: &mut Vec<core_ir::Path>) {
    match &expr.kind {
        ExprKind::Var(path) => out.push(path.clone()),
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => collect_expr_refs(body, out),
        ExprKind::Apply { callee, arg, .. } => {
            collect_expr_refs(callee, out);
            collect_expr_refs(arg, out);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_refs(cond, out);
            collect_expr_refs(then_branch, out);
            collect_expr_refs(else_branch, out);
        }
        ExprKind::Tuple(items) => {
            for item in items {
                collect_expr_refs(item, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                collect_expr_refs(&field.value, out);
            }
            collect_record_spread_refs(spread, out);
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                collect_expr_refs(value, out);
            }
        }
        ExprKind::Select { base, .. } => collect_expr_refs(base, out),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            collect_expr_refs(scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                collect_stmt_refs(stmt, out);
            }
            if let Some(tail) = tail {
                collect_expr_refs(tail, out);
            }
        }
        ExprKind::Handle { body, arms, .. } => {
            collect_expr_refs(body, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_expr_refs(guard, out);
                }
                collect_expr_refs(&arm.body, out);
            }
        }
        ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
}

fn collect_record_spread_refs(spread: &Option<RecordSpreadExpr>, out: &mut Vec<core_ir::Path>) {
    if let Some(spread) = spread {
        match spread {
            RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                collect_expr_refs(expr, out);
            }
        }
    }
}

fn collect_stmt_refs(stmt: &Stmt, out: &mut Vec<core_ir::Path>) {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            collect_expr_refs(value, out);
        }
    }
}

fn is_unit_or_hole(ty: &DemandCoreType) -> bool {
    match ty {
        DemandCoreType::Hole(_) => true,
        DemandCoreType::Named { path, args } => {
            path.segments.len() == 1 && path.segments[0].0 == "unit" && args.is_empty()
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Binding, Expr, Root, TypeInstantiation};

    #[test]
    fn collector_enqueues_direct_generic_call_demand() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![generic_binding(id.clone())],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(id.clone()),
                        RuntimeType::fun(
                            RuntimeType::core(core_ir::Type::Any),
                            RuntimeType::core(core_ir::Type::Any),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None::<TypeInstantiation>,
                },
                RuntimeType::core(named("int")),
            )],
            roots: vec![Root::Expr(0)],
        };

        let mut collector = DemandCollector::from_module(&module);
        collector.collect_module(&module);
        let mut queue = collector.into_queue();
        let demand = queue.pop_front().expect("direct call demand");

        assert_eq!(demand.target, id);
        assert_eq!(
            demand.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(DemandCoreType::Named {
                    path: path("int"),
                    args: Vec::new(),
                })),
                ret: Box::new(DemandSignature::Core(DemandCoreType::Named {
                    path: path("int"),
                    args: Vec::new(),
                })),
            }
        );
        assert!(queue.is_empty());
    }

    #[test]
    fn collector_enqueues_legacy_mono_call_to_generic_demand() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![generic_binding(id.clone())],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(path("id__mono3")),
                        RuntimeType::fun(
                            RuntimeType::core(named("int")),
                            RuntimeType::core(named("int")),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None::<TypeInstantiation>,
                },
                RuntimeType::core(named("int")),
            )],
            roots: vec![Root::Expr(0)],
        };

        let mut collector = DemandCollector::from_module(&module);
        collector.collect_module(&module);
        let mut queue = collector.into_queue();
        let demand = queue.pop_front().expect("legacy mono call demand");

        assert_eq!(demand.target, id);
        assert_eq!(
            demand.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
        assert!(queue.is_empty());
    }

    #[test]
    fn collector_scans_materialized_legacy_body_even_when_type_is_open() {
        let id = path("id");
        let use_id = path("use_id__mono3");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                generic_binding(id.clone()),
                Binding {
                    name: use_id,
                    type_params: vec![core_ir::TypeVar("b".to_string())],
                    scheme: core_ir::Scheme {
                        requirements: Vec::new(),
                        body: core_ir::Type::Any,
                    },
                    body: Expr::typed(
                        ExprKind::Apply {
                            callee: Box::new(Expr::typed(
                                ExprKind::Var(path("id__ddmono9")),
                                RuntimeType::fun(
                                    RuntimeType::core(named("int")),
                                    RuntimeType::core(named("int")),
                                ),
                            )),
                            arg: Box::new(Expr::typed(
                                ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                                RuntimeType::core(named("int")),
                            )),
                            evidence: None,
                            instantiation: None::<TypeInstantiation>,
                        },
                        RuntimeType::core(named("int")),
                    ),
                },
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(path("use_id__mono3"))],
        };

        let mut collector = DemandCollector::from_module(&module);
        collector.collect_module(&module);
        let mut queue = collector.into_queue();
        let demand = queue.pop_front().expect("materialized legacy body demand");

        assert_eq!(demand.target, id);
        assert_eq!(
            demand.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
        assert!(queue.is_empty());
    }

    #[test]
    fn collector_ignores_unreachable_materialized_legacy_body() {
        let id = path("id");
        let use_id = path("use_id__mono3");
        let main = path("main");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                generic_binding(id.clone()),
                Binding {
                    name: use_id,
                    type_params: vec![core_ir::TypeVar("b".to_string())],
                    scheme: core_ir::Scheme {
                        requirements: Vec::new(),
                        body: core_ir::Type::Any,
                    },
                    body: Expr::typed(
                        ExprKind::Apply {
                            callee: Box::new(Expr::typed(
                                ExprKind::Var(path("id__ddmono9")),
                                RuntimeType::fun(
                                    RuntimeType::core(named("int")),
                                    RuntimeType::core(named("int")),
                                ),
                            )),
                            arg: Box::new(Expr::typed(
                                ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                                RuntimeType::core(named("int")),
                            )),
                            evidence: None,
                            instantiation: None::<TypeInstantiation>,
                        },
                        RuntimeType::core(named("int")),
                    ),
                },
                monomorphic_binding(main.clone()),
            ],
            root_exprs: Vec::new(),
            roots: vec![Root::Binding(main)],
        };

        let mut collector = DemandCollector::from_module(&module);
        collector.collect_module(&module);

        assert!(collector.queue().is_empty());
    }

    #[test]
    fn collector_ignores_monomorphic_direct_call() {
        let f = path("f");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![monomorphic_binding(f.clone())],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(f),
                        RuntimeType::fun(
                            RuntimeType::core(named("int")),
                            RuntimeType::core(named("int")),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None::<TypeInstantiation>,
                },
                RuntimeType::core(named("int")),
            )],
            roots: vec![Root::Expr(0)],
        };

        let mut collector = DemandCollector::from_module(&module);
        collector.collect_module(&module);

        assert!(collector.queue().is_empty());
    }

    #[test]
    fn collector_enqueues_curried_generic_call_as_one_demand() {
        let f = path("f");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![generic_binding(f.clone())],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Apply {
                            callee: Box::new(Expr::typed(
                                ExprKind::Var(f.clone()),
                                RuntimeType::fun(
                                    RuntimeType::core(core_ir::Type::Any),
                                    RuntimeType::fun(
                                        RuntimeType::core(core_ir::Type::Any),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                ),
                            )),
                            arg: Box::new(Expr::typed(
                                ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                                RuntimeType::core(named("int")),
                            )),
                            evidence: None,
                            instantiation: None::<TypeInstantiation>,
                        },
                        RuntimeType::fun(
                            RuntimeType::core(core_ir::Type::Any),
                            RuntimeType::core(core_ir::Type::Any),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::String("x".to_string())),
                        RuntimeType::core(named("str")),
                    )),
                    evidence: None,
                    instantiation: None::<TypeInstantiation>,
                },
                RuntimeType::core(named("bool")),
            )],
            roots: vec![Root::Expr(0)],
        };

        let mut collector = DemandCollector::from_module(&module);
        collector.collect_module(&module);
        let mut queue = collector.into_queue();
        let demand = queue.pop_front().expect("curried call demand");

        assert_eq!(demand.target, f);
        assert_eq!(
            demand.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Fun {
                    param: Box::new(DemandSignature::Core(named_demand("str"))),
                    ret: Box::new(DemandSignature::Core(named_demand("bool"))),
                }),
            }
        );
        assert!(queue.is_empty());
    }

    #[test]
    fn collector_enqueues_generic_role_impl_candidates() {
        let role_add = path_segments(&["std", "prelude", "Add", "add"]);
        let impl_add = path_segments(&["std", "prelude", "&impl#1", "add"]);
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![generic_binding(impl_add.clone())],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(role_add),
                        RuntimeType::fun(
                            RuntimeType::core(named("int")),
                            RuntimeType::core(named("int")),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None::<TypeInstantiation>,
                },
                RuntimeType::core(named("int")),
            )],
            roots: vec![Root::Expr(0)],
        };

        let mut collector = DemandCollector::from_module(&module);
        collector.collect_module(&module);
        let mut queue = collector.into_queue();
        let demand = queue.pop_front().expect("role impl demand");

        assert_eq!(demand.target, impl_add);
        assert_eq!(
            demand.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("int"))),
                ret: Box::new(DemandSignature::Core(named_demand("int"))),
            }
        );
        assert!(queue.is_empty());
    }

    #[test]
    fn collector_keeps_runtime_thunk_when_apply_evidence_is_value_only() {
        let f = path("f");
        let io = named("io");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![generic_binding(f.clone())],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(f.clone()),
                        RuntimeType::fun(
                            RuntimeType::core(core_ir::Type::Any),
                            RuntimeType::core(core_ir::Type::Any),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Unit),
                        RuntimeType::core(named("unit")),
                    )),
                    evidence: Some(core_ir::ApplyEvidence {
                        callee_source_edge: None,
                        expected_callee: None,
                        arg_source_edge: None,
                        callee: core_ir::TypeBounds::exact(core_ir::Type::Fun {
                            param: Box::new(named("unit")),
                            param_effect: Box::new(core_ir::Type::Never),
                            ret_effect: Box::new(core_ir::Type::Never),
                            ret: Box::new(named("int")),
                        }),
                        arg: core_ir::TypeBounds::exact(named("unit")),
                        expected_arg: None,
                        result: core_ir::TypeBounds::exact(named("int")),
                        principal_callee: None,
                        substitutions: Vec::new(),
                        substitution_candidates: Vec::new(),
                        role_method: false,
                        principal_elaboration: None,
                    }),
                    instantiation: None::<TypeInstantiation>,
                },
                RuntimeType::thunk(io, RuntimeType::core(named("int"))),
            )],
            roots: vec![Root::Expr(0)],
        };

        let mut collector = DemandCollector::from_module(&module);
        collector.collect_module(&module);
        let mut queue = collector.into_queue();
        let demand = queue.pop_front().expect("direct call demand");

        assert_eq!(
            demand.key.signature,
            DemandSignature::Fun {
                param: Box::new(DemandSignature::Core(named_demand("unit"))),
                ret: Box::new(DemandSignature::Thunk {
                    effect: DemandEffect::Atom(named_demand("io")),
                    value: Box::new(DemandSignature::Core(named_demand("int"))),
                }),
            }
        );
    }

    fn generic_binding(name: core_ir::Path) -> Binding {
        Binding {
            name,
            type_params: vec![core_ir::TypeVar("a".to_string())],
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: core_ir::Type::Any,
            },
            body: Expr::typed(
                ExprKind::Lit(core_ir::Lit::Unit),
                RuntimeType::core(named("unit")),
            ),
        }
    }

    fn monomorphic_binding(name: core_ir::Path) -> Binding {
        Binding {
            name,
            type_params: Vec::new(),
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: named("int"),
            },
            body: Expr::typed(
                ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                RuntimeType::core(named("int")),
            ),
        }
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn named_demand(name: &str) -> DemandCoreType {
        DemandCoreType::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }

    fn path_segments(segments: &[&str]) -> core_ir::Path {
        core_ir::Path {
            segments: segments
                .iter()
                .map(|segment| core_ir::Name((*segment).to_string()))
                .collect(),
        }
    }
}
