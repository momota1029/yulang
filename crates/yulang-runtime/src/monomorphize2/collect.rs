use std::collections::{HashMap, HashSet};

use super::*;
use crate::ir::{Expr, ExprKind, Module, Stmt};

#[derive(Debug, Clone)]
pub struct DemandCollector {
    generic_bindings: HashSet<core_ir::Path>,
    generic_role_impls: HashMap<core_ir::Name, Vec<core_ir::Path>>,
    queue: DemandQueue,
}

impl DemandCollector {
    pub fn from_module(module: &Module) -> Self {
        let generic_bindings = module
            .bindings
            .iter()
            .filter(|binding| !binding.type_params.is_empty())
            .map(|binding| binding.name.clone())
            .collect();
        let mut generic_role_impls: HashMap<core_ir::Name, Vec<core_ir::Path>> = HashMap::new();
        for binding in &module.bindings {
            if binding.type_params.is_empty() || !is_impl_method_path(&binding.name) {
                continue;
            }
            let Some(method) = binding.name.segments.last() else {
                continue;
            };
            generic_role_impls
                .entry(method.clone())
                .or_default()
                .push(binding.name.clone());
        }
        for candidates in generic_role_impls.values_mut() {
            candidates.sort_by_key(path_key);
        }
        Self {
            generic_bindings,
            generic_role_impls,
            queue: DemandQueue::default(),
        }
    }

    pub fn collect_module(&mut self, module: &Module) {
        for expr in &module.root_exprs {
            self.collect_expr(expr);
        }
        for binding in &module.bindings {
            if binding.type_params.is_empty() {
                self.collect_expr(&binding.body);
            }
        }
    }

    pub fn queue(&self) -> &DemandQueue {
        &self.queue
    }

    pub fn into_queue(self) -> DemandQueue {
        self.queue
    }

    fn collect_expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Apply {
                callee,
                arg,
                evidence: _,
                instantiation: _,
            } => {
                if let Some((target, head, args)) = applied_call_with_head(expr)
                    && self.generic_bindings.contains(target)
                {
                    let expected = curried_call_type(&args, expr.ty.clone());
                    let (arg_signatures, ret) = call_signatures_from_head(head, &args, expr);
                    self.queue.push_signature(
                        target.clone(),
                        expected,
                        curried_signatures(&arg_signatures, ret),
                    );
                    for arg in args {
                        self.collect_expr(arg);
                    }
                    return;
                }
                if let Some((target, head, args)) = applied_call_with_head(expr)
                    && is_role_method_path(target)
                    && let Some(method) = target.segments.last()
                    && let Some(candidates) = self.generic_role_impls.get(method)
                {
                    let expected = curried_call_type(&args, expr.ty.clone());
                    let (arg_signatures, ret) = call_signatures_from_head(head, &args, expr);
                    let signature = curried_signatures(&arg_signatures, ret);
                    for candidate in candidates {
                        self.queue.push_signature(
                            candidate.clone(),
                            expected.clone(),
                            signature.clone(),
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
            | ExprKind::BindHere { expr: body }
            | ExprKind::Thunk { expr: body, .. }
            | ExprKind::LocalPushId { body, .. }
            | ExprKind::AddId { thunk: body, .. }
            | ExprKind::Coerce { expr: body, .. }
            | ExprKind::Pack { expr: body, .. } => self.collect_expr(body),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_expr(cond);
                self.collect_expr(then_branch);
                self.collect_expr(else_branch);
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
                    self.collect_expr(tail);
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
) -> (Vec<DemandSignature>, DemandSignature) {
    let fallback_args = args
        .iter()
        .map(|arg| expr_signature(arg))
        .collect::<Vec<_>>();
    let fallback_ret = expr_signature(expr);
    let Some((hints, ret_hint)) = curried_signatures_from_type(&head.ty, args.len()) else {
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

fn return_effect_from_args(ret: DemandSignature, args: &[DemandSignature]) -> DemandSignature {
    args.iter()
        .rev()
        .find_map(|arg| effectful_return_matching_value(arg, &ret))
        .unwrap_or(ret)
}

fn effectful_return_matching_value(
    signature: &DemandSignature,
    value: &DemandSignature,
) -> Option<DemandSignature> {
    match signature {
        DemandSignature::Fun { ret, .. } => effectful_return_matching_value(ret, value),
        DemandSignature::Thunk {
            effect,
            value: thunk_value,
        } if DemandUnifier::new()
            .unify_signature(value, thunk_value)
            .is_ok() =>
        {
            Some(DemandSignature::Thunk {
                effect: effect.clone(),
                value: thunk_value.clone(),
            })
        }
        DemandSignature::Core(DemandCoreType::Fun {
            ret_effect, ret, ..
        }) if !matches!(ret_effect.as_ref(), DemandEffect::Empty)
            && DemandUnifier::new()
                .unify_signature(value, &DemandSignature::Core(ret.as_ref().clone()))
                .is_ok() =>
        {
            Some(DemandSignature::Thunk {
                effect: ret_effect.as_ref().clone(),
                value: Box::new(DemandSignature::Core(ret.as_ref().clone())),
            })
        }
        _ => None,
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
                        callee: core_ir::TypeBounds::exact(core_ir::Type::Fun {
                            param: Box::new(named("unit")),
                            param_effect: Box::new(core_ir::Type::Never),
                            ret_effect: Box::new(core_ir::Type::Never),
                            ret: Box::new(named("int")),
                        }),
                        arg: core_ir::TypeBounds::exact(named("unit")),
                        result: core_ir::TypeBounds::exact(named("int")),
                        role_method: false,
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
