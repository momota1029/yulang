use std::collections::HashSet;

use super::*;
use crate::ir::{Expr, ExprKind, Module, Stmt};

#[derive(Debug, Clone)]
pub struct DemandCollector {
    generic_bindings: HashSet<core_ir::Path>,
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
        Self {
            generic_bindings,
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
                if let Some((target, args)) = applied_call(expr)
                    && self.generic_bindings.contains(target)
                {
                    let expected = curried_call_type(&args, expr.ty.clone());
                    let ret = expr_signature(expr);
                    let arg_signatures = args
                        .iter()
                        .map(|arg| expr_signature(arg))
                        .collect::<Vec<_>>();
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

pub(super) fn applied_call(expr: &Expr) -> Option<(&core_ir::Path, Vec<&Expr>)> {
    let mut callee = expr;
    let mut args = Vec::new();
    loop {
        match &callee.kind {
            ExprKind::Apply {
                callee: next, arg, ..
            } => {
                args.push(arg.as_ref());
                callee = next;
            }
            ExprKind::Var(target) => {
                args.reverse();
                return Some((target, args));
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
        } => apply_evidence_signature(evidence)
            .unwrap_or_else(|| DemandSignature::from_runtime_type(&expr.ty)),
        ExprKind::BindHere { expr }
        | ExprKind::LocalPushId { body: expr, .. }
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

fn apply_evidence_signature(evidence: &core_ir::ApplyEvidence) -> Option<DemandSignature> {
    if let Some(core_ir::Type::Fun {
        ret_effect, ret, ..
    }) = bounds_type(&evidence.callee)
    {
        let mut next_hole = 0;
        let ret = DemandSignature::from_runtime_type_with_holes(
            &RuntimeType::core(ret.as_ref().clone()),
            &mut next_hole,
        );
        let ret_effect = DemandEffect::from_core_type_with_holes(ret_effect, &mut next_hole);
        return Some(effected_core_signature(
            signature_core_value(&ret),
            ret_effect,
        ));
    }
    bounds_type(&evidence.result)
        .map(|ty| DemandSignature::from_runtime_type(&RuntimeType::core(ty.clone())))
}

fn bounds_type(bounds: &core_ir::TypeBounds) -> Option<&core_ir::Type> {
    bounds.lower.as_deref().or(bounds.upper.as_deref())
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
}
