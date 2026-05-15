use std::collections::{HashMap, HashSet};
use std::fmt;

use yulang_runtime as runtime;
use yulang_typed_ir as typed_ir;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeBackendPlan {
    pub roots: Vec<NativeRootBackend>,
}

impl NativeBackendPlan {
    pub fn module_backend(&self) -> NativeBackendSelection {
        self.roots
            .iter()
            .find_map(|root| match &root.selection {
                NativeBackendSelection::CpsMainline { reason } => {
                    Some(NativeBackendSelection::CpsMainline {
                        reason: reason.clone(),
                    })
                }
                NativeBackendSelection::ValueFastPath => None,
                NativeBackendSelection::Unsupported { reason } => {
                    Some(NativeBackendSelection::Unsupported {
                        reason: reason.clone(),
                    })
                }
            })
            .unwrap_or(NativeBackendSelection::ValueFastPath)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeRootBackend {
    pub root: NativeRootLabel,
    pub selection: NativeBackendSelection,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeRootLabel {
    Binding(typed_ir::Path),
    Expr(usize),
}

impl fmt::Display for NativeRootLabel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NativeRootLabel::Binding(path) => write!(f, "binding {:?}", path),
            NativeRootLabel::Expr(index) => write!(f, "root expr {index}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NativeBackendSelection {
    ValueFastPath,
    CpsMainline { reason: NativeBackendReason },
    Unsupported { reason: NativeBackendReason },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeBackendReason {
    pub root: NativeRootLabel,
    pub kind: NativeBackendReasonKind,
}

impl fmt::Display for NativeBackendReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} contains {}", self.root, self.kind)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NativeBackendReasonKind {
    EffectOperation,
    Handler,
    Thunk,
    ThunkBoundary,
    ClosureValue,
    EffectIdScope,
    EffectIdRead,
}

impl fmt::Display for NativeBackendReasonKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            NativeBackendReasonKind::EffectOperation => "effect operation",
            NativeBackendReasonKind::Handler => "effect handler",
            NativeBackendReasonKind::Thunk => "thunk",
            NativeBackendReasonKind::ThunkBoundary => "thunk boundary",
            NativeBackendReasonKind::ClosureValue => "closure value",
            NativeBackendReasonKind::EffectIdScope => "effect id scope",
            NativeBackendReasonKind::EffectIdRead => "effect id read",
        };
        f.write_str(text)
    }
}

pub fn select_native_backends(module: &runtime::Module) -> NativeBackendPlan {
    let bindings = module
        .bindings
        .iter()
        .map(|binding| (binding.name.clone(), &binding.body))
        .collect::<HashMap<_, _>>();
    let roots = module
        .roots
        .iter()
        .map(|root| {
            let label = root_label(root);
            let reason = match root {
                runtime::Root::Binding(path) => bindings
                    .get(path)
                    .and_then(|body| first_cps_reason(body, &bindings)),
                runtime::Root::Expr(index) => module
                    .root_exprs
                    .get(*index)
                    .and_then(|expr| first_cps_reason(expr, &bindings)),
            };
            NativeRootBackend {
                root: label.clone(),
                selection: reason
                    .map(|kind| NativeBackendSelection::CpsMainline {
                        reason: NativeBackendReason { root: label, kind },
                    })
                    .unwrap_or(NativeBackendSelection::ValueFastPath),
            }
        })
        .collect();
    NativeBackendPlan { roots }
}

fn root_label(root: &runtime::Root) -> NativeRootLabel {
    match root {
        runtime::Root::Binding(path) => NativeRootLabel::Binding(path.clone()),
        runtime::Root::Expr(index) => NativeRootLabel::Expr(*index),
    }
}

fn first_cps_reason(
    root: &runtime::Expr,
    bindings: &HashMap<typed_ir::Path, &runtime::Expr>,
) -> Option<NativeBackendReasonKind> {
    let mut seen_bindings = HashSet::new();
    first_cps_reason_expr(root, bindings, &mut seen_bindings)
}

fn first_cps_reason_expr(
    expr: &runtime::Expr,
    bindings: &HashMap<typed_ir::Path, &runtime::Expr>,
    seen_bindings: &mut HashSet<typed_ir::Path>,
) -> Option<NativeBackendReasonKind> {
    match &expr.kind {
        runtime::ExprKind::EffectOp(_) => Some(NativeBackendReasonKind::EffectOperation),
        runtime::ExprKind::Handle { .. } => Some(NativeBackendReasonKind::Handler),
        runtime::ExprKind::Thunk { .. } => Some(NativeBackendReasonKind::Thunk),
        runtime::ExprKind::BindHere { .. } | runtime::ExprKind::AddId { .. } => {
            Some(NativeBackendReasonKind::ThunkBoundary)
        }
        runtime::ExprKind::LocalPushId { .. } => Some(NativeBackendReasonKind::EffectIdScope),
        runtime::ExprKind::PeekId | runtime::ExprKind::FindId { .. } => {
            Some(NativeBackendReasonKind::EffectIdRead)
        }
        runtime::ExprKind::Var(path) => {
            if seen_bindings.insert(path.clone()) {
                let reason = bindings
                    .get(path)
                    .and_then(|body| first_cps_reason_expr(body, bindings, seen_bindings));
                seen_bindings.remove(path);
                reason
            } else {
                None
            }
        }
        runtime::ExprKind::PrimitiveOp(_) | runtime::ExprKind::Lit(_) => None,
        runtime::ExprKind::Lambda { .. } => Some(NativeBackendReasonKind::ClosureValue),
        runtime::ExprKind::Apply { callee, arg, .. } => {
            first_cps_reason_expr(callee, bindings, seen_bindings)
                .or_else(|| first_cps_reason_expr(arg, bindings, seen_bindings))
        }
        runtime::ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => first_cps_reason_expr(cond, bindings, seen_bindings)
            .or_else(|| first_cps_reason_expr(then_branch, bindings, seen_bindings))
            .or_else(|| first_cps_reason_expr(else_branch, bindings, seen_bindings)),
        runtime::ExprKind::Tuple(items) => items
            .iter()
            .find_map(|item| first_cps_reason_expr(item, bindings, seen_bindings)),
        runtime::ExprKind::Record { fields, spread } => fields
            .iter()
            .find_map(|field| first_cps_reason_expr(&field.value, bindings, seen_bindings))
            .or_else(|| match spread {
                Some(runtime::RecordSpreadExpr::Head(expr))
                | Some(runtime::RecordSpreadExpr::Tail(expr)) => {
                    first_cps_reason_expr(expr, bindings, seen_bindings)
                }
                None => None,
            }),
        runtime::ExprKind::Variant { value, .. } => value
            .as_deref()
            .and_then(|value| first_cps_reason_expr(value, bindings, seen_bindings)),
        runtime::ExprKind::Select { base, .. } => {
            first_cps_reason_expr(base, bindings, seen_bindings)
        }
        runtime::ExprKind::Match {
            scrutinee, arms, ..
        } => first_cps_reason_expr(scrutinee, bindings, seen_bindings).or_else(|| {
            arms.iter().find_map(|arm| {
                arm.guard
                    .as_ref()
                    .and_then(|guard| first_cps_reason_expr(guard, bindings, seen_bindings))
                    .or_else(|| first_cps_reason_expr(&arm.body, bindings, seen_bindings))
            })
        }),
        runtime::ExprKind::Block { stmts, tail } => stmts
            .iter()
            .find_map(|stmt| match stmt {
                runtime::Stmt::Let { value, .. } | runtime::Stmt::Expr(value) => {
                    first_cps_reason_expr(value, bindings, seen_bindings)
                }
                runtime::Stmt::Module { body, .. } => {
                    first_cps_reason_expr(body, bindings, seen_bindings)
                }
            })
            .or_else(|| {
                tail.as_deref()
                    .and_then(|tail| first_cps_reason_expr(tail, bindings, seen_bindings))
            }),
        runtime::ExprKind::Coerce { expr, .. } | runtime::ExprKind::Pack { expr, .. } => {
            first_cps_reason_expr(expr, bindings, seen_bindings)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module_with_root(expr: runtime::Expr) -> runtime::Module {
        runtime::Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![expr],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    fn module_with_binding(
        name: &str,
        body: runtime::Expr,
        root: runtime::Expr,
    ) -> runtime::Module {
        runtime::Module {
            path: typed_ir::Path::default(),
            bindings: vec![runtime::Binding {
                name: path(name),
                type_params: Vec::new(),
                scheme: typed_ir::Scheme {
                    requirements: Vec::new(),
                    body: typed_ir::Type::Unknown,
                },
                body,
            }],
            root_exprs: vec![root],
            roots: vec![runtime::Root::Expr(0)],
            role_impls: Vec::new(),
        }
    }

    fn path(name: &str) -> typed_ir::Path {
        typed_ir::Path::from_name(typed_ir::Name(name.to_string()))
    }

    fn lit_int(value: &str) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Lit(typed_ir::Lit::Int(value.to_string())),
            runtime::Type::unknown(),
        )
    }

    fn var(name: &str) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::Var(path(name)), runtime::Type::unknown())
    }

    fn primitive(op: typed_ir::PrimitiveOp) -> runtime::Expr {
        runtime::Expr::typed(runtime::ExprKind::PrimitiveOp(op), runtime::Type::unknown())
    }

    fn apply(callee: runtime::Expr, arg: runtime::Expr) -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(arg),
                evidence: None,
                instantiation: None,
            },
            runtime::Type::unknown(),
        )
    }

    fn identity_lambda() -> runtime::Expr {
        runtime::Expr::typed(
            runtime::ExprKind::Lambda {
                param: typed_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(var("x")),
            },
            runtime::Type::unknown(),
        )
    }

    #[test]
    fn selects_value_fast_path_for_pure_root() {
        let plan = select_native_backends(&module_with_root(lit_int("42")));

        assert_eq!(plan.module_backend(), NativeBackendSelection::ValueFastPath);
    }

    #[test]
    fn selects_cps_mainline_for_effect_operation_root() {
        let expr = runtime::Expr::typed(
            runtime::ExprKind::EffectOp(path("yield")),
            runtime::Type::unknown(),
        );
        let plan = select_native_backends(&module_with_root(expr));

        assert_eq!(
            plan.module_backend(),
            NativeBackendSelection::CpsMainline {
                reason: NativeBackendReason {
                    root: NativeRootLabel::Expr(0),
                    kind: NativeBackendReasonKind::EffectOperation,
                },
            }
        );
    }

    #[test]
    fn follows_reachable_binding_when_selecting_backend() {
        let body = runtime::Expr::typed(
            runtime::ExprKind::Handle {
                body: Box::new(lit_int("1")),
                arms: Vec::new(),
                evidence: runtime::JoinEvidence {
                    result: typed_ir::Type::Unknown,
                },
                handler: runtime::HandleEffect {
                    consumes: Vec::new(),
                    residual_before: None,
                    residual_after: None,
                },
            },
            runtime::Type::unknown(),
        );
        let plan = select_native_backends(&module_with_binding("run", body, var("run")));

        assert_eq!(
            plan.module_backend(),
            NativeBackendSelection::CpsMainline {
                reason: NativeBackendReason {
                    root: NativeRootLabel::Expr(0),
                    kind: NativeBackendReasonKind::Handler,
                },
            }
        );
    }

    #[test]
    fn selects_cps_mainline_for_closure_value_root() {
        let expr = identity_lambda();
        let plan = select_native_backends(&module_with_root(expr));

        assert_eq!(
            plan.module_backend(),
            NativeBackendSelection::CpsMainline {
                reason: NativeBackendReason {
                    root: NativeRootLabel::Expr(0),
                    kind: NativeBackendReasonKind::ClosureValue,
                },
            }
        );
    }

    #[test]
    fn selects_cps_mainline_for_closure_value_inside_record() {
        let expr = runtime::Expr::typed(
            runtime::ExprKind::Record {
                fields: vec![runtime::RecordExprField {
                    name: typed_ir::Name("f".to_string()),
                    value: identity_lambda(),
                }],
                spread: None,
            },
            runtime::Type::unknown(),
        );
        let plan = select_native_backends(&module_with_root(expr));

        assert_eq!(
            plan.module_backend(),
            NativeBackendSelection::CpsMainline {
                reason: NativeBackendReason {
                    root: NativeRootLabel::Expr(0),
                    kind: NativeBackendReasonKind::ClosureValue,
                },
            }
        );
    }

    #[test]
    fn selects_cps_mainline_for_closure_value_inside_list_primitive() {
        let expr = apply(
            primitive(typed_ir::PrimitiveOp::ListSingleton),
            identity_lambda(),
        );
        let plan = select_native_backends(&module_with_root(expr));

        assert_eq!(
            plan.module_backend(),
            NativeBackendSelection::CpsMainline {
                reason: NativeBackendReason {
                    root: NativeRootLabel::Expr(0),
                    kind: NativeBackendReasonKind::ClosureValue,
                },
            }
        );
    }
}
