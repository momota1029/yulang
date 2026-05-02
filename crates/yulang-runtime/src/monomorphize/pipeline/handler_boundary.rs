use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct HandlerBindingInfo {
    pub(super) consumes: Vec<core_ir::Path>,
    pub(super) residual_before_known: bool,
    pub(super) residual_after_known: bool,
    pub(super) pure: bool,
}

pub(super) fn handler_binding_info(binding: &Binding) -> Option<HandlerBindingInfo> {
    expr_handler_info(&binding.body)
}

fn expr_handler_info(expr: &Expr) -> Option<HandlerBindingInfo> {
    match &expr.kind {
        ExprKind::Handle {
            body,
            arms,
            handler,
            ..
        } => Some(HandlerBindingInfo {
            consumes: handler.consumes.clone(),
            residual_before_known: handler.residual_before.is_some(),
            residual_after_known: handler.residual_after.is_some(),
            pure: handler.residual_after.as_ref().is_some_and(effect_is_empty),
        })
        .or_else(|| expr_handler_info(body))
        .or_else(|| arms.iter().find_map(handle_arm_handler_info)),
        ExprKind::Apply { callee, arg, .. } => {
            expr_handler_info(callee).or_else(|| expr_handler_info(arg))
        }
        ExprKind::Lambda { body, .. }
        | ExprKind::BindHere { expr: body }
        | ExprKind::Thunk { expr: body, .. }
        | ExprKind::LocalPushId { body, .. }
        | ExprKind::AddId { thunk: body, .. }
        | ExprKind::Coerce { expr: body, .. }
        | ExprKind::Pack { expr: body, .. } => expr_handler_info(body),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => expr_handler_info(cond)
            .or_else(|| expr_handler_info(then_branch))
            .or_else(|| expr_handler_info(else_branch)),
        ExprKind::Tuple(items) => items.iter().find_map(expr_handler_info),
        ExprKind::Record { fields, spread } => fields
            .iter()
            .find_map(|field| expr_handler_info(&field.value))
            .or_else(|| {
                spread.as_ref().and_then(|spread| match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        expr_handler_info(expr)
                    }
                })
            }),
        ExprKind::Variant { value, .. } => {
            value.as_ref().and_then(|value| expr_handler_info(value))
        }
        ExprKind::Select { base, .. } => expr_handler_info(base),
        ExprKind::Match {
            scrutinee, arms, ..
        } => expr_handler_info(scrutinee).or_else(|| arms.iter().find_map(match_arm_handler_info)),
        ExprKind::Block { stmts, tail } => stmts
            .iter()
            .find_map(stmt_handler_info)
            .or_else(|| tail.as_ref().and_then(|tail| expr_handler_info(tail))),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => None,
    }
}

fn handle_arm_handler_info(arm: &HandleArm) -> Option<HandlerBindingInfo> {
    arm.guard
        .as_ref()
        .and_then(expr_handler_info)
        .or_else(|| expr_handler_info(&arm.body))
}

fn match_arm_handler_info(arm: &MatchArm) -> Option<HandlerBindingInfo> {
    arm.guard
        .as_ref()
        .and_then(expr_handler_info)
        .or_else(|| expr_handler_info(&arm.body))
}

fn stmt_handler_info(stmt: &Stmt) -> Option<HandlerBindingInfo> {
    match stmt {
        Stmt::Let { value, .. } | Stmt::Expr(value) | Stmt::Module { body: value, .. } => {
            expr_handler_info(value)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handler_binding_detection_is_structural() {
        let mut binding = test_binding(fun(named("unit"), named("unit")));

        assert!(handler_binding_info(&binding).is_none());

        binding.body = Expr::typed(
            ExprKind::Lambda {
                param: core_ir::Name("x".to_string()),
                param_effect_annotation: None,
                param_function_allowed_effects: None,
                body: Box::new(Expr::typed(
                    ExprKind::Handle {
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(named("unit")),
                        )),
                        arms: vec![HandleArm {
                            effect: path_segments(&["std", "effect"]),
                            payload: Pattern::Wildcard {
                                ty: RuntimeType::core(named("unit")),
                            },
                            resume: None,
                            guard: None,
                            body: Expr::typed(
                                ExprKind::Lit(core_ir::Lit::Unit),
                                RuntimeType::core(named("unit")),
                            ),
                        }],
                        evidence: crate::ir::JoinEvidence {
                            result: named("unit"),
                        },
                        handler: crate::ir::HandleEffect {
                            consumes: Vec::new(),
                            residual_before: None,
                            residual_after: None,
                        },
                    },
                    RuntimeType::core(named("unit")),
                )),
            },
            RuntimeType::fun(
                RuntimeType::core(named("unit")),
                RuntimeType::core(named("unit")),
            ),
        );

        let info = handler_binding_info(&binding).expect("handler info");
        assert_eq!(info.consumes, Vec::<core_ir::Path>::new());
        assert!(!info.residual_before_known);
        assert!(!info.residual_after_known);
        assert!(!info.pure);
    }

    fn test_binding(scheme_body: core_ir::Type) -> Binding {
        Binding {
            name: path_segments(&["std", "prelude", "&impl#0", "method"]),
            type_params: Vec::new(),
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: scheme_body.clone(),
            },
            body: Expr::typed(ExprKind::Var(path("body")), RuntimeType::core(scheme_body)),
        }
    }

    fn fun(param: core_ir::Type, ret: core_ir::Type) -> core_ir::Type {
        core_ir::Type::Fun {
            param: Box::new(param),
            param_effect: Box::new(core_ir::Type::Never),
            ret_effect: Box::new(core_ir::Type::Never),
            ret: Box::new(ret),
        }
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
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
