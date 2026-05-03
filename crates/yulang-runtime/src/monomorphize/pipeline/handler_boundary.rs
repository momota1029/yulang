use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct HandlerBindingInfo {
    pub(super) consumes: Vec<core_ir::Path>,
    pub(super) principal_input_effect: Option<core_ir::Type>,
    pub(super) principal_output_effect: Option<core_ir::Type>,
    pub(super) residual_before_known: bool,
    pub(super) residual_after_known: bool,
    pub(super) pure: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct HandlerCallBoundary {
    pub(super) consumes: Vec<core_ir::Path>,
    pub(super) input_effect: Option<core_ir::Type>,
    pub(super) output_effect: Option<core_ir::Type>,
    pub(super) consumes_input_effect: bool,
    pub(super) preserves_output_effect: bool,
    pub(super) pure: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct HandlerAdapterPlan {
    pub(super) residual_before: Option<core_ir::Type>,
    pub(super) residual_after: Option<core_ir::Type>,
    pub(super) return_wrapper_effect: Option<core_ir::Type>,
}

pub(super) fn handler_binding_info(binding: &Binding) -> Option<HandlerBindingInfo> {
    let mut info = expr_handler_info(&binding.body)?;
    if let Some((input_effect, output_effect)) = principal_handler_effects(&binding.scheme.body) {
        info.principal_input_effect = Some(input_effect);
        info.principal_output_effect = Some(output_effect);
    }
    Some(info)
}

pub(super) fn handler_call_boundary(
    info: &HandlerBindingInfo,
    args: &[&Expr],
    result_ty: &RuntimeType,
) -> HandlerCallBoundary {
    let input_effect = args.first().and_then(|arg| runtime_thunk_effect(&arg.ty));
    let output_effect = runtime_thunk_effect(result_ty);
    HandlerCallBoundary {
        consumes: info.consumes.clone(),
        consumes_input_effect: input_effect
            .as_ref()
            .is_some_and(|effect| effect_contains_any(effect, &info.consumes)),
        preserves_output_effect: output_effect
            .as_ref()
            .is_some_and(|effect| !effect_is_empty(effect)),
        input_effect,
        output_effect,
        pure: info.pure,
    }
}

pub(super) fn handler_adapter_plan(
    info: &HandlerBindingInfo,
    boundary: &HandlerCallBoundary,
) -> HandlerAdapterPlan {
    let residual_before = handler_residual_before(info, boundary);
    let residual_after = residual_before
        .as_ref()
        .map(|effect| remove_consumed_effects(effect, &info.consumes));
    let return_wrapper_effect =
        handler_return_wrapper_effect(info, boundary, residual_after.as_ref());
    HandlerAdapterPlan {
        residual_before,
        residual_after,
        return_wrapper_effect,
    }
}

fn runtime_thunk_effect(ty: &RuntimeType) -> Option<core_ir::Type> {
    match ty {
        RuntimeType::Thunk { effect, .. } => Some(effect.clone()),
        RuntimeType::Core(_) | RuntimeType::Fun { .. } => None,
    }
}

fn handler_residual_before(
    info: &HandlerBindingInfo,
    boundary: &HandlerCallBoundary,
) -> Option<core_ir::Type> {
    let structural = info
        .principal_input_effect
        .as_ref()
        .filter(|effect| effect_contains_any(effect, &info.consumes))
        .cloned()
        .or_else(|| {
            (!info.consumes.is_empty()).then(|| effect_row_from_paths(info.consumes.clone()))
        });
    merge_effects(structural, boundary.input_effect.clone())
}

fn handler_return_wrapper_effect(
    info: &HandlerBindingInfo,
    boundary: &HandlerCallBoundary,
    _residual_after: Option<&core_ir::Type>,
) -> Option<core_ir::Type> {
    if !boundary.pure || boundary.output_effect.is_some() {
        return None;
    }
    info.consumes
        .first()
        .cloned()
        .map(|path| core_ir::Type::Named {
            path,
            args: Vec::new(),
        })
}

fn merge_effects(
    left: Option<core_ir::Type>,
    right: Option<core_ir::Type>,
) -> Option<core_ir::Type> {
    match (left, right) {
        (Some(left), Some(right)) => Some(merge_effect_rows(left, right)),
        (Some(effect), None) | (None, Some(effect)) => Some(effect),
        (None, None) => None,
    }
}

fn merge_effect_rows(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    if effect_is_empty(&left) {
        return right;
    }
    if effect_is_empty(&right) || left == right {
        return left;
    }
    let (mut items, left_tail) = effect_row_parts(left);
    let (right_items, right_tail) = effect_row_parts(right);
    for item in right_items {
        push_unique_effect_item(&mut items, item);
    }
    let tail = merge_effect_tails(left_tail, right_tail);
    effect_row(items, tail)
}

fn effect_row_parts(effect: core_ir::Type) -> (Vec<core_ir::Type>, core_ir::Type) {
    match effect {
        core_ir::Type::Row { items, tail } => (items, *tail),
        other => (vec![other], core_ir::Type::Never),
    }
}

fn merge_effect_tails(left: core_ir::Type, right: core_ir::Type) -> core_ir::Type {
    if effect_is_empty(&left) {
        return right;
    }
    if effect_is_empty(&right) || left == right {
        return left;
    }
    core_ir::Type::Union(vec![left, right])
}

fn push_unique_effect_item(items: &mut Vec<core_ir::Type>, item: core_ir::Type) {
    if effect_is_empty(&item) || items.iter().any(|existing| existing == &item) {
        return;
    }
    items.push(item);
}

fn effect_row(items: Vec<core_ir::Type>, tail: core_ir::Type) -> core_ir::Type {
    let items = items
        .into_iter()
        .filter(|item| !effect_is_empty(item) && item != &tail)
        .collect::<Vec<_>>();
    if items.is_empty() {
        return tail;
    }
    core_ir::Type::Row {
        items,
        tail: Box::new(tail),
    }
}

fn effect_row_from_paths(paths: Vec<core_ir::Path>) -> core_ir::Type {
    effect_row(
        paths
            .into_iter()
            .map(|path| core_ir::Type::Named {
                path,
                args: Vec::new(),
            })
            .collect(),
        core_ir::Type::Never,
    )
}

fn remove_consumed_effects(effect: &core_ir::Type, consumed: &[core_ir::Path]) -> core_ir::Type {
    match effect {
        core_ir::Type::Named { path, .. }
            if consumed
                .iter()
                .any(|consumed| effect_paths_match(consumed, path)) =>
        {
            core_ir::Type::Never
        }
        core_ir::Type::Row { items, tail } => {
            let items = items
                .iter()
                .map(|item| remove_consumed_effects(item, consumed))
                .filter(|item| !effect_is_empty(item))
                .collect();
            let tail = remove_consumed_effects(tail, consumed);
            effect_row(items, tail)
        }
        core_ir::Type::Union(items) | core_ir::Type::Inter(items) => effect_row(
            items
                .iter()
                .map(|item| remove_consumed_effects(item, consumed))
                .filter(|item| !effect_is_empty(item))
                .collect(),
            core_ir::Type::Never,
        ),
        core_ir::Type::Recursive { var, body } => core_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(remove_consumed_effects(body, consumed)),
        },
        other => other.clone(),
    }
}

fn effect_contains_any(effect: &core_ir::Type, targets: &[core_ir::Path]) -> bool {
    let paths = effect_paths(effect);
    paths.iter().any(|path| {
        targets
            .iter()
            .any(|target| effect_paths_match(path, target))
    })
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
            principal_input_effect: None,
            principal_output_effect: None,
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

fn principal_handler_effects(ty: &core_ir::Type) -> Option<(core_ir::Type, core_ir::Type)> {
    match ty {
        core_ir::Type::Fun {
            param_effect,
            ret_effect,
            ..
        } => Some((param_effect.as_ref().clone(), ret_effect.as_ref().clone())),
        core_ir::Type::Recursive { body, .. } => principal_handler_effects(body),
        core_ir::Type::Inter(items) | core_ir::Type::Union(items) => {
            items.iter().find_map(principal_handler_effects)
        }
        _ => None,
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
        assert_eq!(info.principal_input_effect, Some(core_ir::Type::Never));
        assert_eq!(info.principal_output_effect, Some(core_ir::Type::Never));
        assert!(!info.residual_before_known);
        assert!(!info.residual_after_known);
        assert!(!info.pure);
    }

    #[test]
    fn handler_call_boundary_reports_consumed_and_preserved_effects() {
        let consumes = path_segments(&["std", "flow", "sub"]);
        let outer = path_segments(&["std", "junction", "junction"]);
        let info = HandlerBindingInfo {
            consumes: vec![consumes.clone()],
            principal_input_effect: None,
            principal_output_effect: None,
            residual_before_known: true,
            residual_after_known: true,
            pure: true,
        };
        let arg = Expr::typed(
            ExprKind::Var(path("x")),
            RuntimeType::thunk(
                effect_row(vec![effect(consumes), effect(outer.clone())]),
                RuntimeType::core(named("int")),
            ),
        );
        let result_ty = RuntimeType::thunk(effect(outer), RuntimeType::core(named("int")));

        let boundary = handler_call_boundary(&info, &[&arg], &result_ty);

        assert!(boundary.consumes_input_effect);
        assert!(boundary.preserves_output_effect);
        assert!(boundary.pure);
    }

    #[test]
    fn handler_adapter_plan_combines_structural_and_call_site_effects() {
        let consumes = path_segments(&["std", "flow", "sub"]);
        let outer = path_segments(&["std", "junction", "junction"]);
        let info = HandlerBindingInfo {
            consumes: vec![consumes.clone()],
            principal_input_effect: Some(effect(consumes.clone())),
            principal_output_effect: Some(core_ir::Type::Never),
            residual_before_known: true,
            residual_after_known: true,
            pure: true,
        };
        let boundary = HandlerCallBoundary {
            consumes: vec![consumes.clone()],
            input_effect: Some(effect(outer.clone())),
            output_effect: None,
            consumes_input_effect: false,
            preserves_output_effect: false,
            pure: true,
        };

        let plan = handler_adapter_plan(&info, &boundary);

        assert_eq!(
            plan.residual_before,
            Some(effect_row(vec![
                effect(consumes.clone()),
                effect(outer.clone())
            ]))
        );
        assert_eq!(plan.residual_after, Some(effect_row(vec![effect(outer)])));
        assert_eq!(plan.return_wrapper_effect, Some(effect(consumes)));
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

    fn effect(path: core_ir::Path) -> core_ir::Type {
        core_ir::Type::Named {
            path,
            args: Vec::new(),
        }
    }

    fn effect_row(items: Vec<core_ir::Type>) -> core_ir::Type {
        core_ir::Type::Row {
            items,
            tail: Box::new(core_ir::Type::Never),
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
