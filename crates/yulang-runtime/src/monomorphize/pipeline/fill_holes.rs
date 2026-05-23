use super::*;
use crate::runtime_intrinsic::binding_is_parametric_runtime_intrinsic;
use crate::types::{BoundsChoice, choose_bounds_type, runtime_core_type};

#[derive(Debug, Clone, Default)]
pub(super) struct FillHolesReport {
    pub(super) filled_value_holes: usize,
    pub(super) filled_effect_holes: usize,
}

pub(super) fn fill_final_type_holes(mut module: Module) -> (Module, FillHolesReport) {
    let mut report = FillHolesReport::default();
    for binding in &mut module.bindings {
        if binding_is_parametric_runtime_intrinsic(binding) {
            continue;
        }
        fill_scheme_holes(&mut binding.scheme, &mut report);
        fill_expr_holes(&mut binding.body, &mut report);
        refresh_binding_type_params(binding);
    }
    for root in &mut module.root_exprs {
        fill_expr_holes(root, &mut report);
    }
    (module, report)
}

fn fill_scheme_holes(scheme: &mut typed_ir::Scheme, report: &mut FillHolesReport) {
    fill_core_value_type_holes(&mut scheme.body, report);
    for requirement in &mut scheme.requirements {
        for arg in &mut requirement.args {
            match arg {
                typed_ir::RoleRequirementArg::Input(bounds)
                | typed_ir::RoleRequirementArg::Associated { bounds, .. } => {
                    fill_type_bounds_holes(bounds, report);
                }
            }
        }
    }
}

fn fill_expr_holes(expr: &mut Expr, report: &mut FillHolesReport) {
    match &mut expr.kind {
        ExprKind::Lambda { body, .. } => fill_expr_holes(body, report),
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation: _,
        } => {
            if let Some(evidence) = evidence {
                if let Some(bounds) = evidence.expected_callee.as_ref() {
                    fill_expr_type_from_bounds_if_hole(callee, bounds, report);
                } else {
                    fill_expr_type_from_bounds_if_hole(callee, &evidence.callee, report);
                }
            }
            fill_expr_holes(callee, report);
            if let Some(evidence) = evidence {
                if let Some(bounds) = evidence.expected_arg.as_ref() {
                    fill_expr_type_from_bounds_if_hole(arg, bounds, report);
                } else {
                    fill_expr_type_from_bounds_if_hole(arg, &evidence.arg, report);
                }
            }
            if let Some(param) = runtime_function_param_default(&callee.ty) {
                fill_runtime_value_type_holes_with_runtime_default(&mut arg.ty, param, report);
            }
            fill_expr_holes(arg, report);
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            fill_expr_holes(cond, report);
            fill_expr_holes(then_branch, report);
            fill_expr_holes(else_branch, report);
            if let Some(evidence) = evidence {
                fill_core_value_type_holes(&mut evidence.result, report);
            }
        }
        ExprKind::Tuple(items) => {
            for item in items {
                fill_expr_holes(item, report);
            }
        }
        ExprKind::Record { fields, spread } => {
            for field in fields {
                fill_expr_holes(&mut field.value, report);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        fill_expr_holes(expr, report);
                    }
                }
            }
        }
        ExprKind::Variant { value, .. } => {
            if let Some(value) = value {
                fill_expr_holes(value, report);
            }
        }
        ExprKind::Select { base, .. } => fill_expr_holes(base, report),
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => {
            fill_expr_holes(scrutinee, report);
            fill_core_value_type_holes(&mut evidence.result, report);
            for arm in arms {
                fill_match_arm_holes(arm, report);
            }
        }
        ExprKind::Block { stmts, tail } => {
            for stmt in stmts {
                fill_stmt_holes(stmt, report);
            }
            if let Some(tail) = tail {
                fill_expr_holes(tail, report);
            }
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            fill_expr_holes(body, report);
            fill_core_value_type_holes(&mut evidence.result, report);
            fill_handle_effect_holes(handler, report);
            for arm in arms {
                fill_handle_arm_holes(arm, report);
            }
        }
        ExprKind::BindHere { expr } | ExprKind::Pack { expr, .. } => {
            fill_expr_holes(expr, report);
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            fill_effect_type_holes(effect, report);
            fill_runtime_value_type_holes(value, report);
            fill_expr_holes(expr, report);
        }
        ExprKind::LocalPushId { body, .. } => fill_expr_holes(body, report),
        ExprKind::AddId { allowed, thunk, .. } => {
            fill_effect_type_holes(allowed, report);
            fill_expr_holes(thunk, report);
        }
        ExprKind::Coerce { from, to, expr } => {
            fill_core_value_type_holes(from, report);
            fill_core_value_type_holes(to, report);
            fill_expr_holes(expr, report);
        }
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => {}
    }
    fill_expr_result_type_holes(expr, report);
}

fn fill_stmt_holes(stmt: &mut Stmt, report: &mut FillHolesReport) {
    match stmt {
        Stmt::Let { pattern, value } => {
            fill_expr_holes(value, report);
            fill_pattern_type_from_runtime_default_if_hole(pattern, value.ty.clone(), report);
            fill_pattern_holes(pattern, report);
        }
        Stmt::Expr(expr) | Stmt::Module { body: expr, .. } => fill_expr_holes(expr, report),
    }
}

fn fill_match_arm_holes(arm: &mut MatchArm, report: &mut FillHolesReport) {
    fill_pattern_holes(&mut arm.pattern, report);
    if let Some(guard) = &mut arm.guard {
        fill_expr_holes(guard, report);
    }
    fill_expr_holes(&mut arm.body, report);
}

fn fill_handle_arm_holes(arm: &mut HandleArm, report: &mut FillHolesReport) {
    fill_pattern_holes(&mut arm.payload, report);
    if let Some(resume) = &mut arm.resume {
        fill_runtime_value_type_holes(&mut resume.ty, report);
    }
    if let Some(guard) = &mut arm.guard {
        fill_expr_holes(guard, report);
    }
    fill_expr_holes(&mut arm.body, report);
}

fn fill_pattern_holes(pattern: &mut Pattern, report: &mut FillHolesReport) {
    match pattern {
        Pattern::Tuple { items, ty } => {
            for item in items.iter_mut() {
                fill_pattern_holes(item, report);
            }
            let shape = typed_ir::Type::Tuple(
                items
                    .iter()
                    .map(|item| runtime_core_type(pattern_type(item)))
                    .collect(),
            );
            fill_runtime_value_type_holes_with_default(ty, shape, report);
        }
        Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => {
            for item in prefix {
                fill_pattern_holes(item, report);
            }
            if let Some(spread) = spread {
                fill_pattern_holes(spread, report);
            }
            for item in suffix {
                fill_pattern_holes(item, report);
            }
            fill_runtime_value_type_holes(ty, report);
        }
        Pattern::Record { fields, spread, ty } => {
            for field in fields.iter_mut() {
                fill_pattern_holes(&mut field.pattern, report);
                if let Some(default) = &mut field.default {
                    fill_expr_holes(default, report);
                }
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpreadPattern::Head(pattern) | RecordSpreadPattern::Tail(pattern) => {
                        fill_pattern_holes(pattern, report);
                    }
                }
            }
            if spread.is_none() {
                let shape = typed_ir::Type::Record(typed_ir::RecordType {
                    fields: fields
                        .iter()
                        .map(|field| typed_ir::RecordField {
                            name: field.name.clone(),
                            value: runtime_core_type(pattern_type(&field.pattern)),
                            optional: field.default.is_some(),
                        })
                        .collect(),
                    spread: None,
                });
                fill_runtime_value_type_holes_with_default(ty, shape, report);
            } else {
                fill_runtime_value_type_holes(ty, report);
            }
        }
        Pattern::Variant { value, ty, .. } => {
            if let Some(value) = value {
                fill_pattern_holes(value, report);
            }
            fill_runtime_value_type_holes(ty, report);
        }
        Pattern::Or { left, right, ty } => {
            fill_pattern_holes(left, report);
            fill_pattern_holes(right, report);
            fill_runtime_value_type_holes(ty, report);
        }
        Pattern::As { pattern, ty, .. } => {
            fill_pattern_holes(pattern, report);
            if runtime_value_type_is_direct_hole(ty) {
                let shape = runtime_core_type(pattern_type(pattern));
                fill_runtime_value_type_holes_with_default(ty, shape, report);
            } else {
                fill_runtime_value_type_holes(ty, report);
            }
        }
        Pattern::Wildcard { ty } | Pattern::Bind { ty, .. } | Pattern::Lit { ty, .. } => {
            fill_runtime_value_type_holes(ty, report);
        }
    }
}

fn fill_expr_result_type_holes(expr: &mut Expr, report: &mut FillHolesReport) {
    if let Some(default) = expr_result_type_default(&expr.kind) {
        fill_runtime_value_type_holes_with_default(&mut expr.ty, default, report);
    } else {
        fill_runtime_value_type_holes(&mut expr.ty, report);
    }
}

fn expr_result_type_default(kind: &ExprKind) -> Option<typed_ir::Type> {
    match kind {
        ExprKind::Apply {
            evidence: Some(evidence),
            ..
        } => runtime_type_default_from_bounds(&evidence.result).map(|ty| runtime_core_type(&ty)),
        ExprKind::Tuple(items) => Some(typed_ir::Type::Tuple(
            items
                .iter()
                .map(|item| runtime_core_type(&item.ty))
                .collect(),
        )),
        ExprKind::Record {
            fields,
            spread: None,
        } => Some(typed_ir::Type::Record(typed_ir::RecordType {
            fields: fields
                .iter()
                .map(|field| typed_ir::RecordField {
                    name: field.name.clone(),
                    value: runtime_core_type(&field.value.ty),
                    optional: false,
                })
                .collect(),
            spread: None,
        })),
        ExprKind::Variant { tag, value } => Some(typed_ir::Type::Variant(typed_ir::VariantType {
            cases: vec![typed_ir::VariantCase {
                name: tag.clone(),
                payloads: value
                    .iter()
                    .map(|value| runtime_core_type(&value.ty))
                    .collect(),
            }],
            tail: Some(Box::new(typed_ir::Type::Never)),
        })),
        _ => None,
    }
}

fn fill_expr_type_from_bounds_if_hole(
    expr: &mut Expr,
    bounds: &typed_ir::TypeBounds,
    report: &mut FillHolesReport,
) {
    if !runtime_value_type_is_direct_hole(&expr.ty) {
        return;
    }
    let Some(default) = runtime_type_default_from_bounds(bounds) else {
        return;
    };
    expr.ty = default;
    report.filled_value_holes += 1;
}

fn runtime_type_default_from_bounds(bounds: &typed_ir::TypeBounds) -> Option<RuntimeType> {
    let ty = choose_bounds_type(bounds, BoundsChoice::ValidationEvidence)?;
    if core_value_type_is_direct_hole(&ty) {
        return None;
    }
    Some(normalize_hir_function_type(RuntimeType::core(ty)))
}

fn runtime_function_param_default(ty: &RuntimeType) -> Option<RuntimeType> {
    match ty {
        RuntimeType::Fun { param, .. } => Some(param.as_ref().clone()),
        RuntimeType::Thunk { value, .. } => runtime_function_param_default(value),
        RuntimeType::Core(typed_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => {
            let param = RuntimeType::core(param.as_ref().clone());
            if should_thunk_effect(param_effect) {
                Some(RuntimeType::thunk(param_effect.as_ref().clone(), param))
            } else {
                Some(param)
            }
        }
        RuntimeType::Unknown | RuntimeType::Core(_) => None,
    }
}

fn pattern_type(pattern: &Pattern) -> &RuntimeType {
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

fn pattern_type_mut(pattern: &mut Pattern) -> &mut RuntimeType {
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

fn fill_pattern_type_from_runtime_default_if_hole(
    pattern: &mut Pattern,
    default: RuntimeType,
    report: &mut FillHolesReport,
) {
    fill_runtime_value_type_holes_with_runtime_default(pattern_type_mut(pattern), default, report);
}

fn fill_handle_effect_holes(handler: &mut HandleEffect, report: &mut FillHolesReport) {
    if let Some(effect) = &mut handler.residual_before {
        fill_effect_type_holes(effect, report);
    }
    if let Some(effect) = &mut handler.residual_after {
        fill_effect_type_holes(effect, report);
    }
}

fn fill_type_bounds_holes(bounds: &mut typed_ir::TypeBounds, report: &mut FillHolesReport) {
    if let Some(lower) = &mut bounds.lower {
        fill_core_value_type_holes(lower, report);
    }
    if let Some(upper) = &mut bounds.upper {
        fill_core_value_type_holes(upper, report);
    }
}

fn fill_runtime_value_type_holes(ty: &mut RuntimeType, report: &mut FillHolesReport) {
    match ty {
        RuntimeType::Unknown => {}
        RuntimeType::Core(ty) => fill_core_value_type_holes(ty, report),
        RuntimeType::Fun { .. } => {}
        RuntimeType::Thunk { effect, value } => {
            fill_effect_type_holes(effect, report);
            fill_runtime_value_type_holes(value, report);
        }
    }
}

fn fill_runtime_value_type_holes_with_default(
    ty: &mut RuntimeType,
    default: typed_ir::Type,
    report: &mut FillHolesReport,
) {
    if runtime_value_type_is_direct_hole(ty) {
        *ty = RuntimeType::core(default);
        report.filled_value_holes += 1;
    } else {
        fill_runtime_value_type_holes(ty, report);
    }
}

fn fill_runtime_value_type_holes_with_runtime_default(
    ty: &mut RuntimeType,
    default: RuntimeType,
    report: &mut FillHolesReport,
) {
    if runtime_value_type_is_direct_hole(ty) && !runtime_value_type_is_direct_hole(&default) {
        *ty = default;
        report.filled_value_holes += 1;
    }
}

fn runtime_value_type_is_direct_hole(ty: &RuntimeType) -> bool {
    matches!(
        ty,
        RuntimeType::Unknown | RuntimeType::Core(typed_ir::Type::Unknown | typed_ir::Type::Any)
    )
}

fn core_value_type_is_direct_hole(ty: &typed_ir::Type) -> bool {
    matches!(ty, typed_ir::Type::Unknown | typed_ir::Type::Any)
}

fn fill_core_value_type_holes(ty: &mut typed_ir::Type, report: &mut FillHolesReport) {
    match ty {
        typed_ir::Type::Fun {
            param_effect,
            ret_effect,
            ..
        } => {
            fill_effect_type_holes(param_effect, report);
            fill_effect_type_holes(ret_effect, report);
        }
        typed_ir::Type::Named { args, .. } => {
            for arg in args {
                fill_type_arg_holes(arg, report);
            }
        }
        typed_ir::Type::Tuple(items)
        | typed_ir::Type::Union(items)
        | typed_ir::Type::Inter(items) => {
            for item in items {
                fill_core_value_type_holes(item, report);
            }
        }
        typed_ir::Type::Record(record) => {
            for field in &mut record.fields {
                fill_core_value_type_holes(&mut field.value, report);
            }
            if let Some(spread) = &mut record.spread {
                match spread {
                    typed_ir::RecordSpread::Head(ty) | typed_ir::RecordSpread::Tail(ty) => {
                        fill_core_value_type_holes(ty, report);
                    }
                }
            }
        }
        typed_ir::Type::Variant(variant) => {
            for case in &mut variant.cases {
                for payload in &mut case.payloads {
                    fill_core_value_type_holes(payload, report);
                }
            }
            if let Some(tail) = &mut variant.tail {
                fill_core_value_type_holes(tail, report);
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                fill_effect_type_holes(item, report);
            }
            fill_effect_type_holes(tail, report);
        }
        typed_ir::Type::Recursive { body, .. } => fill_core_value_type_holes(body, report),
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_) => {}
    }
}

fn fill_effect_type_holes(_ty: &mut typed_ir::Type, _report: &mut FillHolesReport) {
    // Effect holes are only safe to close after total substitution has applied
    // every lower/upper candidate. Closing them in the current legacy runtime
    // surface can hide std or synthetic requests from their handlers.
}

fn fill_type_arg_holes(arg: &mut typed_ir::TypeArg, report: &mut FillHolesReport) {
    match arg {
        typed_ir::TypeArg::Type(ty) => fill_core_value_type_holes(ty, report),
        typed_ir::TypeArg::Bounds(bounds) => fill_type_bounds_holes(bounds, report),
    }
}

#[cfg(test)]
fn unit_type() -> typed_ir::Type {
    typed_ir::Type::Named {
        path: typed_ir::Path::from_name(typed_ir::Name("unit".to_string())),
        args: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn final_type_holes_fill_structural_value_positions_in_module() {
        let tuple = Expr::typed(
            ExprKind::Tuple(vec![Expr::typed(
                ExprKind::Lit(typed_ir::Lit::Unit),
                RuntimeType::core(unit_type()),
            )]),
            RuntimeType::Unknown,
        );
        let thunk = Expr::typed(
            ExprKind::Thunk {
                effect: typed_ir::Type::Unknown,
                value: RuntimeType::core(unit_type()),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::core(unit_type()),
                )),
            },
            RuntimeType::Thunk {
                effect: typed_ir::Type::Any,
                value: Box::new(RuntimeType::core(unit_type())),
            },
        );
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![tuple, thunk],
            roots: vec![Root::Expr(0), Root::Expr(1)],
            role_impls: Vec::new(),
        };

        let (module, report) = fill_final_type_holes(module);

        assert_eq!(report.filled_value_holes, 1);
        assert_eq!(report.filled_effect_holes, 0);
        assert_eq!(
            module.root_exprs[0].ty,
            RuntimeType::core(typed_ir::Type::Tuple(vec![unit_type()]))
        );
        assert_eq!(
            module.root_exprs[1].ty,
            RuntimeType::thunk(typed_ir::Type::Any, RuntimeType::core(unit_type()))
        );
        let ExprKind::Thunk {
            effect,
            value,
            expr,
        } = &module.root_exprs[1].kind
        else {
            panic!("root should stay a thunk");
        };
        assert_eq!(effect, &typed_ir::Type::Unknown);
        assert_eq!(value, &RuntimeType::core(unit_type()));
        assert_eq!(expr.ty, RuntimeType::core(unit_type()));
    }

    #[test]
    fn final_type_holes_skip_parametric_runtime_intrinsic_bindings() {
        let body = Expr::typed(
            ExprKind::PrimitiveOp(typed_ir::PrimitiveOp::ListEmpty),
            RuntimeType::Unknown,
        );
        let binding = Binding {
            name: typed_ir::Path::from_name(typed_ir::Name("__runtime_list_empty".to_string())),
            type_params: vec![typed_ir::TypeVar("a".to_string())],
            scheme: typed_ir::Scheme {
                requirements: Vec::new(),
                body: typed_ir::Type::Var(typed_ir::TypeVar("a".to_string())),
            },
            body,
        };
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: vec![binding.clone()],
            root_exprs: Vec::new(),
            roots: Vec::new(),
            role_impls: Vec::new(),
        };

        let (module, report) = fill_final_type_holes(module);

        assert_eq!(report.filled_value_holes, 0);
        assert_eq!(module.bindings[0], binding);
    }

    #[test]
    fn final_type_holes_leave_effect_vars_for_total_substitution() {
        let effect_var = typed_ir::Type::Var(typed_ir::TypeVar("e".to_string()));
        let root = Expr::typed(
            ExprKind::Thunk {
                effect: effect_var.clone(),
                value: RuntimeType::core(unit_type()),
                expr: Box::new(Expr::typed(
                    ExprKind::Lit(typed_ir::Lit::Unit),
                    RuntimeType::core(unit_type()),
                )),
            },
            RuntimeType::Thunk {
                effect: effect_var.clone(),
                value: Box::new(RuntimeType::core(unit_type())),
            },
        );
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let (module, report) = fill_final_type_holes(module);

        assert_eq!(report.filled_effect_holes, 0);
        assert_eq!(
            module.root_exprs[0].ty,
            RuntimeType::thunk(effect_var.clone(), RuntimeType::core(unit_type()))
        );
        let ExprKind::Thunk { effect, .. } = &module.root_exprs[0].kind else {
            panic!("root should stay a thunk");
        };
        assert_eq!(effect, &effect_var);
    }

    #[test]
    fn final_type_holes_leave_value_vars_for_substitution_passes() {
        let var = typed_ir::Type::Var(typed_ir::TypeVar("a".to_string()));
        let root = Expr::typed(
            ExprKind::Lit(typed_ir::Lit::Unit),
            RuntimeType::core(var.clone()),
        );
        let module = Module {
            path: typed_ir::Path::default(),
            bindings: Vec::new(),
            root_exprs: vec![root],
            roots: vec![Root::Expr(0)],
            role_impls: Vec::new(),
        };

        let (module, report) = fill_final_type_holes(module);

        assert_eq!(report.filled_value_holes, 0);
        assert_eq!(module.root_exprs[0].ty, RuntimeType::core(var));
    }
}
