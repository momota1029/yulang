use super::*;

pub(super) fn substitute_binding(
    binding: Binding,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Binding {
    Binding {
        name: binding.name,
        type_params: binding.type_params,
        scheme: substitute_scheme(binding.scheme, substitutions),
        body: substitute_expr(binding.body, substitutions),
    }
}

pub(super) fn substitute_expr(
    expr: Expr,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Expr {
    let ty = substitute_hir_type(expr.ty, substitutions);
    let kind = match expr.kind {
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body: Box::new(substitute_expr(*body, substitutions)),
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(substitute_expr(*callee, substitutions)),
            arg: Box::new(substitute_expr(*arg, substitutions)),
            evidence: evidence.map(|evidence| substitute_apply_evidence(evidence, substitutions)),
            instantiation: instantiation
                .map(|instantiation| substitute_type_instantiation(instantiation, substitutions)),
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(substitute_expr(*cond, substitutions)),
            then_branch: Box::new(substitute_expr(*then_branch, substitutions)),
            else_branch: Box::new(substitute_expr(*else_branch, substitutions)),
            evidence: evidence.map(|evidence| substitute_join_evidence(evidence, substitutions)),
        },
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(|item| substitute_expr(item, substitutions))
                .collect(),
        ),
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordExprField {
                    name: field.name,
                    value: substitute_expr(field.value, substitutions),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadExpr::Head(expr) => {
                    RecordSpreadExpr::Head(Box::new(substitute_expr(*expr, substitutions)))
                }
                RecordSpreadExpr::Tail(expr) => {
                    RecordSpreadExpr::Tail(Box::new(substitute_expr(*expr, substitutions)))
                }
            }),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(substitute_expr(*value, substitutions))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(substitute_expr(*base, substitutions)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(substitute_expr(*scrutinee, substitutions)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: substitute_pattern(arm.pattern, substitutions),
                    guard: arm.guard.map(|guard| substitute_expr(guard, substitutions)),
                    body: substitute_expr(arm.body, substitutions),
                })
                .collect(),
            evidence: substitute_join_evidence(evidence, substitutions),
        },
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts
                .into_iter()
                .map(|stmt| substitute_stmt(stmt, substitutions))
                .collect(),
            tail: tail.map(|tail| Box::new(substitute_expr(*tail, substitutions))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(substitute_expr(*body, substitutions)),
            arms: arms
                .into_iter()
                .map(|arm| HandleArm {
                    effect: arm.effect,
                    payload: substitute_pattern(arm.payload, substitutions),
                    resume: arm.resume.map(|resume| ResumeBinding {
                        name: resume.name,
                        ty: substitute_hir_type(resume.ty, substitutions),
                    }),
                    guard: arm.guard.map(|guard| substitute_expr(guard, substitutions)),
                    body: substitute_expr(arm.body, substitutions),
                })
                .collect(),
            evidence: substitute_join_evidence(evidence, substitutions),
            handler,
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(substitute_expr(*expr, substitutions)),
        },
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => ExprKind::Thunk {
            effect: substitute_type(&effect, substitutions),
            value: substitute_hir_type(value, substitutions),
            expr: Box::new(substitute_expr(*expr, substitutions)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(substitute_expr(*body, substitutions)),
        },
        ExprKind::PeekId => ExprKind::PeekId,
        ExprKind::FindId { id } => ExprKind::FindId { id },
        ExprKind::AddId { id, allowed, thunk } => ExprKind::AddId {
            id,
            allowed: substitute_type(&allowed, substitutions),
            thunk: Box::new(substitute_expr(*thunk, substitutions)),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from: substitute_type(&from, substitutions),
            to: substitute_type(&to, substitutions),
            expr: Box::new(substitute_expr(*expr, substitutions)),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(substitute_expr(*expr, substitutions)),
        },
        ExprKind::Var(_) | ExprKind::EffectOp(_) | ExprKind::PrimitiveOp(_) | ExprKind::Lit(_) => {
            expr.kind
        }
    };
    Expr { ty, kind }
}

pub(super) fn substitute_stmt(
    stmt: Stmt,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Stmt {
    match stmt {
        Stmt::Let { pattern, value } => Stmt::Let {
            pattern: substitute_pattern(pattern, substitutions),
            value: substitute_expr(value, substitutions),
        },
        Stmt::Expr(expr) => Stmt::Expr(substitute_expr(expr, substitutions)),
        Stmt::Module { def, body } => Stmt::Module {
            def,
            body: substitute_expr(body, substitutions),
        },
    }
}

pub(super) fn substitute_pattern(
    pattern: Pattern,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> Pattern {
    match pattern {
        Pattern::Wildcard { ty } => Pattern::Wildcard {
            ty: substitute_hir_type(ty, substitutions),
        },
        Pattern::Bind { name, ty } => Pattern::Bind {
            name,
            ty: substitute_hir_type(ty, substitutions),
        },
        Pattern::Lit { lit, ty } => Pattern::Lit {
            lit,
            ty: substitute_hir_type(ty, substitutions),
        },
        Pattern::Tuple { items, ty } => Pattern::Tuple {
            items: items
                .into_iter()
                .map(|item| substitute_pattern(item, substitutions))
                .collect(),
            ty: substitute_hir_type(ty, substitutions),
        },
        Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => Pattern::List {
            prefix: prefix
                .into_iter()
                .map(|item| substitute_pattern(item, substitutions))
                .collect(),
            spread: spread.map(|spread| Box::new(substitute_pattern(*spread, substitutions))),
            suffix: suffix
                .into_iter()
                .map(|item| substitute_pattern(item, substitutions))
                .collect(),
            ty: substitute_hir_type(ty, substitutions),
        },
        Pattern::Record { fields, spread, ty } => Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordPatternField {
                    name: field.name,
                    pattern: substitute_pattern(field.pattern, substitutions),
                    default: field
                        .default
                        .map(|default| substitute_expr(default, substitutions)),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadPattern::Head(pattern) => {
                    RecordSpreadPattern::Head(Box::new(substitute_pattern(*pattern, substitutions)))
                }
                RecordSpreadPattern::Tail(pattern) => {
                    RecordSpreadPattern::Tail(Box::new(substitute_pattern(*pattern, substitutions)))
                }
            }),
            ty: substitute_hir_type(ty, substitutions),
        },
        Pattern::Variant { tag, value, ty } => Pattern::Variant {
            tag,
            value: value.map(|value| Box::new(substitute_pattern(*value, substitutions))),
            ty: substitute_hir_type(ty, substitutions),
        },
        Pattern::Or { left, right, ty } => Pattern::Or {
            left: Box::new(substitute_pattern(*left, substitutions)),
            right: Box::new(substitute_pattern(*right, substitutions)),
            ty: substitute_hir_type(ty, substitutions),
        },
        Pattern::As { pattern, name, ty } => Pattern::As {
            pattern: Box::new(substitute_pattern(*pattern, substitutions)),
            name,
            ty: substitute_hir_type(ty, substitutions),
        },
    }
}

pub(super) fn substitute_hir_type(
    ty: RuntimeType,
    substitutions: &BTreeMap<core_ir::TypeVar, core_ir::Type>,
) -> RuntimeType {
    let ty = match ty {
        RuntimeType::Core(ty) => RuntimeType::core(substitute_type(&ty, substitutions)),
        RuntimeType::Fun { param, ret } => RuntimeType::fun(
            substitute_hir_type(*param, substitutions),
            substitute_hir_type(*ret, substitutions),
        ),
        RuntimeType::Thunk { effect, value } => RuntimeType::thunk(
            substitute_type(&effect, substitutions),
            substitute_hir_type(*value, substitutions),
        ),
    };
    normalize_hir_function_type(ty)
}
