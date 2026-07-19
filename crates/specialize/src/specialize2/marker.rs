use super::*;

pub(super) fn function_boundary_types(actual: &Type, expected: &Type) -> bool {
    matches!((actual, expected), (Type::Fun { .. }, Type::Fun { .. }))
}

pub(super) fn wrap_stack_handler_marker(signature: &Type, body: Expr) -> Expr {
    if let Some(path) = stack_handler_marker_path(signature) {
        return wrap_stack_handler_marker_body(path, body);
    }
    let Some(path) = stack_handler_marker_path_from_body(&body) else {
        return body;
    };
    wrap_stack_handler_marker_body(path, body)
}

pub(super) fn stack_handler_marker_path(signature: &Type) -> Option<Vec<String>> {
    let Type::Fun {
        arg, arg_effect, ..
    } = signature
    else {
        return None;
    };
    effect_marker_path(arg_effect).or_else(|| thunk_effect_marker_path(arg))
}

pub(super) fn thunk_effect_marker_path(ty: &Type) -> Option<Vec<String>> {
    match ty {
        Type::Thunk { effect, .. } => effect_marker_path(effect),
        Type::Stack { inner, .. } => thunk_effect_marker_path(inner),
        _ => None,
    }
}

pub(super) fn effect_marker_path(effect: &Type) -> Option<Vec<String>> {
    match effect {
        Type::EffectRow(items) => items.iter().find_map(effect_marker_path),
        Type::Con { path, .. } if !path.is_empty() => Some(path.clone()),
        Type::Stack { inner, .. } => effect_marker_path(inner),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            effect_marker_path(left).or_else(|| effect_marker_path(right))
        }
        _ => None,
    }
}

pub(super) fn stack_handler_marker_path_from_body(body: &Expr) -> Option<Vec<String>> {
    match &body.kind {
        ExprKind::Catch { body, arms } => catch_stack_handler_marker_path(body, arms)
            .or_else(|| stack_handler_marker_path_from_body(body))
            .or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(stack_handler_marker_path_from_body)
                        .or_else(|| stack_handler_marker_path_from_body(&arm.body))
                })
            }),
        ExprKind::Lambda(_, body) => stack_handler_marker_path_from_body(body),
        ExprKind::Block(block) => stack_handler_marker_path_from_block(block),
        ExprKind::FunctionAdapter { function, .. }
        | ExprKind::Coerce { expr: function, .. }
        | ExprKind::MakeThunk { body: function, .. }
        | ExprKind::ForceThunk {
            thunk: function, ..
        }
        | ExprKind::Select { base: function, .. } => stack_handler_marker_path_from_body(function),
        ExprKind::Apply(callee, arg) | ExprKind::RefSet(callee, arg) => {
            stack_handler_marker_path_from_body(callee)
                .or_else(|| stack_handler_marker_path_from_body(arg))
        }
        ExprKind::Tuple(items) => items.iter().find_map(stack_handler_marker_path_from_body),
        ExprKind::Record { fields, spread } => fields
            .iter()
            .find_map(|field| stack_handler_marker_path_from_body(&field.value))
            .or_else(|| stack_handler_marker_path_from_record_spread(spread)),
        ExprKind::PolyVariant { payloads, .. } => payloads
            .iter()
            .find_map(stack_handler_marker_path_from_body),
        ExprKind::Case { scrutinee, arms } => stack_handler_marker_path_from_body(scrutinee)
            .or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_ref()
                        .and_then(stack_handler_marker_path_from_body)
                        .or_else(|| stack_handler_marker_path_from_body(&arm.body))
                })
            }),
        _ => None,
    }
}

pub(super) fn catch_stack_handler_marker_path(
    body: &Expr,
    arms: &[CatchArm],
) -> Option<Vec<String>> {
    let path = forced_body_effect_marker_path(body)?;
    arms.iter()
        .filter_map(|arm| arm.operation_path.as_ref())
        .any(|operation_path| effect_paths_same_family(&path, operation_path))
        .then_some(path)
}

pub(super) fn forced_body_effect_marker_path(body: &Expr) -> Option<Vec<String>> {
    match &body.kind {
        ExprKind::ForceThunk { target, .. } => effect_marker_path(&target.effect),
        ExprKind::MarkerFrame { body, .. } | ExprKind::Coerce { expr: body, .. } => {
            forced_body_effect_marker_path(body)
        }
        _ => None,
    }
}

pub(super) fn stack_handler_marker_path_from_block(block: &Block) -> Option<Vec<String>> {
    block
        .stmts
        .iter()
        .find_map(stack_handler_marker_path_from_stmt)
        .or_else(|| {
            block
                .tail
                .as_ref()
                .and_then(|tail| stack_handler_marker_path_from_body(tail))
        })
}

pub(super) fn stack_handler_marker_path_from_stmt(stmt: &Stmt) -> Option<Vec<String>> {
    match stmt {
        Stmt::Let(_, _, expr) | Stmt::Expr(expr) => stack_handler_marker_path_from_body(expr),
        Stmt::Module(_, stmts) => stmts.iter().find_map(stack_handler_marker_path_from_stmt),
    }
}

pub(super) fn stack_handler_marker_path_from_record_spread(
    spread: &RecordSpread<Box<Expr>>,
) -> Option<Vec<String>> {
    match spread {
        RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
            stack_handler_marker_path_from_body(expr)
        }
        RecordSpread::None => None,
    }
}

pub(super) fn wrap_stack_handler_marker_body(path: Vec<String>, body: Expr) -> Expr {
    let application_provenance = body.application_provenance;
    let wrapped = match body.kind {
        ExprKind::Lambda(param, lambda_body) => Expr::new(ExprKind::Lambda(
            param,
            Box::new(wrap_stack_handler_marker_body(path, *lambda_body)),
        )),
        ExprKind::Catch { body, arms } => Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::MarkerFrame {
                path: path.clone(),
                body,
            })),
            arms: arms
                .into_iter()
                .map(|arm| wrap_stack_handler_marker_catch_arm(path.clone(), arm))
                .collect(),
        }),
        ExprKind::Block(block) => Expr::new(ExprKind::Block(wrap_stack_handler_marker_block(
            path, block,
        ))),
        ExprKind::FunctionAdapter {
            source,
            target,
            function,
            hygiene,
        } => Expr::new(ExprKind::FunctionAdapter {
            source,
            target,
            function: Box::new(wrap_stack_handler_marker_body(path, *function)),
            hygiene,
        }),
        ExprKind::Coerce {
            source,
            target,
            expr,
        } => Expr::new(ExprKind::Coerce {
            source,
            target,
            expr: Box::new(wrap_stack_handler_marker_body(path, *expr)),
        }),
        ExprKind::MakeThunk {
            source,
            target,
            body,
        } => Expr::new(ExprKind::MakeThunk {
            source,
            target,
            body: Box::new(wrap_stack_handler_marker_body(path, *body)),
        }),
        ExprKind::ForceThunk {
            source,
            target,
            thunk,
        } => Expr::new(ExprKind::ForceThunk {
            source,
            target,
            thunk: Box::new(wrap_stack_handler_marker_body(path, *thunk)),
        }),
        ExprKind::Apply(callee, arg) => Expr::new(ExprKind::Apply(
            Box::new(wrap_stack_handler_marker_body(path.clone(), *callee)),
            Box::new(wrap_stack_handler_marker_body(path, *arg)),
        )),
        ExprKind::RefSet(reference, value) => Expr::new(ExprKind::RefSet(
            Box::new(wrap_stack_handler_marker_body(path.clone(), *reference)),
            Box::new(wrap_stack_handler_marker_body(path, *value)),
        )),
        ExprKind::Tuple(items) => Expr::new(ExprKind::Tuple(
            items
                .into_iter()
                .map(|item| wrap_stack_handler_marker_body(path.clone(), item))
                .collect(),
        )),
        ExprKind::Record { fields, spread } => Expr::new(ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordField {
                    name: field.name,
                    value: wrap_stack_handler_marker_body(path.clone(), field.value),
                })
                .collect(),
            spread: wrap_stack_handler_marker_record_spread(path, spread),
        }),
        ExprKind::PolyVariant { tag, payloads } => Expr::new(ExprKind::PolyVariant {
            tag,
            payloads: payloads
                .into_iter()
                .map(|payload| wrap_stack_handler_marker_body(path.clone(), payload))
                .collect(),
        }),
        ExprKind::Select {
            base,
            name,
            resolution,
        } => Expr::new(ExprKind::Select {
            base: Box::new(wrap_stack_handler_marker_body(path, *base)),
            name,
            resolution,
        }),
        ExprKind::Case { scrutinee, arms } => Expr::new(ExprKind::Case {
            scrutinee: Box::new(wrap_stack_handler_marker_body(path.clone(), *scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| wrap_stack_handler_marker_case_arm(path.clone(), arm))
                .collect(),
        }),
        other => Expr::new(other),
    };
    if let Some(tag) = application_provenance {
        wrapped.with_application_provenance(tag)
    } else {
        wrapped
    }
}

pub(super) fn wrap_stack_handler_marker_block(path: Vec<String>, block: Block) -> Block {
    Block {
        stmts: block
            .stmts
            .into_iter()
            .map(|stmt| wrap_stack_handler_marker_stmt(path.clone(), stmt))
            .collect(),
        tail: block
            .tail
            .map(|tail| Box::new(wrap_stack_handler_marker_body(path, *tail))),
    }
}

pub(super) fn wrap_stack_handler_marker_stmt(path: Vec<String>, stmt: Stmt) -> Stmt {
    match stmt {
        Stmt::Let(vis, pat, expr) => {
            Stmt::Let(vis, pat, wrap_stack_handler_marker_body(path, expr))
        }
        Stmt::Expr(expr) => Stmt::Expr(wrap_stack_handler_marker_body(path, expr)),
        Stmt::Module(def, stmts) => Stmt::Module(
            def,
            stmts
                .into_iter()
                .map(|stmt| wrap_stack_handler_marker_stmt(path.clone(), stmt))
                .collect(),
        ),
    }
}

pub(super) fn wrap_stack_handler_marker_case_arm(path: Vec<String>, arm: CaseArm) -> CaseArm {
    CaseArm {
        pat: arm.pat,
        guard: arm
            .guard
            .map(|guard| wrap_stack_handler_marker_body(path.clone(), guard)),
        body: wrap_stack_handler_marker_body(path, arm.body),
    }
}

pub(super) fn wrap_stack_handler_marker_catch_arm(path: Vec<String>, arm: CatchArm) -> CatchArm {
    CatchArm {
        operation_path: arm.operation_path,
        pat: arm.pat,
        continuation: arm.continuation,
        guard: arm
            .guard
            .map(|guard| wrap_stack_handler_marker_body(path.clone(), guard)),
        body: wrap_stack_handler_marker_body(path, arm.body),
    }
}

pub(super) fn wrap_stack_handler_marker_record_spread(
    path: Vec<String>,
    spread: RecordSpread<Box<Expr>>,
) -> RecordSpread<Box<Expr>> {
    match spread {
        RecordSpread::Head(expr) => {
            RecordSpread::Head(Box::new(wrap_stack_handler_marker_body(path, *expr)))
        }
        RecordSpread::Tail(expr) => {
            RecordSpread::Tail(Box::new(wrap_stack_handler_marker_body(path, *expr)))
        }
        RecordSpread::None => RecordSpread::None,
    }
}
