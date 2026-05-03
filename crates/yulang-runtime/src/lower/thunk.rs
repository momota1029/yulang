//! Runtime thunk construction rules used by core-to-runtime lowering.
//!
//! This module owns the places where lowering deliberately changes a value
//! expression into `Thunk[effect, value]` or forces a thunk with `BindHere`.
//! Later passes may preserve, specialize, or refine these shapes, but they
//! should not rediscover thunk boundaries from erased display types.
//!
//! The intended rules are:
//!
//! - an expected thunk type wraps a compatible value expression in `Thunk`;
//! - an expected value type forces a compatible thunk with `BindHere`;
//! - forced effects from expression forms are attached once with `Thunk`;
//! - function-boundary hygiene protects created thunks with `AddId[peek, effect]`;
//! - pure or empty effects are left as values, not administrative thunks.

use super::*;

pub(super) fn apply_param_allowed_effect(
    param_ty: RuntimeType,
    annotation: Option<&core_ir::ParamEffectAnnotation>,
    function_allowed_effects: Option<&core_ir::FunctionSigAllowedEffects>,
) -> RuntimeType {
    if function_allowed_effects.is_none()
        && let Some(allowed) = allowed_effect_for_param(annotation, None, &param_ty)
            .map(|allowed| project_runtime_effect(&allowed))
    {
        return match param_ty {
            RuntimeType::Thunk { .. } => param_ty,
            value => RuntimeType::thunk(allowed, value),
        };
    }
    param_ty
}

pub(super) fn allowed_effect_for_param(
    annotation: Option<&core_ir::ParamEffectAnnotation>,
    function_allowed_effects: Option<&core_ir::FunctionSigAllowedEffects>,
    param_ty: &RuntimeType,
) -> Option<core_ir::Type> {
    if let Some(allowed) = function_allowed_effects {
        return Some(match allowed {
            core_ir::FunctionSigAllowedEffects::Wildcard => wildcard_effect_type(),
            core_ir::FunctionSigAllowedEffects::Effects(paths) => core_ir::Type::Row {
                items: paths
                    .iter()
                    .cloned()
                    .map(|path| core_ir::Type::Named {
                        path,
                        args: Vec::new(),
                    })
                    .collect(),
                tail: Box::new(core_ir::Type::Never),
            },
        });
    }
    match annotation {
        Some(core_ir::ParamEffectAnnotation::Wildcard) => Some(wildcard_effect_type()),
        Some(core_ir::ParamEffectAnnotation::Region(_)) => thunk_effect(param_ty),
        None if returns_thunk(param_ty) => Some(empty_row()),
        None => None,
    }
}

pub(super) fn returns_thunk(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Thunk { .. } => true,
        RuntimeType::Fun { ret, .. } => returns_thunk(ret),
        _ => false,
    }
}

pub(super) fn empty_row() -> core_ir::Type {
    core_ir::Type::Row {
        items: Vec::new(),
        tail: Box::new(core_ir::Type::Never),
    }
}

pub(super) fn prepare_expr_for_expected_profiled(
    expr: Expr,
    expected: &RuntimeType,
    source: TypeSource,
    profile: &mut RuntimeAdapterProfile,
) -> RuntimeResult<Expr> {
    prepare_expr_for_expected_with_adapter_source_profiled(expr, expected, source, profile, None)
}

pub(super) fn prepare_expr_for_expected_with_adapter_source_profiled(
    expr: Expr,
    expected: &RuntimeType,
    source: TypeSource,
    profile: &mut RuntimeAdapterProfile,
    adapter_source: Option<RuntimeAdapterSource>,
) -> RuntimeResult<Expr> {
    match expected {
        RuntimeType::Thunk { effect, value } => match &expr.ty {
            RuntimeType::Thunk { .. } => {
                require_apply_arg_compatible(expected, &expr.ty, source)?;
                profile.reused_thunk += 1;
                Ok(expr)
            }
            _ => {
                require_same_hir_type(value, &expr.ty, source)?;
                let value = more_informative_hir_type(value, &expr.ty);
                let ty = RuntimeType::thunk(effect.clone(), value.clone());
                profile.value_to_thunk += 1;
                if apply_adapter_source(source) {
                    profile.apply_evidence_value_to_thunk += 1;
                    if let Some(adapter_source) = adapter_source {
                        adapter_source.profile_apply_adapter(profile);
                    }
                    if apply_argument_adapter_source(source)
                        || adapter_source.is_some_and(|source| source.has_apply_arg_source_edge)
                    {
                        profile.apply_evidence_value_to_thunk_with_source_edge += 1;
                    }
                }
                Ok(Expr::typed(
                    ExprKind::Thunk {
                        effect: effect.clone(),
                        value,
                        expr: Box::new(expr),
                    },
                    ty,
                ))
            }
        },
        RuntimeType::Core(core_ir::Type::Any | core_ir::Type::Var(_))
            if matches!(expr.ty, RuntimeType::Thunk { .. }) =>
        {
            Ok(expr)
        }
        _ => {
            if matches!(expr.ty, RuntimeType::Thunk { .. }) && apply_adapter_source(source) {
                profile.apply_evidence_thunk_to_value += 1;
                profile.apply_evidence_bind_here += 1;
                if let Some(adapter_source) = adapter_source {
                    adapter_source.profile_apply_adapter(profile);
                }
                if apply_argument_adapter_source(source)
                    || adapter_source.is_some_and(|source| source.has_apply_arg_source_edge)
                {
                    profile.apply_evidence_thunk_to_value_with_source_edge += 1;
                    profile.apply_evidence_bind_here_with_source_edge += 1;
                }
            }
            let (expr, actual) = force_value_expr_profiled(expr, profile);
            require_same_hir_type(expected, &actual, source)?;
            Ok(expr)
        }
    }
}

fn apply_adapter_source(source: TypeSource) -> bool {
    matches!(
        source,
        TypeSource::ApplyEvidence | TypeSource::ApplyArgumentEvidence
    )
}

fn apply_argument_adapter_source(source: TypeSource) -> bool {
    matches!(source, TypeSource::ApplyArgumentEvidence)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct RuntimeAdapterSource {
    pub has_apply_evidence: bool,
    pub has_apply_arg_source_edge: bool,
}

impl RuntimeAdapterSource {
    fn profile_apply_adapter(self, profile: &mut RuntimeAdapterProfile) {
        if self.has_apply_evidence {
            profile.apply_evidence_adapter_with_evidence += 1;
        } else {
            profile.apply_evidence_adapter_without_evidence += 1;
        }
        if self.has_apply_arg_source_edge {
            profile.apply_evidence_adapter_with_source_edge += 1;
        }
    }
}

pub(super) fn finalize_effectful_expr_profiled(
    expr: Expr,
    expected: Option<&RuntimeType>,
    source: TypeSource,
    profile: &mut RuntimeAdapterProfile,
) -> RuntimeResult<Expr> {
    let expr = attach_forced_effect_profiled(expr, profile);
    match expected {
        Some(expected) => prepare_expr_for_expected_profiled(expr, expected, source, profile),
        None => Ok(expr),
    }
}

pub(super) fn finalize_handler_expr_profiled(
    expr: Expr,
    expected: Option<&RuntimeType>,
    source: TypeSource,
    profile: &mut RuntimeAdapterProfile,
) -> RuntimeResult<Expr> {
    let expr = attach_forced_effect_profiled(expr, profile);
    match (expected, &expr.ty) {
        (
            Some(RuntimeType::Thunk {
                value: expected_value,
                ..
            }),
            actual,
        ) if hir_type_compatible(expected_value, actual) => {
            require_same_hir_type(expected_value, actual, source)?;
            Ok(expr)
        }
        (Some(expected), _) => prepare_expr_for_expected_profiled(expr, expected, source, profile),
        (None, _) => Ok(expr),
    }
}

pub(super) fn attach_forced_effect_profiled(
    expr: Expr,
    profile: &mut RuntimeAdapterProfile,
) -> Expr {
    match expr_forced_effect(&expr) {
        Some(effect) => {
            let effect = project_runtime_effect(&effect);
            if should_thunk_effect(&effect) {
                profile.forced_effect_thunk += 1;
                attach_expr_effect(expr, effect)
            } else {
                expr
            }
        }
        _ => expr,
    }
}

pub(super) fn attach_expr_effect(expr: Expr, effect: core_ir::Type) -> Expr {
    match expr.ty.clone() {
        RuntimeType::Thunk {
            effect: existing,
            value,
        } => {
            let effect = project_runtime_effect(&merge_effect_rows(effect, existing));
            let ty = RuntimeType::thunk(effect.clone(), (*value).clone());
            let kind = match expr.kind {
                ExprKind::Thunk {
                    value, expr: inner, ..
                } => ExprKind::Thunk {
                    effect,
                    value,
                    expr: inner,
                },
                other => other,
            };
            Expr { ty, kind }
        }
        value => Expr::typed(
            ExprKind::Thunk {
                effect: effect.clone(),
                value: value.clone(),
                expr: Box::new(expr),
            },
            RuntimeType::thunk(effect, value),
        ),
    }
}

pub(super) fn add_id_to_created_thunks(expr: Expr) -> Expr {
    let ty = expr.ty;
    let kind = match expr.kind {
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            let inner = add_id_to_created_thunks(*expr);
            let thunk = Expr::typed(
                ExprKind::Thunk {
                    effect: effect.clone(),
                    value,
                    expr: Box::new(inner),
                },
                ty,
            );
            return add_id_with_peek_if_needed(thunk, effect);
        }
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        },
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => ExprKind::Apply {
            callee: Box::new(add_id_to_created_thunks(*callee)),
            arg: Box::new(add_id_to_created_thunks(*arg)),
            evidence,
            instantiation,
        },
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => ExprKind::If {
            cond: Box::new(add_id_to_created_thunks(*cond)),
            then_branch: Box::new(add_id_to_created_thunks(*then_branch)),
            else_branch: Box::new(add_id_to_created_thunks(*else_branch)),
            evidence,
        },
        ExprKind::Tuple(items) => {
            ExprKind::Tuple(items.into_iter().map(add_id_to_created_thunks).collect())
        }
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| RecordExprField {
                    name: field.name,
                    value: add_id_to_created_thunks(field.value),
                })
                .collect(),
            spread: spread.map(|spread| match spread {
                RecordSpreadExpr::Head(expr) => {
                    RecordSpreadExpr::Head(Box::new(add_id_to_created_thunks(*expr)))
                }
                RecordSpreadExpr::Tail(expr) => {
                    RecordSpreadExpr::Tail(Box::new(add_id_to_created_thunks(*expr)))
                }
            }),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(add_id_to_created_thunks(*value))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(add_id_to_created_thunks(*base)),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(add_id_to_created_thunks(*scrutinee)),
            arms: arms
                .into_iter()
                .map(|arm| MatchArm {
                    pattern: arm.pattern,
                    guard: arm.guard.map(add_id_to_created_thunks),
                    body: add_id_to_created_thunks(arm.body),
                })
                .collect(),
            evidence,
        },
        ExprKind::Block { stmts, tail } => ExprKind::Block {
            stmts: stmts
                .into_iter()
                .map(|stmt| match stmt {
                    Stmt::Let { pattern, value } => Stmt::Let {
                        pattern,
                        value: add_id_to_created_thunks(value),
                    },
                    Stmt::Expr(expr) => Stmt::Expr(add_id_to_created_thunks(expr)),
                    Stmt::Module { def, body } => Stmt::Module {
                        def,
                        body: add_id_to_created_thunks(body),
                    },
                })
                .collect(),
            tail: tail.map(|tail| Box::new(add_id_to_created_thunks(*tail))),
        },
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => ExprKind::Handle {
            body: Box::new(add_id_to_created_thunks(*body)),
            arms: arms
                .into_iter()
                .map(|arm| HandleArm {
                    effect: arm.effect,
                    payload: arm.payload,
                    resume: arm.resume,
                    guard: arm.guard.map(add_id_to_created_thunks),
                    body: add_id_to_created_thunks(arm.body),
                })
                .collect(),
            evidence,
            handler,
        },
        ExprKind::BindHere { expr } => ExprKind::BindHere {
            expr: Box::new(add_id_to_created_thunks(*expr)),
        },
        ExprKind::LocalPushId { id, body } => ExprKind::LocalPushId {
            id,
            body: Box::new(add_id_to_created_thunks(*body)),
        },
        ExprKind::FindId { id } => ExprKind::FindId { id },
        ExprKind::AddId { id, allowed, thunk } => ExprKind::AddId {
            id,
            allowed,
            thunk: Box::new(add_id_to_created_thunks(*thunk)),
        },
        ExprKind::Coerce { from, to, expr } => ExprKind::Coerce {
            from,
            to,
            expr: Box::new(add_id_to_created_thunks(*expr)),
        },
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(add_id_to_created_thunks(*expr)),
        },
        kind @ (ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId) => kind,
    };
    Expr { ty, kind }
}

pub(super) fn add_id_with_peek_if_needed(thunk: Expr, allowed: core_ir::Type) -> Expr {
    let allowed = project_runtime_effect(&allowed);
    if !should_thunk_effect(&allowed) {
        return thunk;
    }
    Expr::typed(
        ExprKind::AddId {
            id: EffectIdRef::Peek,
            allowed,
            thunk: Box::new(thunk.clone()),
        },
        thunk.ty,
    )
}

pub(super) fn contains_peek_add_id(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::AddId {
            id: EffectIdRef::Peek,
            ..
        } => true,
        ExprKind::Lambda { .. } => false,
        ExprKind::Apply { callee, arg, .. } => {
            contains_peek_add_id(callee) || contains_peek_add_id(arg)
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            ..
        } => {
            contains_peek_add_id(cond)
                || contains_peek_add_id(then_branch)
                || contains_peek_add_id(else_branch)
        }
        ExprKind::Tuple(items) => items.iter().any(contains_peek_add_id),
        ExprKind::Record { fields, spread } => {
            fields
                .iter()
                .any(|field| contains_peek_add_id(&field.value))
                || spread.as_ref().is_some_and(|spread| match spread {
                    RecordSpreadExpr::Head(expr) | RecordSpreadExpr::Tail(expr) => {
                        contains_peek_add_id(expr)
                    }
                })
        }
        ExprKind::Variant { value, .. } => value.as_deref().is_some_and(contains_peek_add_id),
        ExprKind::Select { base, .. } => contains_peek_add_id(base),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            contains_peek_add_id(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(contains_peek_add_id)
                        || contains_peek_add_id(&arm.body)
                })
        }
        ExprKind::Block { stmts, tail } => {
            stmts.iter().any(|stmt| match stmt {
                Stmt::Let { value, .. } | Stmt::Expr(value) => contains_peek_add_id(value),
                Stmt::Module { body, .. } => contains_peek_add_id(body),
            }) || tail.as_deref().is_some_and(contains_peek_add_id)
        }
        ExprKind::Handle { body, arms, .. } => {
            contains_peek_add_id(body)
                || arms.iter().any(|arm| {
                    arm.guard.as_ref().is_some_and(contains_peek_add_id)
                        || contains_peek_add_id(&arm.body)
                })
        }
        ExprKind::BindHere { expr }
        | ExprKind::Thunk { expr, .. }
        | ExprKind::Coerce { expr, .. }
        | ExprKind::Pack { expr, .. } => contains_peek_add_id(expr),
        ExprKind::LocalPushId { body, .. } => contains_peek_add_id(body),
        ExprKind::AddId { thunk, .. } => contains_peek_add_id(thunk),
        ExprKind::Var(_)
        | ExprKind::EffectOp(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Lit(_)
        | ExprKind::PeekId
        | ExprKind::FindId { .. } => false,
    }
}
