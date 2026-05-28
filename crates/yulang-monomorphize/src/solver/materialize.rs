//! Substitution application — turning a graph solution into concrete IR.
//!
//! Given `[TypeSubstitution]` produced by the graph solver, materialize:
//!   - `Expr` trees, with optional `expected` runtime type to thread Thunk
//!     boundaries through (`materialize_expr_with_expected`)
//!   - `Stmt` / `Pattern` / `RecordSpreadExpr` children
//!   - evidence side-information (`materialize_apply_evidence`,
//!     `materialize_principal_elaboration_plan`, `materialize_join_evidence`,
//!     `materialize_type_bounds`)
//!   - apply-argument shape adjustments (`materialize_apply_arg`) that adapt
//!     value/thunk boundaries based on the expected type at the call site.
//!
//! Type-level materialization (`materialize_core_type`, `materialize_runtime_type`)
//! lives in `graph.rs`; this module is the expression-level counterpart.

use yulang_runtime_ir::{
    FinalizedExpr as Expr, FinalizedExprKind as ExprKind, RuntimeType, TypeInstantiation,
    TypeSubstitution,
};
use yulang_typed_ir as typed_ir;

use crate::{
    graph::should_thunk_effect,
    graph::{runtime_type_from_core_value, runtime_type_from_core_value_and_effect},
    materialize_core_type, materialize_runtime_type,
};

pub(crate) fn materialize_expr(expr: Expr, substitutions: &[typed_ir::TypeSubstitution]) -> Expr {
    materialize_expr_with_expected(expr, substitutions, None)
}

pub(crate) fn materialize_expr_with_expected(
    expr: Expr,
    substitutions: &[typed_ir::TypeSubstitution],
    expected: Option<&RuntimeType>,
) -> Expr {
    let ty = materialize_runtime_type(expr.ty, substitutions);
    let kind = match expr.kind {
        ExprKind::Var(path) => ExprKind::Var(path),
        ExprKind::EffectOp(path) => ExprKind::EffectOp(path),
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(op),
        ExprKind::Lit(lit) => {
            return Expr::typed(ExprKind::Lit(lit.clone()), literal_runtime_type(&lit));
        }
        ExprKind::Lambda {
            param,
            param_effect_annotation,
            param_function_allowed_effects,
            body,
        } => {
            let outer_ty = expected
                .filter(|expected| matches!(expected, RuntimeType::Fun { .. }))
                .cloned()
                .unwrap_or(ty);
            let outer_ty =
                materialize_lambda_param_effect(outer_ty, param_effect_annotation.as_ref());
            let body_expected = match &outer_ty {
                RuntimeType::Fun { ret, .. } => Some((**ret).clone()),
                _ => None,
            };
            let body = materialize_expr_with_expected(*body, substitutions, body_expected.as_ref());
            let kind = ExprKind::Lambda {
                param,
                param_effect_annotation,
                param_function_allowed_effects,
                body: Box::new(body),
            };
            return Expr::typed(kind, outer_ty);
        }
        ExprKind::Apply {
            callee,
            arg,
            evidence,
            instantiation,
        } => {
            let evidence =
                evidence.map(|evidence| materialize_apply_evidence(evidence, substitutions));
            let instantiation = instantiation
                .map(|instantiation| materialize_type_instantiation(instantiation, substitutions));
            let callee = materialize_expr(*callee, substitutions);
            let expected_arg = materialized_runtime_callee_arg(&callee.ty)
                .or_else(|| evidence.as_ref().and_then(materialized_apply_expected_arg));
            let kind = ExprKind::Apply {
                callee: Box::new(callee),
                arg: Box::new(materialize_apply_arg(
                    *arg,
                    substitutions,
                    expected_arg.as_ref(),
                )),
                evidence,
                instantiation,
            };
            let ty = materialized_apply_result_type(ty, &kind);
            return Expr::typed(kind, ty);
        }
        ExprKind::Tuple(items) => ExprKind::Tuple(
            items
                .into_iter()
                .map(|item| materialize_expr(item, substitutions))
                .collect(),
        ),
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
            evidence,
        } => {
            let evidence =
                evidence.map(|evidence| materialize_join_evidence(evidence, substitutions));
            let branch_expected = materialized_join_expected(evidence.as_ref(), expected);
            ExprKind::If {
                cond: Box::new(materialize_expr(*cond, substitutions)),
                then_branch: Box::new(materialize_expr_to_expected(
                    *then_branch,
                    substitutions,
                    branch_expected.as_ref(),
                )),
                else_branch: Box::new(materialize_expr_to_expected(
                    *else_branch,
                    substitutions,
                    branch_expected.as_ref(),
                )),
                evidence,
            }
        }
        ExprKind::Record { fields, spread } => ExprKind::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::FinalizedRecordExprField {
                    name: field.name,
                    value: materialize_expr(field.value, substitutions),
                })
                .collect(),
            spread: spread.map(|spread| materialize_record_spread_expr(spread, substitutions)),
        },
        ExprKind::Variant { tag, value } => ExprKind::Variant {
            tag,
            value: value.map(|value| Box::new(materialize_expr(*value, substitutions))),
        },
        ExprKind::Select { base, field } => ExprKind::Select {
            base: Box::new(force_core_value_expr(materialize_expr(
                *base,
                substitutions,
            ))),
            field,
        },
        ExprKind::Match {
            scrutinee,
            arms,
            evidence,
        } => ExprKind::Match {
            scrutinee: Box::new(materialize_expr(*scrutinee, substitutions)),
            arms: arms
                .into_iter()
                .map(|arm| materialize_match_arm(arm, substitutions))
                .collect(),
            evidence: materialize_join_evidence(evidence, substitutions),
        },
        ExprKind::Block { stmts, tail } => {
            let stmts = stmts
                .into_iter()
                .map(|stmt| materialize_stmt(stmt, substitutions))
                .collect();
            let tail = tail.map(|tail| {
                Box::new(materialize_expr_with_expected(
                    *tail,
                    substitutions,
                    expected,
                ))
            });
            let block_ty = tail
                .as_ref()
                .map(|tail| tail.ty.clone())
                .unwrap_or_else(|| RuntimeType::Value(super::unit_type()));
            return Expr::typed(ExprKind::Block { stmts, tail }, block_ty);
        }
        ExprKind::Handle {
            body,
            arms,
            evidence,
            handler,
        } => {
            let evidence = materialize_join_evidence(evidence, substitutions);
            let result = expected_core_type(expected).unwrap_or(evidence.result);
            let expected_result = runtime_type_from_core_value(result.clone());
            let handler = materialize_handle_effect(handler, substitutions);
            let body = materialize_handle_body(*body, substitutions, &handler);
            let kind = ExprKind::Handle {
                body: Box::new(body),
                arms: arms
                    .into_iter()
                    .map(|arm| {
                        materialize_handle_arm(arm, substitutions, &expected_result, &handler)
                    })
                    .collect(),
                handler,
                evidence: yulang_runtime_ir::JoinEvidence {
                    result: result.clone(),
                },
            };
            return Expr::typed(kind, expected_result);
        }
        ExprKind::BindHere { expr } => {
            let body_expected =
                expected.filter(|expected| !matches!(expected, RuntimeType::Thunk { .. }));
            let expr = materialize_expr_with_expected(*expr, substitutions, body_expected);
            let value = match &expr.ty {
                RuntimeType::Thunk { value, .. } => (**value).clone(),
                _ if super::runtime_type_has_unknown(&expr.ty) => {
                    body_expected.cloned().unwrap_or_else(|| ty.clone())
                }
                _ => return expr,
            };
            let kind = ExprKind::BindHere {
                expr: Box::new(expr),
            };
            return Expr::typed(kind, value);
        }
        ExprKind::Thunk {
            effect,
            value,
            expr,
        } => {
            let (effect, expected_value) = match expected {
                Some(RuntimeType::Thunk { effect, value }) => {
                    (effect.clone(), Some((**value).clone()))
                }
                Some(_) | None => (materialize_core_type(effect, substitutions), None),
            };
            let value =
                expected_value.unwrap_or_else(|| materialize_runtime_type(value, substitutions));
            let kind = ExprKind::Thunk {
                effect: effect.clone(),
                value: value.clone(),
                expr: Box::new(materialize_expr_with_expected(
                    *expr,
                    substitutions,
                    Some(&value),
                )),
            };
            return Expr::typed(
                kind,
                RuntimeType::Thunk {
                    effect,
                    value: Box::new(value),
                },
            );
        }
        ExprKind::LocalPushId { id, body } => {
            let body = materialize_expr_with_expected(*body, substitutions, expected);
            let ty = body.ty.clone();
            let kind = ExprKind::LocalPushId {
                id,
                body: Box::new(body),
            };
            return Expr::typed(kind, ty);
        }
        ExprKind::PeekId => ExprKind::PeekId,
        ExprKind::FindId { id } => ExprKind::FindId { id },
        ExprKind::AddId {
            id,
            allowed,
            active,
            thunk,
        } => {
            let allowed = materialize_core_type(allowed, substitutions);
            let expected_thunk = add_id_expected_thunk(
                &thunk,
                materialize_runtime_type(thunk.ty.clone(), substitutions),
                &allowed,
                substitutions,
            );
            let thunk = materialize_expr_to_expected(*thunk, substitutions, Some(&expected_thunk));
            let ty = thunk.ty.clone();
            let kind = ExprKind::AddId {
                id,
                allowed,
                active,
                thunk: Box::new(thunk),
            };
            return Expr::typed(kind, ty);
        }
        ExprKind::Coerce { from, to, expr } => {
            let to = expected_core_type(expected)
                .unwrap_or_else(|| materialize_core_type(to, substitutions));
            let expected_runtime = runtime_type_from_core_value(to.clone());
            let expr = materialize_expr(*expr, substitutions);
            let expr = adapt_expr_to_expected_runtime(expr, &expected_runtime);
            let materialized_from = materialize_core_type(from, substitutions);
            let from = match &expr.ty {
                RuntimeType::Unknown => materialized_from,
                _ => super::runtime_type_to_core(expr.ty.clone()),
            };
            if from == to && super::runtime_type_to_core(expr.ty.clone()) == to {
                return expr;
            }
            let kind = ExprKind::Coerce {
                from,
                to: to.clone(),
                expr: Box::new(expr),
            };
            return Expr::typed(kind, runtime_type_from_core_value(to));
        }
        ExprKind::Pack { var, expr } => ExprKind::Pack {
            var,
            expr: Box::new(materialize_expr(*expr, substitutions)),
        },
    };
    Expr::typed(kind, ty)
}

fn materialize_type_instantiation(
    instantiation: TypeInstantiation,
    substitutions: &[typed_ir::TypeSubstitution],
) -> TypeInstantiation {
    TypeInstantiation {
        target: instantiation.target,
        args: instantiation
            .args
            .into_iter()
            .map(|arg| TypeSubstitution {
                var: arg.var,
                ty: materialize_core_type(arg.ty, substitutions),
            })
            .collect(),
    }
}

pub(crate) fn materialize_expr_in_place(
    expr: &mut Expr,
    substitutions: &[typed_ir::TypeSubstitution],
) {
    *expr = materialize_expr(expr.clone(), substitutions);
}

fn materialize_stmt(
    stmt: yulang_runtime_ir::FinalizedStmt,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::FinalizedStmt {
    match stmt {
        yulang_runtime_ir::FinalizedStmt::Let { pattern, value } => {
            yulang_runtime_ir::FinalizedStmt::Let {
                pattern: materialize_pattern(pattern, substitutions),
                value: materialize_expr(value, substitutions),
            }
        }
        yulang_runtime_ir::FinalizedStmt::Expr(expr) => {
            yulang_runtime_ir::FinalizedStmt::Expr(materialize_expr(expr, substitutions))
        }
        yulang_runtime_ir::FinalizedStmt::Module { def, body } => {
            yulang_runtime_ir::FinalizedStmt::Module {
                def,
                body: materialize_expr(body, substitutions),
            }
        }
    }
}

fn materialize_pattern(
    pattern: yulang_runtime_ir::FinalizedPattern,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::FinalizedPattern {
    use yulang_runtime_ir::FinalizedPattern as Pattern;

    match pattern {
        Pattern::Wildcard { ty } => Pattern::Wildcard {
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Bind { name, ty } => Pattern::Bind {
            name,
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Lit { lit, ty } => Pattern::Lit {
            lit,
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Tuple { items, ty } => Pattern::Tuple {
            items: items
                .into_iter()
                .map(|item| materialize_pattern(item, substitutions))
                .collect(),
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::List {
            prefix,
            spread,
            suffix,
            ty,
        } => Pattern::List {
            prefix: prefix
                .into_iter()
                .map(|item| materialize_pattern(item, substitutions))
                .collect(),
            spread: spread.map(|spread| Box::new(materialize_pattern(*spread, substitutions))),
            suffix: suffix
                .into_iter()
                .map(|item| materialize_pattern(item, substitutions))
                .collect(),
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Record { fields, spread, ty } => Pattern::Record {
            fields: fields
                .into_iter()
                .map(|field| yulang_runtime_ir::FinalizedRecordPatternField {
                    name: field.name,
                    pattern: materialize_pattern(field.pattern, substitutions),
                    default: field
                        .default
                        .map(|expr| materialize_expr(expr, substitutions)),
                })
                .collect(),
            spread,
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Variant { tag, value, ty } => Pattern::Variant {
            tag,
            value: value.map(|value| Box::new(materialize_pattern(*value, substitutions))),
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::Or { left, right, ty } => Pattern::Or {
            left: Box::new(materialize_pattern(*left, substitutions)),
            right: Box::new(materialize_pattern(*right, substitutions)),
            ty: materialize_runtime_type(ty, substitutions),
        },
        Pattern::As { pattern, name, ty } => Pattern::As {
            pattern: Box::new(materialize_pattern(*pattern, substitutions)),
            name,
            ty: materialize_runtime_type(ty, substitutions),
        },
    }
}

fn materialize_record_spread_expr(
    spread: yulang_runtime_ir::FinalizedRecordSpreadExpr,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::FinalizedRecordSpreadExpr {
    match spread {
        yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(expr) => {
            yulang_runtime_ir::FinalizedRecordSpreadExpr::Head(Box::new(materialize_expr(
                *expr,
                substitutions,
            )))
        }
        yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(expr) => {
            yulang_runtime_ir::FinalizedRecordSpreadExpr::Tail(Box::new(materialize_expr(
                *expr,
                substitutions,
            )))
        }
    }
}

fn materialize_match_arm(
    arm: yulang_runtime_ir::FinalizedMatchArm,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::FinalizedMatchArm {
    yulang_runtime_ir::FinalizedMatchArm {
        pattern: materialize_pattern(arm.pattern, substitutions),
        guard: arm
            .guard
            .map(|guard| materialize_expr(guard, substitutions)),
        body: materialize_expr(arm.body, substitutions),
    }
}

fn materialize_handle_arm(
    arm: yulang_runtime_ir::FinalizedHandleArm,
    substitutions: &[typed_ir::TypeSubstitution],
    expected: &RuntimeType,
    handler: &yulang_runtime_ir::HandleEffect,
) -> yulang_runtime_ir::FinalizedHandleArm {
    yulang_runtime_ir::FinalizedHandleArm {
        effect: materialize_handle_arm_effect(arm.effect, handler),
        payload: materialize_pattern(arm.payload, substitutions),
        resume: arm
            .resume
            .map(|resume| yulang_runtime_ir::FinalizedResumeBinding {
                name: resume.name,
                ty: materialize_runtime_type(resume.ty, substitutions),
            }),
        guard: arm
            .guard
            .map(|guard| materialize_expr(guard, substitutions)),
        body: materialize_expr_with_expected(arm.body, substitutions, Some(expected)),
    }
}

fn materialize_handle_arm_effect(
    effect: typed_ir::Path,
    handler: &yulang_runtime_ir::HandleEffect,
) -> typed_ir::Path {
    let Some((operation, handled_effect)) = effect.segments.split_last() else {
        return effect;
    };
    if handled_effect.is_empty() {
        return effect;
    }
    let matches = handler
        .consumes
        .iter()
        .filter(|consumed| consumed.segments.ends_with(handled_effect))
        .collect::<Vec<_>>();
    let [consumed] = matches.as_slice() else {
        return effect;
    };
    let mut segments = consumed.segments.clone();
    segments.push((*operation).clone());
    typed_ir::Path::new(segments)
}

fn materialize_join_evidence(
    evidence: yulang_runtime_ir::JoinEvidence,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::JoinEvidence {
    yulang_runtime_ir::JoinEvidence {
        result: materialize_core_type(evidence.result, substitutions),
    }
}

fn materialized_join_expected(
    evidence: Option<&yulang_runtime_ir::JoinEvidence>,
    expected: Option<&RuntimeType>,
) -> Option<RuntimeType> {
    expected
        .filter(|expected| should_materialize_expected_runtime(expected))
        .cloned()
        .or_else(|| {
            evidence
                .map(|evidence| runtime_type_from_core_value(evidence.result.clone()))
                .filter(should_materialize_expected_runtime)
        })
}

fn materialize_apply_evidence(
    evidence: typed_ir::ApplyEvidence,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::ApplyEvidence {
    typed_ir::ApplyEvidence {
        callee_source_edge: evidence.callee_source_edge,
        arg_source_edge: evidence.arg_source_edge,
        callee: materialize_type_bounds(evidence.callee, substitutions),
        expected_callee: evidence
            .expected_callee
            .map(|bounds| materialize_type_bounds(bounds, substitutions)),
        arg: materialize_type_bounds(evidence.arg, substitutions),
        expected_arg: evidence
            .expected_arg
            .map(|bounds| materialize_type_bounds(bounds, substitutions)),
        result: materialize_type_bounds(evidence.result, substitutions),
        principal_callee: evidence
            .principal_callee
            .map(|ty| materialize_core_type(ty, substitutions)),
        substitutions: evidence
            .substitutions
            .into_iter()
            .map(|subst| typed_ir::TypeSubstitution {
                var: subst.var,
                ty: materialize_core_type(subst.ty, substitutions),
            })
            .collect(),
        substitution_candidates: evidence
            .substitution_candidates
            .into_iter()
            .map(|candidate| typed_ir::PrincipalSubstitutionCandidate {
                var: candidate.var,
                relation: candidate.relation,
                ty: materialize_core_type(candidate.ty, substitutions),
                source_edge: candidate.source_edge,
                path: candidate.path,
            })
            .collect(),
        role_method: evidence.role_method,
        principal_elaboration: evidence
            .principal_elaboration
            .map(|plan| materialize_principal_elaboration_plan(plan, substitutions)),
    }
}

fn materialize_principal_elaboration_plan(
    plan: typed_ir::PrincipalElaborationPlan,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::PrincipalElaborationPlan {
    typed_ir::PrincipalElaborationPlan {
        target: plan.target,
        principal_callee: materialize_core_type(plan.principal_callee, substitutions),
        substitutions: plan
            .substitutions
            .into_iter()
            .map(|subst| typed_ir::TypeSubstitution {
                var: subst.var,
                ty: materialize_core_type(subst.ty, substitutions),
            })
            .collect(),
        args: plan
            .args
            .into_iter()
            .map(|arg| typed_ir::PrincipalElaborationArg {
                index: arg.index,
                intrinsic: materialize_type_bounds(arg.intrinsic, substitutions),
                contextual: arg
                    .contextual
                    .map(|bounds| materialize_type_bounds(bounds, substitutions)),
                expected_runtime: arg
                    .expected_runtime
                    .map(|ty| materialize_core_type(ty, substitutions)),
                source_edge: arg.source_edge,
            })
            .collect(),
        result: typed_ir::PrincipalElaborationResult {
            intrinsic: materialize_type_bounds(plan.result.intrinsic, substitutions),
            contextual: plan
                .result
                .contextual
                .map(|bounds| materialize_type_bounds(bounds, substitutions)),
            expected_runtime: plan
                .result
                .expected_runtime
                .map(|ty| materialize_core_type(ty, substitutions)),
        },
        adapters: plan
            .adapters
            .into_iter()
            .map(|adapter| typed_ir::PrincipalAdapterHole {
                kind: adapter.kind,
                source_edge: adapter.source_edge,
                actual: materialize_core_type(adapter.actual, substitutions),
                expected: materialize_core_type(adapter.expected, substitutions),
            })
            .collect(),
        complete: plan.complete,
        incomplete_reasons: plan.incomplete_reasons,
    }
}

pub(crate) fn materialize_type_bounds(
    bounds: typed_ir::TypeBounds,
    substitutions: &[typed_ir::TypeSubstitution],
) -> typed_ir::TypeBounds {
    typed_ir::TypeBounds {
        lower: bounds
            .lower
            .map(|ty| Box::new(materialize_core_type(*ty, substitutions))),
        upper: bounds
            .upper
            .map(|ty| Box::new(materialize_core_type(*ty, substitutions))),
    }
}

fn materialized_apply_expected_arg(evidence: &typed_ir::ApplyEvidence) -> Option<RuntimeType> {
    materialized_apply_expected_callee_arg(evidence).or_else(|| {
        evidence
            .expected_arg
            .as_ref()
            .and_then(super::apply_spine::type_from_bounds)
            .map(runtime_type_from_core_value)
            .filter(should_materialize_expected_runtime)
    })
}

fn materialized_apply_result_type(fallback: RuntimeType, kind: &ExprKind) -> RuntimeType {
    if let ExprKind::Apply { callee, .. } = kind
        && let Some(ret) = materialized_runtime_callee_ret(&callee.ty)
    {
        return ret;
    }
    let ExprKind::Apply {
        evidence: Some(evidence),
        ..
    } = kind
    else {
        return fallback;
    };
    let Some(value) =
        super::apply_spine::type_from_bounds(&evidence.result).filter(super::core_type_is_closed)
    else {
        return fallback;
    };
    let effect = materialized_apply_return_effect(evidence).unwrap_or(typed_ir::Type::Never);
    runtime_type_from_core_value_and_effect(value, effect)
}

fn materialized_apply_return_effect(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    materialized_apply_return_callee(evidence).and_then(|ty| match ty {
        typed_ir::Type::Fun { ret_effect, .. } => {
            let effect = *ret_effect;
            super::core_type_is_closed(&effect).then_some(effect)
        }
        _ => None,
    })
}

fn materialized_apply_return_callee(evidence: &typed_ir::ApplyEvidence) -> Option<typed_ir::Type> {
    evidence
        .expected_callee
        .as_ref()
        .and_then(super::apply_spine::type_from_bounds)
        .or_else(|| super::apply_spine::type_from_bounds(&evidence.callee))
}

fn materialize_handle_body(
    body: Expr,
    substitutions: &[typed_ir::TypeSubstitution],
    handler: &yulang_runtime_ir::HandleEffect,
) -> Expr {
    let body = materialize_expr(body, substitutions);
    if handler.consumes.is_empty() || matches!(body.ty, RuntimeType::Thunk { .. }) {
        return body;
    }
    let effect = handler
        .residual_before
        .clone()
        .filter(should_thunk_effect)
        .unwrap_or_else(|| typed_ir::Type::Row {
            items: handler
                .consumes
                .iter()
                .cloned()
                .map(|path| typed_ir::Type::Named {
                    path,
                    args: Vec::new(),
                })
                .collect(),
            tail: Box::new(typed_ir::Type::Never),
        });
    let value = body.ty.clone();
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value.clone(),
            expr: Box::new(body),
        },
        RuntimeType::Thunk {
            effect,
            value: Box::new(value),
        },
    )
}

fn add_id_expected_thunk(
    expr: &Expr,
    ty: RuntimeType,
    allowed: &typed_ir::Type,
    substitutions: &[typed_ir::TypeSubstitution],
) -> RuntimeType {
    match ty {
        RuntimeType::Thunk { .. } => ty,
        value => {
            let (effect, value) = match &expr.kind {
                ExprKind::Thunk {
                    effect,
                    value: thunk_value,
                    ..
                } => (
                    materialize_core_type(effect.clone(), substitutions),
                    materialize_runtime_type(thunk_value.clone(), substitutions),
                ),
                _ => (allowed.clone(), value),
            };
            RuntimeType::Thunk {
                effect,
                value: Box::new(value),
            }
        }
    }
}

fn materialize_lambda_param_effect(
    ty: RuntimeType,
    annotation: Option<&typed_ir::ParamEffectAnnotation>,
) -> RuntimeType {
    let Some(annotation) = annotation else {
        return ty;
    };
    let RuntimeType::Fun { param, ret } = ty else {
        return ty;
    };
    let param = match *param {
        RuntimeType::Thunk { .. } => param,
        value => Box::new(RuntimeType::Thunk {
            effect: param_effect_annotation_effect(annotation),
            value: Box::new(value),
        }),
    };
    RuntimeType::Fun { param, ret }
}

fn materialized_apply_expected_callee_arg(
    evidence: &typed_ir::ApplyEvidence,
) -> Option<RuntimeType> {
    evidence
        .expected_callee
        .as_ref()
        .and_then(super::apply_spine::type_from_bounds)
        .or_else(|| super::apply_spine::type_from_bounds(&evidence.callee))
        .and_then(|ty| match ty {
            typed_ir::Type::Fun {
                param,
                param_effect,
                ..
            } => Some(runtime_type_from_core_value_and_effect(
                *param,
                *param_effect,
            )),
            _ => None,
        })
        .filter(should_materialize_expected_runtime)
}

fn param_effect_annotation_effect(annotation: &typed_ir::ParamEffectAnnotation) -> typed_ir::Type {
    match annotation {
        typed_ir::ParamEffectAnnotation::Wildcard => typed_ir::Type::Any,
        typed_ir::ParamEffectAnnotation::Region(name) => typed_ir::Type::Named {
            path: typed_ir::Path::from_name(name.clone()),
            args: Vec::new(),
        },
    }
}

fn materialized_runtime_callee_arg(ty: &RuntimeType) -> Option<RuntimeType> {
    let arg = match ty {
        RuntimeType::Fun { param, .. } => param.as_ref().clone(),
        RuntimeType::Value(typed_ir::Type::Fun {
            param,
            param_effect,
            ..
        }) => runtime_type_from_core_value_and_effect(
            param.as_ref().clone(),
            param_effect.as_ref().clone(),
        ),
        RuntimeType::Unknown | RuntimeType::Value(_) | RuntimeType::Thunk { .. } => return None,
    };
    should_materialize_expected_runtime(&arg).then_some(arg)
}

fn materialized_runtime_callee_ret(ty: &RuntimeType) -> Option<RuntimeType> {
    let ret = match ty {
        RuntimeType::Fun { ret, .. } => ret.as_ref().clone(),
        RuntimeType::Value(typed_ir::Type::Fun {
            ret_effect, ret, ..
        }) => runtime_type_from_core_value_and_effect(
            ret.as_ref().clone(),
            ret_effect.as_ref().clone(),
        ),
        RuntimeType::Unknown | RuntimeType::Value(_) | RuntimeType::Thunk { .. } => return None,
    };
    super::runtime_type_is_closed(&ret).then_some(ret)
}

fn should_materialize_expected_runtime(ty: &RuntimeType) -> bool {
    match ty {
        RuntimeType::Value(ty) => should_materialize_expected_core(ty),
        RuntimeType::Thunk { effect, value } => {
            should_thunk_effect(effect)
                && super::runtime_type_is_closed(value)
                && should_materialize_expected_core(&super::runtime_type_to_core(
                    value.as_ref().clone(),
                ))
        }
        RuntimeType::Fun { .. } => super::runtime_type_is_closed(ty),
        RuntimeType::Unknown => false,
    }
}

fn should_materialize_expected_core(ty: &typed_ir::Type) -> bool {
    super::core_type_is_closed(ty) && !matches!(ty, typed_ir::Type::Any | typed_ir::Type::Never)
}

fn materialize_apply_arg(
    arg: Expr,
    substitutions: &[typed_ir::TypeSubstitution],
    expected: Option<&RuntimeType>,
) -> Expr {
    materialize_expr_to_expected(arg, substitutions, expected)
}

fn materialize_expr_to_expected(
    expr: Expr,
    substitutions: &[typed_ir::TypeSubstitution],
    expected: Option<&RuntimeType>,
) -> Expr {
    let expr = materialize_expr_with_expected(expr, substitutions, expected);
    let Some(expected) = expected else {
        return expr;
    };
    adapt_expr_to_expected_runtime(expr, expected)
}

pub(crate) fn force_core_value_expr(expr: Expr) -> Expr {
    let value = match &expr.ty {
        RuntimeType::Thunk { value, .. } => value.as_ref().clone(),
        _ => return expr,
    };
    Expr::typed(
        ExprKind::BindHere {
            expr: Box::new(expr),
        },
        value,
    )
}

fn literal_runtime_type(lit: &typed_ir::Lit) -> RuntimeType {
    RuntimeType::Value(typed_ir::Type::Named {
        path: match lit {
            typed_ir::Lit::Int(_) => primitive_path(&["int"]),
            typed_ir::Lit::Float(_) => primitive_path(&["float"]),
            typed_ir::Lit::String(_) => primitive_path(&["std", "str", "str"]),
            typed_ir::Lit::Bool(_) => primitive_path(&["bool"]),
            typed_ir::Lit::Unit => primitive_path(&["unit"]),
        },
        args: Vec::new(),
    })
}

fn primitive_path(segments: &[&str]) -> typed_ir::Path {
    typed_ir::Path::new(
        segments
            .iter()
            .map(|segment| typed_ir::Name((*segment).to_string()))
            .collect(),
    )
}

fn adapt_expr_to_expected_runtime(expr: Expr, expected: &RuntimeType) -> Expr {
    if let RuntimeType::Thunk { effect, value } = expected {
        return materialize_value_to_thunk(expr, effect, value);
    }
    let Some(expected) = expected_core_type(Some(expected)) else {
        return expr;
    };
    materialize_thunk_to_value_or_coerce(expr, expected)
}

fn materialize_thunk_to_value_or_coerce(expr: Expr, expected: typed_ir::Type) -> Expr {
    if matches!(expr.ty, RuntimeType::Thunk { .. }) {
        return expr;
    }
    let actual = super::runtime_type_to_core(expr.ty.clone());
    materialize_value_coerce(expr, actual, expected)
}

fn materialize_value_coerce(expr: Expr, actual: typed_ir::Type, expected: typed_ir::Type) -> Expr {
    if actual == expected || matches!(actual, typed_ir::Type::Unknown) {
        return expr;
    }
    if !super::core_type_is_closed(&actual) || !super::core_type_is_closed(&expected) {
        return expr;
    }
    Expr::typed(
        ExprKind::Coerce {
            from: actual,
            to: expected.clone(),
            expr: Box::new(expr),
        },
        runtime_type_from_core_value(expected),
    )
}

fn materialize_value_to_thunk(arg: Expr, effect: &typed_ir::Type, value: &RuntimeType) -> Expr {
    if matches!(arg.ty, RuntimeType::Thunk { .. }) {
        return arg;
    }
    let expected = super::runtime_type_to_core(value.clone());
    let actual = super::runtime_type_to_core(arg.ty.clone());
    if !super::core_type_is_closed(&actual) || !super::core_type_is_closed(&expected) {
        return arg;
    }
    let expr = materialize_value_coerce(arg, actual, expected);
    Expr::typed(
        ExprKind::Thunk {
            effect: effect.clone(),
            value: value.clone(),
            expr: Box::new(expr),
        },
        RuntimeType::Thunk {
            effect: effect.clone(),
            value: Box::new(value.clone()),
        },
    )
}

fn materialize_handle_effect(
    handler: yulang_runtime_ir::HandleEffect,
    substitutions: &[typed_ir::TypeSubstitution],
) -> yulang_runtime_ir::HandleEffect {
    let residual_before = handler
        .residual_before
        .map(|ty| materialize_core_type(ty, substitutions));
    let residual_after = handler
        .residual_after
        .map(|ty| materialize_core_type(ty, substitutions));
    let consumes = materialize_handle_consumes(
        handler.consumes,
        [residual_before.as_ref(), residual_after.as_ref()],
    );
    yulang_runtime_ir::HandleEffect {
        consumes,
        residual_before,
        residual_after,
    }
}

fn materialize_handle_consumes(
    consumes: Vec<typed_ir::Path>,
    residuals: [Option<&typed_ir::Type>; 2],
) -> Vec<typed_ir::Path> {
    let mut candidates = Vec::new();
    for residual in residuals.into_iter().flatten() {
        collect_effect_named_paths(residual, &mut candidates);
    }
    consumes
        .into_iter()
        .map(|consume| qualify_effect_path_from_candidates(consume, &candidates))
        .collect()
}

fn qualify_effect_path_from_candidates(
    path: typed_ir::Path,
    candidates: &[typed_ir::Path],
) -> typed_ir::Path {
    let matches = candidates
        .iter()
        .filter(|candidate| candidate.segments.ends_with(&path.segments))
        .collect::<Vec<_>>();
    let [candidate] = matches.as_slice() else {
        return path;
    };
    (*candidate).clone()
}

fn collect_effect_named_paths(effect: &typed_ir::Type, out: &mut Vec<typed_ir::Path>) {
    match effect {
        typed_ir::Type::Named { path, .. } => {
            if !out.contains(path) {
                out.push(path.clone());
            }
        }
        typed_ir::Type::Row { items, tail } => {
            for item in items {
                collect_effect_named_paths(item, out);
            }
            collect_effect_named_paths(tail, out);
        }
        typed_ir::Type::Union(items) | typed_ir::Type::Inter(items) => {
            for item in items {
                collect_effect_named_paths(item, out);
            }
        }
        typed_ir::Type::Recursive { body, .. } => collect_effect_named_paths(body, out),
        typed_ir::Type::Unknown
        | typed_ir::Type::Never
        | typed_ir::Type::Any
        | typed_ir::Type::Var(_)
        | typed_ir::Type::Fun { .. }
        | typed_ir::Type::Tuple(_)
        | typed_ir::Type::Record(_)
        | typed_ir::Type::Variant(_) => {}
    }
}

fn expected_core_type(expected: Option<&RuntimeType>) -> Option<typed_ir::Type> {
    match expected {
        Some(RuntimeType::Unknown) | None => None,
        Some(RuntimeType::Value(ty)) => Some(ty.clone()),
        Some(expected) => Some(super::runtime_type_to_core(expected.clone())),
    }
}
