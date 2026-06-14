use crate::profile::ProfileClock as Instant;

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{
    CatchArmKind, ExprKind, PolyVariantOrigin, RecordSpread, TypedExpr, TypedStmt,
};
use crate::diagnostic::{ConstraintCause, ConstraintReason, ExpectedEdgeKind};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Name;
use crate::types::{Neg, Pos};

use super::{
    infix_op_ref, lower_expr, lower_var_assignment, make_app_with_cause, neg_prim_type,
    prefix_op_ref, prim_type, resolve_path_expr_at, suffix_op_ref, unit_expr,
};

/// サフィックスノードを acc に適用して新しい TypedExpr を返す。
pub(super) fn apply_suffix(
    state: &mut LowerState,
    acc: TypedExpr,
    suffix: &SyntaxNode,
) -> TypedExpr {
    let start = Instant::now();
    let result = match suffix.kind() {
        SyntaxKind::Field => apply_field_suffix(state, acc, suffix),
        SyntaxKind::ApplyML => apply_ml_suffix(state, acc, suffix),
        SyntaxKind::ApplyC => apply_c_suffix(state, acc, suffix),
        SyntaxKind::ApplyColon => apply_colon_suffix(state, acc, suffix),
        SyntaxKind::Assign => lower_var_assignment(state, acc, suffix),
        SyntaxKind::InfixNode => apply_infix_suffix(state, acc, suffix),
        SyntaxKind::TypeAnn => apply_type_ann_suffix(state, acc, suffix),
        SyntaxKind::PrefixNode => {
            let op_ref = prefix_op_ref(state, suffix);
            let arg = lazy_operator_arg(state, &op_ref, acc);
            make_app_with_cause(state, op_ref, arg, apply_arg_cause(suffix))
        }
        SyntaxKind::SuffixNode => {
            let op_ref = suffix_op_ref(state, suffix);
            let arg = lazy_operator_arg(state, &op_ref, acc);
            make_app_with_cause(state, op_ref, arg, apply_arg_cause(suffix))
        }
        SyntaxKind::Index => apply_index_suffix(state, acc, suffix),
        _ => acc,
    };
    let elapsed = start.elapsed();
    state.lower_detail.apply_suffix += elapsed;
    match suffix.kind() {
        SyntaxKind::Field => state.lower_detail.apply_suffix_field += elapsed,
        SyntaxKind::ApplyML => state.lower_detail.apply_suffix_apply_ml += elapsed,
        SyntaxKind::ApplyC => state.lower_detail.apply_suffix_apply_c += elapsed,
        SyntaxKind::ApplyColon => state.lower_detail.apply_suffix_apply_colon += elapsed,
        SyntaxKind::Assign => state.lower_detail.apply_suffix_assign += elapsed,
        SyntaxKind::InfixNode => state.lower_detail.apply_suffix_infix += elapsed,
        SyntaxKind::TypeAnn => state.lower_detail.apply_suffix_type_ann += elapsed,
        SyntaxKind::PrefixNode => state.lower_detail.apply_suffix_prefix += elapsed,
        SyntaxKind::SuffixNode => state.lower_detail.apply_suffix_suffix += elapsed,
        SyntaxKind::Index => state.lower_detail.apply_suffix_index += elapsed,
        _ => state.lower_detail.apply_suffix_other += elapsed,
    }
    result
}

fn apply_type_ann_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let Some(type_expr) = suffix
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)
    else {
        return acc;
    };
    let Some(sig) = crate::lower::signature::parse_sig_type_expr(&type_expr) else {
        return acc;
    };
    let cause = ConstraintCause {
        span: Some(type_expr.text_range()),
        reason: ConstraintReason::Annotation,
    };
    let mut vars = state.current_type_scope().cloned().unwrap_or_default();
    let lower = crate::lower::signature::lower_pure_sig_pos_id(state, &sig, &mut vars);
    let mut neg_vars = vars.clone();
    let upper = crate::lower::signature::lower_pure_sig_neg_id(state, &sig, &mut neg_vars);
    let ann_tv = state.fresh_tv();
    state
        .infer
        .constrain_with_cause(lower, Neg::Var(ann_tv), cause.clone());
    state
        .infer
        .constrain_with_cause(Pos::Var(ann_tv), upper, cause.clone());
    state
        .implicit_cast_boundary(acc, ann_tv, ExpectedEdgeKind::Annotation, cause, true)
        .0
}

pub(super) fn apply_synthetic_field_selection(
    state: &mut LowerState,
    acc: TypedExpr,
    name: Name,
    node: &SyntaxNode,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_generated_effect_tv();
    push_deferred_selection(
        state,
        acc,
        node,
        name,
        tv,
        eff,
        false,
        Some(node.text_range()),
    )
}

fn apply_field_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_generated_effect_tv();
    let field = suffix
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::DotField)
        .map(|t| {
            let s = t.text().to_string();
            let field_like_source =
                s.starts_with('.') && suffix.to_string().trim_start().starts_with('.');
            (
                Name(s.trim_start_matches('.').to_string()),
                field_like_source,
                t.text_range(),
            )
        });
    if let Some((name, structural_record_allowed, selection_span)) = field {
        if let ExprKind::Var(def) = &acc.kind {
            if let Some(path) = state.ctx.resolve_field_alias(*def, &name) {
                return resolve_path_expr_at(state, path.segments, Some(suffix.text_range()));
            }
        }
        push_deferred_selection(
            state,
            acc,
            suffix,
            name,
            tv,
            eff,
            structural_record_allowed,
            Some(selection_span),
        )
    } else {
        acc
    }
}

fn apply_ml_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    if matches!(acc.kind, ExprKind::PolyVariant(_, _, _)) {
        return apply_variant_payload_suffix(state, acc, suffix);
    }
    let mut result = acc;
    for child in suffix.children().filter(|c| c.kind() == SyntaxKind::Expr) {
        let arg = lower_expr(state, &child);
        result = make_app_with_cause(
            state,
            result,
            arg,
            ConstraintCause {
                span: Some(suffix.text_range()),
                reason: ConstraintReason::ApplyArg,
            },
        );
    }
    result
}

fn apply_c_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    if matches!(acc.kind, ExprKind::PolyVariant(_, _, _)) {
        return apply_variant_payload_suffix(state, acc, suffix);
    }
    let args: Vec<_> = suffix
        .children()
        .filter(|c| c.kind() == SyntaxKind::Expr)
        .map(|c| lower_expr(state, &c))
        .collect();

    if args.is_empty() {
        let unit = unit_expr(state);
        make_app_with_cause(
            state,
            acc,
            unit,
            ConstraintCause {
                span: Some(suffix.text_range()),
                reason: ConstraintReason::ApplyArg,
            },
        )
    } else {
        let mut result = acc;
        for arg in args {
            result = make_app_with_cause(
                state,
                result,
                arg,
                ConstraintCause {
                    span: Some(suffix.text_range()),
                    reason: ConstraintReason::ApplyArg,
                },
            );
        }
        result
    }
}

fn apply_variant_payload_suffix(
    state: &mut LowerState,
    acc: TypedExpr,
    suffix: &SyntaxNode,
) -> TypedExpr {
    let ExprKind::PolyVariant(tag, mut payloads, origin) = acc.kind else {
        return acc;
    };
    payloads.extend(
        suffix
            .children()
            .filter(|child| child.kind() == SyntaxKind::Expr)
            .map(|child| lower_expr(state, &child)),
    );
    lower_poly_variant_expr(state, tag, payloads, origin)
}

pub(super) fn lower_poly_variant_expr(
    state: &mut LowerState,
    tag: Name,
    payloads: Vec<TypedExpr>,
    origin: PolyVariantOrigin,
) -> TypedExpr {
    let tv = state.fresh_tv();
    let eff = state.fresh_exact_pure_eff_tv();
    for payload in &payloads {
        state.infer.constrain(Pos::Var(payload.eff), Neg::Var(eff));
    }
    state.infer.constrain(
        state.pos_variant(vec![(
            tag.clone(),
            payloads
                .iter()
                .map(|payload| Pos::Var(payload.tv))
                .collect(),
        )]),
        Neg::Var(tv),
    );
    state.infer.constrain(
        Pos::Var(tv),
        Neg::PolyVariant(vec![(
            tag.clone(),
            payloads
                .iter()
                .map(|payload| state.infer.alloc_neg(Neg::Var(payload.tv)))
                .collect(),
        )]),
    );
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::PolyVariant(tag, payloads, origin),
    }
}

fn apply_colon_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let mut result = acc;
    for arg_node in suffix.children().filter(|c| {
        matches!(
            c.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    }) {
        let arg = lower_expr(state, &arg_node);
        result = make_app_with_cause(
            state,
            result,
            arg,
            ConstraintCause {
                span: Some(suffix.text_range()),
                reason: ConstraintReason::ApplyArg,
            },
        );
    }
    result
}

fn apply_infix_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let rhs_node = suffix.children().find(|c| c.kind() == SyntaxKind::Expr);
    if let Some(rhs_node) = rhs_node {
        let rhs = lower_expr(state, &rhs_node);
        let op_ref = infix_op_ref(state, suffix);
        let lazy = is_lazy_operator_expr(state, &op_ref);
        let lhs = if lazy {
            unit_thunk_expr(state, acc)
        } else {
            acc
        };
        let rhs = if lazy {
            unit_thunk_expr(state, rhs)
        } else {
            rhs
        };
        let app1 = make_app_with_cause(state, op_ref, lhs, apply_arg_cause(suffix));
        make_app_with_cause(state, app1, rhs, apply_arg_cause(suffix))
    } else {
        acc
    }
}

fn lazy_operator_arg(state: &mut LowerState, op_ref: &TypedExpr, arg: TypedExpr) -> TypedExpr {
    if is_lazy_operator_expr(state, op_ref) {
        unit_thunk_expr(state, arg)
    } else {
        arg
    }
}

fn is_lazy_operator_expr(state: &LowerState, op_ref: &TypedExpr) -> bool {
    matches!(&op_ref.kind, ExprKind::Var(def) if state.ctx.is_lazy_operator_def(*def))
}

fn unit_thunk_expr(state: &mut LowerState, body: TypedExpr) -> TypedExpr {
    let def = state.fresh_def();
    let param_tv = state.fresh_tv();
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    let tv = state.fresh_tv();

    state.register_def_tv(def, param_tv);
    if let Some(owner) = state.current_owner {
        state.register_def_owner(def, owner);
    }
    state.infer.constrain(prim_type("unit"), Neg::Var(param_tv));
    state
        .infer
        .constrain(Pos::Var(param_tv), neg_prim_type("unit"));
    state.infer.constrain(
        state.pos_fun(
            Neg::Var(param_tv),
            Neg::Var(arg_eff_tv),
            Pos::Var(body.eff),
            Pos::Var(body.tv),
        ),
        Neg::Var(tv),
    );
    let eff = super::super::stmt::lambda_expr_eff_tv(state, &body, &[def]);
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Lam(def, Box::new(body)),
    }
}

fn apply_index_suffix(state: &mut LowerState, acc: TypedExpr, suffix: &SyntaxNode) -> TypedExpr {
    let idx_node = suffix
        .children()
        .find(|c| c.kind() == SyntaxKind::Expr)
        .or_else(|| {
            suffix
                .children()
                .find(|c| c.kind() == SyntaxKind::Bracket)
                .and_then(|bracket| bracket.children().find(|c| c.kind() == SyntaxKind::Expr))
        });
    let Some(idx_node) = idx_node else { return acc };
    let idx = lower_expr(state, &idx_node);
    let tv = state.fresh_tv();
    let eff = state.fresh_generated_effect_tv();
    let select = push_deferred_selection(
        state,
        acc,
        suffix,
        Name("index".to_string()),
        tv,
        eff,
        false,
        None,
    );
    make_app_with_cause(state, select, idx, apply_arg_cause(suffix))
}

fn apply_arg_cause(suffix: &SyntaxNode) -> ConstraintCause {
    ConstraintCause {
        span: Some(suffix.text_range()),
        reason: ConstraintReason::ApplyArg,
    }
}

fn push_deferred_selection(
    state: &mut LowerState,
    acc: TypedExpr,
    suffix: &SyntaxNode,
    name: Name,
    tv: crate::ids::TypeVar,
    eff: crate::ids::TypeVar,
    structural_record_allowed: bool,
    source_span: Option<rowan::TextRange>,
) -> TypedExpr {
    let owner = state.current_owner;
    let recv_tv = acc.tv;
    let receiver_is_known_value_struct_field =
        receiver_is_known_value_struct_field_read(state, &acc, &name);
    let receiver_is_plain_pure_value =
        receiver_is_known_value_struct_field || receiver_is_plain_pure_value_read(state, &acc);
    let recv_eff = selection_receiver_eff(state, &acc);
    let eff = if receiver_is_known_value_struct_field {
        state.fresh_exact_pure_eff_tv()
    } else {
        eff
    };
    if let Some(owner) = owner {
        state.infer.increment_pending_selection(owner);
    }
    state
        .infer
        .deferred_selections
        .borrow_mut()
        .entry(acc.tv)
        .or_default()
        .push(crate::solve::DeferredSelection {
            name: name.clone(),
            module: state.ctx.current_module,
            recv_eff,
            result_tv: tv,
            result_eff: eff,
            owner,
            cause: ConstraintCause {
                span: Some(suffix.text_range()),
                reason: ConstraintReason::FieldSelection,
            },
            structural_record_allowed,
            receiver_is_plain_pure_value,
        });
    if let Some(span) = source_span {
        state.record_selection_span(span, recv_tv, recv_eff, tv, eff);
    }
    TypedExpr {
        tv,
        eff,
        kind: ExprKind::Select {
            recv: Box::new(acc),
            name,
        },
    }
}

fn receiver_is_known_value_struct_field_read(
    state: &LowerState,
    expr: &TypedExpr,
    name: &Name,
) -> bool {
    match &expr.kind {
        ExprKind::Var(def) => state
            .value_struct_receiver_paths
            .get(def)
            .and_then(|path| state.infer.type_fields.get(path))
            .is_some_and(|fields| fields.contains_key(name)),
        ExprKind::BindHere(expr) | ExprKind::Coerce { expr, .. } => {
            receiver_is_known_value_struct_field_read(state, expr, name)
        }
        _ => false,
    }
}

fn selection_receiver_eff(state: &mut LowerState, recv: &TypedExpr) -> crate::ids::TypeVar {
    if receiver_is_plain_pure_value_read(state, recv) {
        return state.fresh_exact_pure_eff_tv();
    }

    let mut source_effs = Vec::new();
    collect_receiver_source_effs(state, recv, &mut source_effs);
    if source_effs.is_empty() {
        return recv.eff;
    }
    let eff = state.fresh_generated_effect_tv();
    state.infer.constrain(Pos::Var(recv.eff), Neg::Var(eff));
    for source_eff in source_effs {
        state.infer.constrain(Pos::Var(source_eff), Neg::Var(eff));
    }
    eff
}

fn receiver_is_plain_pure_value_read(state: &LowerState, expr: &TypedExpr) -> bool {
    match &expr.kind {
        ExprKind::Var(def) => {
            !state.def_eff_tvs.contains_key(def)
                && !state.lambda_param_source_eff_tvs.contains_key(def)
        }
        ExprKind::BindHere(expr) | ExprKind::Coerce { expr, .. } => {
            receiver_is_plain_pure_value_read(state, expr)
        }
        _ => false,
    }
}

fn collect_receiver_source_effs(
    state: &LowerState,
    expr: &TypedExpr,
    out: &mut Vec<crate::ids::TypeVar>,
) {
    match &expr.kind {
        ExprKind::Var(def) => {
            if let Some(source_eff) = state.lambda_param_source_eff_tvs.get(def).copied()
                && !out.contains(&source_eff)
            {
                out.push(source_eff);
            }
        }
        ExprKind::BindHere(expr) | ExprKind::Coerce { expr, .. } => {
            collect_receiver_source_effs(state, expr, out);
        }
        ExprKind::App { callee, arg, .. } => {
            collect_receiver_source_effs(state, callee, out);
            collect_receiver_source_effs(state, arg, out);
        }
        ExprKind::RefSet { reference, value } => {
            collect_receiver_source_effs(state, reference, out);
            collect_receiver_source_effs(state, value, out);
        }
        ExprKind::Tuple(items) | ExprKind::PolyVariant(_, items, _) => {
            for item in items {
                collect_receiver_source_effs(state, item, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for (_, field) in fields {
                collect_receiver_source_effs(state, field, out);
            }
            if let Some(spread) = spread {
                match spread {
                    RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
                        collect_receiver_source_effs(state, expr, out);
                    }
                }
            }
        }
        ExprKind::Select { recv, .. } => {
            collect_receiver_source_effs(state, recv, out);
        }
        ExprKind::Match(scrutinee, arms) => {
            collect_receiver_source_effs(state, scrutinee, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_receiver_source_effs(state, guard, out);
                }
                collect_receiver_source_effs(state, &arm.body, out);
            }
        }
        ExprKind::Catch(comp, arms) => {
            collect_receiver_source_effs(state, comp, out);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_receiver_source_effs(state, guard, out);
                }
                match &arm.kind {
                    CatchArmKind::Value(_, body) | CatchArmKind::Effect { body, .. } => {
                        collect_receiver_source_effs(state, body, out);
                    }
                }
            }
        }
        ExprKind::Block(block) => {
            for stmt in &block.stmts {
                match stmt {
                    TypedStmt::Let(_, expr) | TypedStmt::Expr(expr) => {
                        collect_receiver_source_effs(state, expr, out);
                    }
                    TypedStmt::Module(_, block) => {
                        if let Some(tail) = &block.tail {
                            collect_receiver_source_effs(state, tail, out);
                        }
                    }
                }
            }
            if let Some(tail) = &block.tail {
                collect_receiver_source_effs(state, tail, out);
            }
        }
        ExprKind::Lit(_)
        | ExprKind::PrimitiveOp(_)
        | ExprKind::Ref(_)
        | ExprKind::Lam(_, _)
        | ExprKind::PackForall(_, _) => {}
    }
}
