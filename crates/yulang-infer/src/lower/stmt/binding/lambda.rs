use crate::profile::ProfileClock as Instant;

use super::super::lambda_expr_eff_tv;
use super::arg::ArgPatInfo;
use crate::ast::expr::{CatchArmKind, ExprKind, RecordSpread, TypedExpr, TypedStmt};
use crate::ids::DefId;
use crate::lower::LowerState;
use crate::solve::EffectSubtractId;
use crate::types::{Neg, Pos};

#[derive(Clone)]
struct OccurrenceNonSubtract {
    def: DefId,
    predicate_ids: Vec<EffectSubtractId>,
    value_ids: Vec<EffectSubtractId>,
    value_targets: Vec<crate::ids::TypeVar>,
}

pub(crate) fn wrap_header_lambdas(
    state: &mut LowerState,
    raw_body: TypedExpr,
    arg_pats: Vec<ArgPatInfo>,
) -> TypedExpr {
    let start = Instant::now();
    let header_local_defs = arg_pats
        .iter()
        .flat_map(|arg_pat| {
            std::iter::once(arg_pat.def).chain(
                arg_pat
                    .local_bindings
                    .iter()
                    .map(|(_, local_def)| *local_def),
            )
        })
        .collect::<Vec<_>>();
    let mut occurrence_non_subtracts = Vec::new();
    for arg_pat in &arg_pats {
        let mut predicate_ids = super::super::configure_arg_effect_from_ann(
            state,
            arg_pat.arg_eff_tv,
            arg_pat.ann.as_ref(),
        );
        let mut value_ids = Vec::new();
        let mut value_targets = Vec::new();
        if let Some(hint) = state.lambda_param_function_sig_hint(arg_pat.def) {
            predicate_ids.extend_from_slice(hint.subtract_ids());
            value_ids.extend_from_slice(hint.subtract_ids());
            value_targets.extend_from_slice(hint.non_subtract_targets());
        }
        predicate_ids.sort();
        predicate_ids.dedup();
        value_ids.sort();
        value_ids.dedup();
        value_targets.sort_by_key(|tv| tv.0);
        value_targets.dedup();
        if predicate_ids.is_empty() && value_ids.is_empty() {
            continue;
        }
        occurrence_non_subtracts.push(OccurrenceNonSubtract {
            def: arg_pat.def,
            predicate_ids: predicate_ids.clone(),
            value_ids: value_ids.clone(),
            value_targets: value_targets.clone(),
        });
        occurrence_non_subtracts.extend(arg_pat.local_bindings.iter().map(|(_, local_def)| {
            OccurrenceNonSubtract {
                def: *local_def,
                predicate_ids: predicate_ids.clone(),
                value_ids: value_ids.clone(),
                value_targets: value_targets.clone(),
            }
        }));
    }
    record_non_subtracts_for_predicate_occurrences(state, &raw_body, &occurrence_non_subtracts);

    let result = arg_pats.into_iter().rev().fold(raw_body, |body, arg_pat| {
        let def = arg_pat.def;
        let param_tv = arg_pat.tv;
        let tv = state.fresh_tv();
        let arg_eff_tv = arg_pat.arg_eff_tv;
        if arg_pat.unit_arg {
            state
                .infer
                .constrain(super::super::prim_type("unit"), Neg::Var(param_tv));
            state
                .infer
                .constrain(Pos::Var(param_tv), super::super::neg_prim_type("unit"));
        }
        if let Some(pat) = &arg_pat.pat {
            state.infer.constrain(Pos::Var(param_tv), Neg::Var(pat.tv));
            state.infer.constrain(Pos::Var(pat.tv), Neg::Var(param_tv));
            state.register_lambda_param_pat(def, pat.clone());
            state.register_lambda_local_defs(
                def,
                arg_pat
                    .local_bindings
                    .iter()
                    .map(|(_, local_def)| *local_def)
                    .collect(),
            );
            state.ctx.push_local();
            for (name, def) in &arg_pat.local_bindings {
                state.ctx.bind_local(name.clone(), *def);
            }
            super::super::connect_pat_shape_and_locals(state, pat, body.eff);
            state.ctx.pop_local();
        }
        state.infer.constrain(
            state.pos_fun(
                Neg::Var(param_tv),
                Neg::Var(arg_eff_tv),
                Pos::Var(body.eff),
                Pos::Var(body.tv),
            ),
            Neg::Var(tv),
        );
        let mut local_defs = vec![def];
        local_defs.extend(
            arg_pat
                .local_bindings
                .iter()
                .map(|(_, local_def)| *local_def),
        );
        local_defs.extend(header_local_defs.iter().copied());
        let eff = lambda_expr_eff_tv(state, &body, &local_defs);
        TypedExpr {
            tv,
            eff,
            kind: ExprKind::Lam(def, Box::new(body)),
        }
    });
    state.lower_detail.wrap_header_lambdas += start.elapsed();
    result
}

fn record_non_subtracts_for_predicate_occurrences(
    state: &LowerState,
    expr: &TypedExpr,
    tracked: &[OccurrenceNonSubtract],
) {
    if tracked.is_empty() {
        return;
    }

    let mut ids = Vec::new();
    collect_predicate_occurrence_ids(expr, tracked, &mut ids);
    ids.sort();
    ids.dedup();
    for id in ids {
        state.infer.record_effect_non_subtract(expr.tv, id);
        state.infer.record_effect_non_subtract(expr.eff, id);
    }
    record_value_occurrence_non_subtracts(state, expr, tracked);
    record_nested_lambda_predicates(state, expr, tracked);
}

fn collect_predicate_occurrence_ids(
    expr: &TypedExpr,
    tracked: &[OccurrenceNonSubtract],
    out: &mut Vec<EffectSubtractId>,
) {
    match &expr.kind {
        ExprKind::Var(def) => {
            if let Some(entry) = tracked.iter().find(|entry| entry.def == *def) {
                out.extend_from_slice(&entry.predicate_ids);
            }
        }
        ExprKind::App { callee, arg, .. } => {
            collect_predicate_occurrence_ids(callee, tracked, out);
            collect_predicate_occurrence_ids(arg, tracked, out);
        }
        ExprKind::RefSet { reference, value } => {
            collect_predicate_occurrence_ids(reference, tracked, out);
            collect_predicate_occurrence_ids(value, tracked, out);
        }
        ExprKind::Tuple(items) | ExprKind::PolyVariant(_, items, _) => {
            for item in items {
                collect_predicate_occurrence_ids(item, tracked, out);
            }
        }
        ExprKind::Record { fields, spread } => {
            for (_, field) in fields {
                collect_predicate_occurrence_ids(field, tracked, out);
            }
            if let Some(spread) = spread {
                collect_record_spread_occurrence_ids(spread, tracked, out);
            }
        }
        ExprKind::Select { recv, .. }
        | ExprKind::Match(recv, _)
        | ExprKind::Catch(recv, _)
        | ExprKind::BindHere(recv)
        | ExprKind::Coerce { expr: recv, .. }
        | ExprKind::PackForall(_, recv) => {
            collect_predicate_occurrence_ids(recv, tracked, out);
            collect_expr_kind_extra_occurrence_ids(&expr.kind, tracked, out);
        }
        ExprKind::Block(block) => {
            for stmt in &block.stmts {
                collect_stmt_occurrence_ids(stmt, tracked, out);
            }
            if let Some(tail) = &block.tail {
                collect_predicate_occurrence_ids(tail, tracked, out);
            }
        }
        ExprKind::Lam(_, _) => {}
        ExprKind::Lit(_) | ExprKind::PrimitiveOp(_) | ExprKind::Ref(_) => {}
    }
}

fn collect_expr_kind_extra_occurrence_ids(
    kind: &ExprKind,
    tracked: &[OccurrenceNonSubtract],
    out: &mut Vec<EffectSubtractId>,
) {
    match kind {
        ExprKind::Match(_, arms) => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_predicate_occurrence_ids(guard, tracked, out);
                }
                collect_predicate_occurrence_ids(&arm.body, tracked, out);
            }
        }
        ExprKind::Catch(_, arms) => {
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_predicate_occurrence_ids(guard, tracked, out);
                }
                match &arm.kind {
                    CatchArmKind::Value(_, body) | CatchArmKind::Effect { body, .. } => {
                        collect_predicate_occurrence_ids(body, tracked, out);
                    }
                }
            }
        }
        _ => {}
    }
}

fn collect_record_spread_occurrence_ids(
    spread: &RecordSpread,
    tracked: &[OccurrenceNonSubtract],
    out: &mut Vec<EffectSubtractId>,
) {
    match spread {
        RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
            collect_predicate_occurrence_ids(expr, tracked, out);
        }
    }
}

fn collect_stmt_occurrence_ids(
    stmt: &TypedStmt,
    tracked: &[OccurrenceNonSubtract],
    out: &mut Vec<EffectSubtractId>,
) {
    match stmt {
        TypedStmt::Let(_, expr) | TypedStmt::Expr(expr) => {
            collect_predicate_occurrence_ids(expr, tracked, out);
        }
        TypedStmt::Module(_, block) => {
            for stmt in &block.stmts {
                collect_stmt_occurrence_ids(stmt, tracked, out);
            }
            if let Some(tail) = &block.tail {
                collect_predicate_occurrence_ids(tail, tracked, out);
            }
        }
    }
}

fn record_value_occurrence_non_subtracts(
    state: &LowerState,
    expr: &TypedExpr,
    tracked: &[OccurrenceNonSubtract],
) {
    match &expr.kind {
        ExprKind::Var(def) => {
            if let Some(entry) = tracked.iter().find(|entry| entry.def == *def) {
                for id in &entry.value_ids {
                    state.infer.record_effect_non_subtract_deep(expr.tv, *id);
                    state.infer.record_effect_non_subtract_deep(expr.eff, *id);
                    for target in &entry.value_targets {
                        state.infer.record_effect_non_subtract_deep(*target, *id);
                    }
                }
            }
        }
        ExprKind::App { callee, arg, .. } => {
            record_value_occurrence_non_subtracts(state, callee, tracked);
            record_value_occurrence_non_subtracts(state, arg, tracked);
        }
        ExprKind::RefSet { reference, value } => {
            record_value_occurrence_non_subtracts(state, reference, tracked);
            record_value_occurrence_non_subtracts(state, value, tracked);
        }
        ExprKind::Tuple(items) | ExprKind::PolyVariant(_, items, _) => {
            for item in items {
                record_value_occurrence_non_subtracts(state, item, tracked);
            }
        }
        ExprKind::Record { fields, spread } => {
            for (_, field) in fields {
                record_value_occurrence_non_subtracts(state, field, tracked);
            }
            if let Some(spread) = spread {
                record_value_occurrence_non_subtracts_for_spread(state, spread, tracked);
            }
        }
        ExprKind::Select { recv, .. }
        | ExprKind::BindHere(recv)
        | ExprKind::Coerce { expr: recv, .. }
        | ExprKind::PackForall(_, recv) => {
            record_value_occurrence_non_subtracts(state, recv, tracked);
        }
        ExprKind::Match(scrutinee, arms) => {
            record_value_occurrence_non_subtracts(state, scrutinee, tracked);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    record_value_occurrence_non_subtracts(state, guard, tracked);
                }
                record_value_occurrence_non_subtracts(state, &arm.body, tracked);
            }
        }
        ExprKind::Catch(scrutinee, arms) => {
            record_value_occurrence_non_subtracts(state, scrutinee, tracked);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    record_value_occurrence_non_subtracts(state, guard, tracked);
                }
                match &arm.kind {
                    CatchArmKind::Value(_, body) | CatchArmKind::Effect { body, .. } => {
                        record_value_occurrence_non_subtracts(state, body, tracked);
                    }
                }
            }
        }
        ExprKind::Block(block) => {
            for stmt in &block.stmts {
                record_value_occurrence_non_subtracts_for_stmt(state, stmt, tracked);
            }
            if let Some(tail) = &block.tail {
                record_value_occurrence_non_subtracts(state, tail, tracked);
            }
        }
        ExprKind::Lam(_, _) => {}
        ExprKind::Lit(_) | ExprKind::PrimitiveOp(_) | ExprKind::Ref(_) => {}
    }
}

fn record_value_occurrence_non_subtracts_for_spread(
    state: &LowerState,
    spread: &RecordSpread,
    tracked: &[OccurrenceNonSubtract],
) {
    match spread {
        RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
            record_value_occurrence_non_subtracts(state, expr, tracked);
        }
    }
}

fn record_value_occurrence_non_subtracts_for_stmt(
    state: &LowerState,
    stmt: &TypedStmt,
    tracked: &[OccurrenceNonSubtract],
) {
    match stmt {
        TypedStmt::Let(_, expr) | TypedStmt::Expr(expr) => {
            record_value_occurrence_non_subtracts(state, expr, tracked);
        }
        TypedStmt::Module(_, block) => {
            for stmt in &block.stmts {
                record_value_occurrence_non_subtracts_for_stmt(state, stmt, tracked);
            }
            if let Some(tail) = &block.tail {
                record_value_occurrence_non_subtracts(state, tail, tracked);
            }
        }
    }
}

fn record_nested_lambda_predicates(
    state: &LowerState,
    expr: &TypedExpr,
    tracked: &[OccurrenceNonSubtract],
) {
    match &expr.kind {
        ExprKind::Lam(_, body) => {
            record_non_subtracts_for_predicate_occurrences(state, body, tracked);
        }
        ExprKind::App { callee, arg, .. } => {
            record_nested_lambda_predicates(state, callee, tracked);
            record_nested_lambda_predicates(state, arg, tracked);
        }
        ExprKind::RefSet { reference, value } => {
            record_nested_lambda_predicates(state, reference, tracked);
            record_nested_lambda_predicates(state, value, tracked);
        }
        ExprKind::Tuple(items) | ExprKind::PolyVariant(_, items, _) => {
            for item in items {
                record_nested_lambda_predicates(state, item, tracked);
            }
        }
        ExprKind::Record { fields, spread } => {
            for (_, field) in fields {
                record_nested_lambda_predicates(state, field, tracked);
            }
            if let Some(spread) = spread {
                record_nested_lambda_predicates_for_spread(state, spread, tracked);
            }
        }
        ExprKind::Select { recv, .. }
        | ExprKind::BindHere(recv)
        | ExprKind::Coerce { expr: recv, .. }
        | ExprKind::PackForall(_, recv) => {
            record_nested_lambda_predicates(state, recv, tracked);
        }
        ExprKind::Match(scrutinee, arms) => {
            record_nested_lambda_predicates(state, scrutinee, tracked);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    record_nested_lambda_predicates(state, guard, tracked);
                }
                record_nested_lambda_predicates(state, &arm.body, tracked);
            }
        }
        ExprKind::Catch(scrutinee, arms) => {
            record_nested_lambda_predicates(state, scrutinee, tracked);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    record_nested_lambda_predicates(state, guard, tracked);
                }
                match &arm.kind {
                    CatchArmKind::Value(_, body) | CatchArmKind::Effect { body, .. } => {
                        record_nested_lambda_predicates(state, body, tracked);
                    }
                }
            }
        }
        ExprKind::Block(block) => {
            for stmt in &block.stmts {
                record_nested_lambda_predicates_for_stmt(state, stmt, tracked);
            }
            if let Some(tail) = &block.tail {
                record_nested_lambda_predicates(state, tail, tracked);
            }
        }
        ExprKind::Lit(_) | ExprKind::PrimitiveOp(_) | ExprKind::Var(_) | ExprKind::Ref(_) => {}
    }
}

fn record_nested_lambda_predicates_for_spread(
    state: &LowerState,
    spread: &RecordSpread,
    tracked: &[OccurrenceNonSubtract],
) {
    match spread {
        RecordSpread::Head(expr) | RecordSpread::Tail(expr) => {
            record_nested_lambda_predicates(state, expr, tracked);
        }
    }
}

fn record_nested_lambda_predicates_for_stmt(
    state: &LowerState,
    stmt: &TypedStmt,
    tracked: &[OccurrenceNonSubtract],
) {
    match stmt {
        TypedStmt::Let(_, expr) | TypedStmt::Expr(expr) => {
            record_nested_lambda_predicates(state, expr, tracked);
        }
        TypedStmt::Module(_, block) => {
            for stmt in &block.stmts {
                record_nested_lambda_predicates_for_stmt(state, stmt, tracked);
            }
            if let Some(tail) = &block.tail {
                record_nested_lambda_predicates(state, tail, tracked);
            }
        }
    }
}
