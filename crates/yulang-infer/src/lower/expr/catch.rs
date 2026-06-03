use crate::profile::ProfileClock as Instant;
use std::collections::{HashMap, HashSet};

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{CatchArmKind, ExprKind, TypedCatchArm, TypedExpr};
use crate::diagnostic::{
    ConstraintCause, ConstraintReason, ExpectedAdapterEdgeKind, ExpectedEdgeId, ExpectedEdgeKind,
};
use crate::lower::stmt::{bind_pattern_locals, connect_pat_shape_and_locals, lower_pat};
use crate::lower::{CatchArmCheckKind, CatchArmCheckSite, CatchCheckSite, LowerState, SyntaxNode};
use crate::scheme::{
    collect_neg_free_vars, collect_pos_free_vars, subst_neg_id_map, subst_pos_id_map,
};
use crate::solve::{EffectSubtractability, ShiftKeep};
use crate::symbols::{Name, Path};
use crate::types::{EffectAtom, Neg, Pos};

use super::control::{case_like_label_name, lower_arm_guard, lower_recursive_case_like};
use super::{
    collect_child_arms, lower_expr, neg_id_is_pure_row, neg_prim_type, pos_id_is_empty_row,
    prim_type, resolve_bound_def_expr, unit_expr,
};

pub(super) fn lower_catch(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let comp = node
        .children()
        .find(|c| c.kind() == SyntaxKind::Expr)
        .map(|c| lower_expr(state, &c))
        .unwrap_or_else(|| unit_expr(state));
    if let Some(label) = case_like_label_name(node) {
        return lower_recursive_case_like(
            state,
            label,
            Some(comp),
            "#catch-receiver",
            configure_catch_lambda_receiver,
            |state, receiver| {
                let comp = resolve_bound_def_expr(state, receiver.def);
                lower_catch_with_comp(state, node, comp)
            },
        );
    }
    lower_catch_with_comp(state, node, comp)
}

pub(super) fn lower_catch_lambda(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    if let Some(label) = case_like_label_name(node) {
        return lower_recursive_case_like(
            state,
            label,
            None,
            "#catch-receiver",
            configure_catch_lambda_receiver,
            |state, receiver| {
                let comp = resolve_bound_def_expr(state, receiver.def);
                lower_catch_with_comp(state, node, comp)
            },
        );
    }
    let receiver = super::control::fresh_case_like_lambda_receiver(state, "#catch-receiver");
    let arg_eff_tv = configure_catch_lambda_receiver(state, &receiver);
    let comp = resolve_bound_def_expr(state, receiver.def);
    let body = lower_catch_with_comp(state, node, comp);
    super::control::case_like_lambda_expr(state, receiver, body, arg_eff_tv)
}

fn configure_catch_lambda_receiver(
    state: &mut LowerState,
    receiver: &super::control::CaseLikeLambdaReceiver,
) -> crate::ids::TypeVar {
    let arg_eff_tv = state.fresh_tv();
    state.register_def_eff_tv(receiver.def, arg_eff_tv);
    state.register_lambda_param_effect_annotation(
        receiver.def,
        yulang_typed_ir::ParamEffectAnnotation::Wildcard,
    );
    arg_eff_tv
}

fn lower_catch_with_comp(state: &mut LowerState, node: &SyntaxNode, comp: TypedExpr) -> TypedExpr {
    let start = Instant::now();

    let result = (|| {
        let vars = CatchResultVars::fresh(state);
        let scrutinee = catch_scrutinee(state, &comp);

        let mut lowered_arms: Vec<LoweredCatchArm> = catch_arm_nodes(node)
            .into_iter()
            .map(|arm_node| {
                let raw = lower_catch_arm(state, &arm_node, (scrutinee.value_tv, scrutinee.eff_tv));
                let check = catch_arm_check_site(state, &arm_node, &raw.arm);
                LoweredCatchArm {
                    arm: raw.arm,
                    check,
                    guard_eff: raw.guard_eff,
                }
            })
            .collect();

        let mut saw_value_arm = false;
        let mut handled = CatchHandledEffects::default();
        for lowered in &mut lowered_arms {
            let guard_eff = lowered.guard_eff;
            match &mut lowered.arm.kind {
                CatchArmKind::Value(pat, body) => {
                    lowered.check.active = true;
                    saw_value_arm = true;
                    let original_body = body.clone();
                    let (new_body, branch_edge_id) = state.implicit_cast_boundary_with_effects(
                        original_body.clone(),
                        vars.value_tv,
                        vars.value_arm_eff_tv,
                        ExpectedEdgeKind::CatchBranch,
                        ConstraintCause {
                            span: None,
                            reason: ConstraintReason::CatchBranch,
                        },
                        true,
                    );
                    *body = new_body;
                    record_handler_return_adapter_edge(
                        state,
                        branch_edge_id,
                        &original_body,
                        vars.value_tv,
                        vars.value_arm_eff_tv,
                    );
                    if let Some(guard_eff) = guard_eff {
                        state
                            .infer
                            .constrain(Pos::Var(guard_eff), Neg::Var(vars.value_arm_eff_tv));
                    }
                    state
                        .infer
                        .constrain(Pos::Var(scrutinee.value_tv), Neg::Var(pat.tv));
                }
                CatchArmKind::Effect {
                    op_path,
                    pat,
                    k,
                    body,
                } => {
                    let effect_arm = catch_effect_arm_info(
                        state,
                        op_path,
                        scrutinee.eff_tv,
                        &mut handled.effect_arg_substs,
                    );
                    lowered.check.active = effect_arm.active;
                    record_catch_arm_effect_path(
                        &mut lowered.check,
                        effect_arm.effect_path.clone(),
                    );
                    if effect_arm.active {
                        handled.record_active_arm(
                            effect_arm.effect_path.clone(),
                            effect_arm.op_def,
                            pat,
                            effect_arm.handled_atom.clone(),
                            effect_arm.handled_op.clone(),
                        );
                    }

                    let mut resume_pos = None;
                    let mut resume_neg = None;
                    let op_call_eff = state.fresh_tv();
                    if let Some(op_use) = &effect_arm.op_use {
                        let pos_sig = state.infer.arena.get_pos(op_use.pos_sig);
                        let neg_sig = state.infer.arena.get_neg(op_use.neg_sig);
                        let (
                            Pos::Fun {
                                arg: op_arg_neg,
                                ret_eff: op_ret_eff_pos,
                                ret: op_ret_pos,
                                ..
                            },
                            Neg::Fun {
                                arg: op_arg_pos,
                                ret_eff: op_ret_eff_neg,
                                ret: op_ret_neg,
                                ..
                            },
                        ) = (pos_sig, neg_sig)
                        else {
                            unreachable!("effect operation signatures must be functions");
                        };
                        state.infer.constrain(op_arg_pos, Neg::Var(pat.tv));
                        state.infer.constrain(Pos::Var(pat.tv), op_arg_neg);
                        state.infer.constrain(op_ret_eff_pos, Neg::Var(op_call_eff));
                        state.infer.constrain(Pos::Var(op_call_eff), op_ret_eff_neg);
                        resume_pos = Some(state.infer.arena.get_pos(op_ret_pos).clone());
                        resume_neg = Some(state.infer.arena.get_neg(op_ret_neg).clone());
                        if effect_arm.active {
                            state.infer.constrain(
                                Pos::Var(op_call_eff),
                                state.neg_row(vec![effect_arm.handled_op.clone()], Neg::Top),
                            );
                        }
                    }

                    if let Some(&k_tv) = state.def_tvs.get(k) {
                        let (resume_pos, resume_neg) = match (resume_pos, resume_neg) {
                            (Some(pos), Some(neg)) => (pos, neg),
                            _ => {
                                let resume_tv = state.fresh_tv();
                                (Pos::Var(resume_tv), Neg::Var(resume_tv))
                            }
                        };
                        let k_arg_eff = state.fresh_tv();
                        let k_ret_eff = scrutinee.eff_tv; // 変えないこと。userより
                        let k_fun = state.pos_fun(
                            resume_neg,
                            Neg::Var(k_arg_eff),
                            Pos::Var(k_ret_eff),
                            Pos::Var(scrutinee.value_tv),
                        );
                        state.infer.constrain(k_fun.clone(), Neg::Var(k_tv));
                        state.infer.constrain(
                            Pos::Var(k_tv),
                            state.neg_fun(
                                resume_pos,
                                Pos::Var(k_arg_eff),
                                Neg::Var(k_ret_eff),
                                Neg::Var(scrutinee.value_tv),
                            ),
                        );
                    }

                    let original_body = body.clone();
                    let (new_body, branch_edge_id) = state.implicit_cast_boundary_with_effects(
                        original_body.clone(),
                        vars.value_tv,
                        vars.effect_arm_eff_tv,
                        ExpectedEdgeKind::CatchBranch,
                        ConstraintCause {
                            span: None,
                            reason: ConstraintReason::CatchBranch,
                        },
                        true,
                    );
                    *body = new_body;
                    record_handler_return_adapter_edge(
                        state,
                        branch_edge_id,
                        &original_body,
                        vars.value_tv,
                        vars.effect_arm_eff_tv,
                    );
                    if let Some(guard_eff) = guard_eff {
                        state
                            .infer
                            .constrain(Pos::Var(guard_eff), Neg::Var(vars.effect_arm_eff_tv));
                    }
                }
            }
        }
        let check_arms: Vec<CatchArmCheckSite> = lowered_arms
            .iter()
            .map(|lowered| lowered.check.clone())
            .collect();
        let arms: Vec<TypedCatchArm> = lowered_arms
            .into_iter()
            .filter_map(|lowered| lowered.check.active.then_some(lowered.arm))
            .collect();
        state.catch_check_sites.push(CatchCheckSite {
            span: node.text_range(),
            file_span: state.current_source_span(node.text_range()),
            body_tv: scrutinee.value_tv,
            body_eff_tv: scrutinee.eff_tv,
            result_tv: vars.value_tv,
            result_eff_tv: vars.eff_tv,
            arms: check_arms,
        });
        constrain_catch_result_value(state, &comp, &scrutinee, vars, saw_value_arm, &handled);
        constrain_catch_result_effect(
            state,
            &comp,
            &scrutinee,
            vars,
            saw_value_arm,
            &handled,
            node,
        );

        TypedExpr {
            tv: vars.value_tv,
            eff: vars.eff_tv,
            kind: ExprKind::Catch(Box::new(comp), arms),
        }
    })();
    state.lower_detail.lower_catch += start.elapsed();
    result
}

#[derive(Clone)]
struct CatchScrutinee {
    value_tv: crate::ids::TypeVar,
    eff_tv: crate::ids::TypeVar,
}

#[derive(Clone, Copy)]
struct CatchResultVars {
    value_tv: crate::ids::TypeVar,
    eff_tv: crate::ids::TypeVar,
    scrutinee_rest_eff_tv: crate::ids::TypeVar,
    value_arm_eff_tv: crate::ids::TypeVar,
    effect_arm_eff_tv: crate::ids::TypeVar,
}

impl CatchResultVars {
    fn fresh(state: &LowerState) -> Self {
        let vars = Self {
            value_tv: state.fresh_tv(),
            eff_tv: state.fresh_tv(),
            scrutinee_rest_eff_tv: state.fresh_tv(),
            value_arm_eff_tv: state.fresh_tv(),
            effect_arm_eff_tv: state.fresh_tv(),
        };
        state
            .infer
            .record_effect_subtractability(vars.eff_tv, EffectSubtractability::All);
        vars
    }
}

#[derive(Default)]
struct CatchHandledEffects {
    ops: Vec<Neg>,
    paths: HashSet<Path>,
    fully_covered_ops: HashMap<Path, HashSet<crate::ids::DefId>>,
    atoms: HashSet<crate::types::EffectAtom>,
    effect_arg_substs: HashMap<Path, HashMap<crate::ids::TypeVar, crate::ids::TypeVar>>,
}

impl CatchHandledEffects {
    fn record_active_arm(
        &mut self,
        effect_path: Path,
        op_def: Option<crate::ids::DefId>,
        pat: &crate::ast::expr::TypedPat,
        handled_atom: crate::types::EffectAtom,
        handled_op: Neg,
    ) {
        self.paths.insert(effect_path.clone());
        if pattern_covers_all(pat)
            && let Some(op_def) = op_def
        {
            self.fully_covered_ops
                .entry(effect_path)
                .or_default()
                .insert(op_def);
        }
        if self.atoms.insert(handled_atom) {
            self.ops.push(handled_op);
        }
    }
}

struct LoweredCatchArm {
    arm: TypedCatchArm,
    check: CatchArmCheckSite,
    guard_eff: Option<crate::ids::TypeVar>,
}

struct RawLoweredCatchArm {
    arm: TypedCatchArm,
    guard_eff: Option<crate::ids::TypeVar>,
}

struct CatchEffectArmInfo {
    effect_path: Path,
    op_def: Option<crate::ids::DefId>,
    op_use: Option<EffectOpUse>,
    handled_atom: crate::types::EffectAtom,
    handled_op: Neg,
    active: bool,
}

fn catch_effect_arm_info(
    state: &mut LowerState,
    op_path: &Path,
    scrutinee_eff: crate::ids::TypeVar,
    effect_arg_substs: &mut HashMap<Path, HashMap<crate::ids::TypeVar, crate::ids::TypeVar>>,
) -> CatchEffectArmInfo {
    let op_def = resolve_effect_op_def(state, op_path);
    let effect_path = op_def
        .and_then(|def| state.effect_op_effect_paths.get(&def).cloned())
        .unwrap_or_else(|| effect_scope_path(op_path));
    let active = handler_captures_effect_path(state, scrutinee_eff);
    let op_use = op_def
        .and_then(|def| instantiate_effect_op_use(state, def, &effect_path, effect_arg_substs));
    let handled_atom = crate::types::EffectAtom {
        path: effect_path.clone(),
        args: op_use
            .as_ref()
            .map(|op| op.args.clone())
            .unwrap_or_else(|| fresh_effect_atom_args(state, &effect_path)),
    };
    if active {
        constrain_handled_atom_args_from_scrutinee_metadata(state, scrutinee_eff, &handled_atom);
    }
    let handled_op = Neg::Atom(handled_atom.clone());
    CatchEffectArmInfo {
        effect_path,
        op_def,
        op_use,
        handled_atom,
        handled_op,
        active,
    }
}

fn fresh_effect_atom_args(
    state: &mut LowerState,
    effect_path: &Path,
) -> Vec<(crate::ids::TypeVar, crate::ids::TypeVar)> {
    (0..state.effect_arities.get(effect_path).copied().unwrap_or(0))
        .map(|_| {
            let pos = state.fresh_tv();
            let neg = state.fresh_tv();
            (pos, neg)
        })
        .collect()
}

fn constrain_handled_atom_args_from_scrutinee_metadata(
    state: &LowerState,
    scrutinee_eff: crate::ids::TypeVar,
    handled_atom: &EffectAtom,
) {
    let Some(EffectSubtractability::Set(atoms)) = state.infer.effect_subtractability(scrutinee_eff)
    else {
        return;
    };

    for source_atom in atoms {
        if source_atom.path == handled_atom.path
            && source_atom.args.len() == handled_atom.args.len()
        {
            constrain_matched_effect_atom_args(state, &source_atom, handled_atom);
        }
    }
}

fn constrain_matched_effect_atom_args(
    state: &LowerState,
    source_atom: &EffectAtom,
    handled_atom: &EffectAtom,
) {
    for ((source_pos, source_neg), (handled_pos, handled_neg)) in
        source_atom.args.iter().zip(&handled_atom.args)
    {
        state
            .infer
            .constrain(Pos::Var(*source_pos), Neg::Var(*handled_neg));
        state
            .infer
            .constrain(Pos::Var(*handled_pos), Neg::Var(*source_neg));
    }
}

fn constrain_catch_result_value(
    state: &mut LowerState,
    comp: &TypedExpr,
    scrutinee: &CatchScrutinee,
    vars: CatchResultVars,
    saw_value_arm: bool,
    handled: &CatchHandledEffects,
) {
    if saw_value_arm || comp_is_direct_handled_effect_call(state, comp, &handled.ops) {
        return;
    }
    state
        .infer
        .constrain(Pos::Var(scrutinee.value_tv), Neg::Var(vars.value_tv));
    state
        .infer
        .constrain(Pos::Var(vars.value_tv), Neg::Var(scrutinee.value_tv));
}

fn constrain_catch_result_effect(
    state: &mut LowerState,
    comp: &TypedExpr,
    scrutinee: &CatchScrutinee,
    vars: CatchResultVars,
    saw_value_arm: bool,
    handled: &CatchHandledEffects,
    node: &SyntaxNode,
) {
    if handled.ops.is_empty() {
        constrain_catch_result_effect_without_handlers(state, scrutinee, vars, saw_value_arm);
    } else {
        constrain_catch_result_effect_with_handlers(
            state,
            comp,
            scrutinee,
            vars,
            saw_value_arm,
            handled,
            node,
        );
    }
}

fn constrain_catch_result_effect_without_handlers(
    state: &mut LowerState,
    scrutinee: &CatchScrutinee,
    vars: CatchResultVars,
    saw_value_arm: bool,
) {
    state
        .infer
        .constrain(Pos::Var(scrutinee.eff_tv), Neg::Var(vars.eff_tv));
    if saw_value_arm {
        state
            .infer
            .constrain(Pos::Var(vars.value_arm_eff_tv), Neg::Var(vars.eff_tv));
    }
    state
        .infer
        .constrain(Pos::Var(vars.effect_arm_eff_tv), Neg::Var(vars.eff_tv));
}

fn constrain_catch_result_effect_with_handlers(
    state: &mut LowerState,
    comp: &TypedExpr,
    scrutinee: &CatchScrutinee,
    vars: CatchResultVars,
    saw_value_arm: bool,
    handled: &CatchHandledEffects,
    node: &SyntaxNode,
) {
    record_handler_body_boundary_keep(state, comp, scrutinee.eff_tv);
    record_handler_residual_adapter_edge(
        state,
        scrutinee.value_tv,
        scrutinee.eff_tv,
        vars.value_tv,
        vars.eff_tv,
        node,
    );

    let handled_ops = handled
        .ops
        .iter()
        .cloned()
        .into_iter()
        .map(|op| state.infer.alloc_neg(op))
        .collect::<Vec<_>>();
    constrain_handler_row_upper(
        state,
        scrutinee.eff_tv,
        handled_ops.clone(),
        vars.scrutinee_rest_eff_tv,
        ConstraintCause {
            span: Some(node.text_range()),
            reason: ConstraintReason::CatchBranch,
        },
    );
    state.infer.constrain_with_cause(
        Pos::Var(vars.scrutinee_rest_eff_tv),
        Neg::Var(vars.eff_tv),
        ConstraintCause {
            span: Some(node.text_range()),
            reason: ConstraintReason::CatchBranch,
        },
    );

    if saw_value_arm {
        state.infer.constrain_with_cause(
            Pos::Var(vars.value_arm_eff_tv),
            Neg::Var(vars.eff_tv),
            ConstraintCause {
                span: Some(node.text_range()),
                reason: ConstraintReason::CatchBranch,
            },
        );
    }

    state.infer.constrain_with_cause(
        Pos::Var(vars.effect_arm_eff_tv),
        Neg::Var(vars.eff_tv),
        ConstraintCause {
            span: Some(node.text_range()),
            reason: ConstraintReason::CatchBranch,
        },
    );

    let leaves_open =
        catch_leaves_effect_family_open(state, &handled.paths, &handled.fully_covered_ops);
    if leaves_open {
        state.infer.constrain_with_cause(
            Pos::Var(scrutinee.eff_tv),
            Neg::Var(vars.eff_tv),
            ConstraintCause {
                span: Some(node.text_range()),
                reason: ConstraintReason::CatchBranch,
            },
        );
    }
}

fn catch_arm_nodes(node: &SyntaxNode) -> Vec<SyntaxNode> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::CatchBlock)
        .flat_map(|block| collect_child_arms(&block, SyntaxKind::CatchArm))
        .collect()
}

fn catch_arm_check_site(
    state: &LowerState,
    node: &SyntaxNode,
    arm: &TypedCatchArm,
) -> CatchArmCheckSite {
    let pats = catch_arm_pattern_nodes(node);
    let guard_span = catch_arm_guard_span(node);
    CatchArmCheckSite {
        span: node.text_range(),
        file_span: state.current_source_span(node.text_range()),
        guard_span,
        guard_file_span: guard_span.and_then(|span| state.current_source_span(span)),
        active: false,
        kind: catch_arm_check_kind(state, &pats, arm),
    }
}

fn catch_arm_pattern_nodes(node: &SyntaxNode) -> Vec<SyntaxNode> {
    node.children()
        .filter(|child| {
            matches!(
                child.kind(),
                SyntaxKind::Pattern
                    | SyntaxKind::PatOr
                    | SyntaxKind::PatAs
                    | SyntaxKind::PatParenGroup
            )
        })
        .collect()
}

fn catch_arm_guard_span(node: &SyntaxNode) -> Option<rowan::TextRange> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::CatchGuard)
        .map(|guard| guard.text_range())
}

fn catch_arm_check_kind(
    state: &LowerState,
    pats: &[SyntaxNode],
    arm: &TypedCatchArm,
) -> CatchArmCheckKind {
    if let CatchArmKind::Effect { op_path, pat, .. } = &arm.kind {
        let effect_pattern = &pats[0];
        let continuation = &pats[1];
        return CatchArmCheckKind::Effect {
            op_path: op_path.clone(),
            effect_path: None,
            payload_covers_all: pattern_covers_all(pat),
            effect_pattern_span: Some(effect_pattern.text_range()),
            effect_pattern_file_span: state.current_source_span(effect_pattern.text_range()),
            continuation_span: Some(continuation.text_range()),
            continuation_file_span: state.current_source_span(continuation.text_range()),
        };
    }

    let pattern = pats.first();
    let pattern_covers_all = match &arm.kind {
        CatchArmKind::Value(pat, _) => pattern_covers_all(pat),
        CatchArmKind::Effect { .. } => false,
    };
    CatchArmCheckKind::Value {
        pattern_span: pattern.map(|pattern| pattern.text_range()),
        pattern_file_span: pattern
            .and_then(|pattern| state.current_source_span(pattern.text_range())),
        pattern_covers_all,
    }
}

fn record_catch_arm_effect_path(check: &mut CatchArmCheckSite, effect_path: Path) {
    if let CatchArmCheckKind::Effect {
        effect_path: recorded,
        ..
    } = &mut check.kind
    {
        *recorded = Some(effect_path);
    }
}

fn pattern_covers_all(pat: &crate::ast::expr::TypedPat) -> bool {
    use crate::ast::expr::PatKind;

    match &pat.kind {
        PatKind::Wild | PatKind::UnresolvedName(_) => true,
        PatKind::As(inner, _) => pattern_covers_all(inner),
        PatKind::Or(left, right) => pattern_covers_all(left) || pattern_covers_all(right),
        PatKind::Tuple(items) => items.iter().all(pattern_covers_all),
        PatKind::Lit(_)
        | PatKind::Con(_, _)
        | PatKind::List { .. }
        | PatKind::Record { .. }
        | PatKind::PolyVariant(_, _) => false,
    }
}

fn catch_scrutinee(state: &mut LowerState, comp: &TypedExpr) -> CatchScrutinee {
    let value_tv = state.fresh_tv();
    let eff_tv = direct_catch_scrutinee_source_eff_tv(state, comp).unwrap_or(comp.eff);
    state.infer.constrain(Pos::Var(comp.tv), Neg::Var(value_tv));
    copy_catch_scrutinee_bind_metadata(state, comp, eff_tv);

    CatchScrutinee { value_tv, eff_tv }
}

fn copy_catch_scrutinee_bind_metadata(
    state: &LowerState,
    comp: &TypedExpr,
    scrutinee_eff: crate::ids::TypeVar,
) {
    if let Some(source_eff) = direct_catch_scrutinee_source_eff_tv(state, comp) {
        state
            .infer
            .copy_effect_subtractability(source_eff, scrutinee_eff);
    }
}

fn direct_catch_scrutinee_source_eff_tv(
    state: &LowerState,
    comp: &TypedExpr,
) -> Option<crate::ids::TypeVar> {
    let def = direct_catch_scrutinee_param_def(comp)?;
    state.lambda_param_source_eff_tvs.get(&def).copied()
}

fn direct_catch_scrutinee_param_def(comp: &TypedExpr) -> Option<crate::ids::DefId> {
    match &comp.kind {
        ExprKind::Var(def) => Some(*def),
        ExprKind::BindHere(expr) | ExprKind::Coerce { expr, .. } => {
            direct_catch_scrutinee_param_def(expr)
        }
        _ => None,
    }
}

fn constrain_handler_row_upper(
    state: &mut LowerState,
    comp_handler_eff: crate::ids::TypeVar,
    handled: Vec<crate::ids::NegId>,
    rest_eff: crate::ids::TypeVar,
    cause: ConstraintCause,
) {
    let rest_tail = state.infer.alloc_neg(Neg::Var(rest_eff));
    let upper = if handled.is_empty() {
        rest_tail
    } else {
        state.infer.alloc_neg(Neg::Row(handled, rest_tail))
    };
    state
        .infer
        .constrain_with_cause(Pos::Var(comp_handler_eff), upper, cause);
}

fn catch_leaves_effect_family_open(
    state: &LowerState,
    handled_effect_paths: &HashSet<Path>,
    fully_covered_effect_ops: &HashMap<Path, HashSet<crate::ids::DefId>>,
) -> bool {
    for effect_path in handled_effect_paths {
        let known_ops = state
            .effect_op_effect_paths
            .iter()
            .filter_map(|(def, path)| (path == effect_path).then_some(*def))
            .collect::<Vec<_>>();
        if known_ops.is_empty() {
            continue;
        }
        let covered = fully_covered_effect_ops.get(effect_path);
        if known_ops
            .iter()
            .any(|def| !covered.is_some_and(|covered| covered.contains(def)))
        {
            return true;
        }
    }
    false
}

fn handler_captures_effect_path(state: &LowerState, eff: crate::ids::TypeVar) -> bool {
    !eff_tv_is_exact_pure_row(state, eff)
}

fn eff_tv_is_exact_pure_row(state: &LowerState, tv: crate::ids::TypeVar) -> bool {
    let mut seen = HashSet::new();
    seen.insert(tv);
    let lowers = state.infer.lower_refs_of(tv);
    let uppers = state.infer.upper_refs_of(tv);
    !lowers.is_empty()
        && lowers
            .iter()
            .all(|lower| pos_id_is_empty_row(state, *lower, &mut seen))
        && uppers
            .iter()
            .all(|upper| neg_id_is_pure_row(state, *upper, &mut seen))
}

fn comp_is_direct_handled_effect_call(
    state: &LowerState,
    comp: &TypedExpr,
    handled_ops: &[Neg],
) -> bool {
    let Some(effect_path) = direct_effect_call_path(state, comp) else {
        return false;
    };
    handled_ops
        .iter()
        .any(|handled| matches!(handled, Neg::Atom(atom) if atom.path == effect_path))
}

fn direct_effect_call_path(state: &LowerState, expr: &TypedExpr) -> Option<Path> {
    match &expr.kind {
        ExprKind::App { callee, .. } => direct_effect_call_path(state, callee),
        ExprKind::Coerce { expr, .. }
        | ExprKind::BindHere(expr)
        | ExprKind::PackForall(_, expr) => direct_effect_call_path(state, expr),
        ExprKind::Var(def) => state.effect_op_effect_paths.get(def).cloned(),
        _ => None,
    }
}

fn record_handler_body_boundary_keep(
    state: &LowerState,
    comp: &TypedExpr,
    comp_eff: crate::ids::TypeVar,
) {
    let Some(keep) = handler_body_boundary_keep(state, comp) else {
        return;
    };
    state
        .infer
        .record_effect_boundary_keep(comp_eff, keep.clone());
    if let Some(subtractability) = effect_subtractability_for_keep(&keep) {
        state
            .infer
            .record_effect_subtractability(comp_eff, subtractability);
    }
}

fn handler_body_boundary_keep(state: &LowerState, comp: &TypedExpr) -> Option<ShiftKeep> {
    let (def, direct_var) = match &comp.kind {
        ExprKind::Var(def) => (*def, true),
        ExprKind::App { callee, .. } => match &callee.kind {
            ExprKind::Var(def) => (*def, false),
            _ => return None,
        },
        _ => return None,
    };
    if state.effect_op_args.contains_key(&def) {
        return None;
    }
    if state.is_unannotated_current_or_ancestor_lambda_param(def) {
        return Some(if direct_var {
            ShiftKeep::Surface
        } else {
            ShiftKeep::None
        });
    }
    let allowed = state.lambda_param_function_allowed_effects.get(&def)?;
    Some(match allowed {
        yulang_typed_ir::FunctionSigAllowedEffects::Wildcard => ShiftKeep::Surface,
        yulang_typed_ir::FunctionSigAllowedEffects::Effects(paths) => ShiftKeep::Set(
            paths
                .iter()
                .map(|path| Path {
                    segments: path
                        .segments
                        .iter()
                        .map(|name| Name(name.0.clone()))
                        .collect(),
                })
                .collect(),
        ),
    })
}

fn effect_subtractability_for_keep(keep: &ShiftKeep) -> Option<EffectSubtractability> {
    match keep {
        ShiftKeep::None | ShiftKeep::CallBoundary => Some(EffectSubtractability::Empty),
        ShiftKeep::Surface => None,
        ShiftKeep::Set(paths) => Some(EffectSubtractability::from_paths(paths.clone())),
    }
}

fn record_handler_return_adapter_edge(
    state: &mut LowerState,
    source_edge: ExpectedEdgeId,
    body: &TypedExpr,
    result_tv: crate::ids::TypeVar,
    result_eff: crate::ids::TypeVar,
) {
    state.record_expected_adapter_edge(
        ExpectedAdapterEdgeKind::HandlerReturn,
        Some(source_edge),
        Some(body.tv),
        Some(result_tv),
        Some(body.eff),
        Some(result_eff),
        ConstraintCause {
            span: None,
            reason: ConstraintReason::CatchBranch,
        },
    );
}

fn record_handler_residual_adapter_edge(
    state: &mut LowerState,
    scrutinee_tv: crate::ids::TypeVar,
    scrutinee_eff: crate::ids::TypeVar,
    result_tv: crate::ids::TypeVar,
    result_eff: crate::ids::TypeVar,
    node: &SyntaxNode,
) {
    state.record_expected_adapter_edge(
        ExpectedAdapterEdgeKind::HandlerResidual,
        None,
        Some(scrutinee_tv),
        Some(result_tv),
        Some(scrutinee_eff),
        Some(result_eff),
        ConstraintCause {
            span: Some(node.text_range()),
            reason: ConstraintReason::CatchBranch,
        },
    );
}

struct EffectOpUse {
    pos_sig: crate::ids::PosId,
    neg_sig: crate::ids::NegId,
    args: Vec<(crate::ids::TypeVar, crate::ids::TypeVar)>,
}

fn instantiate_effect_op_use(
    state: &mut LowerState,
    def: crate::ids::DefId,
    effect_path: &Path,
    effect_arg_substs: &mut HashMap<Path, HashMap<crate::ids::TypeVar, crate::ids::TypeVar>>,
) -> Option<EffectOpUse> {
    let start = Instant::now();
    let pos_sig = state.effect_op_pos_sigs.get(&def)?;
    let neg_sig = state.effect_op_neg_sigs.get(&def)?;
    let args = state
        .effect_op_args
        .get(&def)
        .map(Vec::as_slice)
        .unwrap_or(&[]);

    let subst = effect_arg_substs
        .entry(effect_path.clone())
        .or_insert_with(HashMap::new);
    for &(pos, neg) in args {
        if !subst.contains_key(&pos) {
            subst.insert(pos, state.fresh_tv());
        }
        if !subst.contains_key(&neg) {
            let fresh = subst.get(&pos).copied().unwrap_or_else(|| state.fresh_tv());
            subst.insert(neg, fresh);
        }
    }

    let mut vars = collect_pos_free_vars(&state.infer, *pos_sig);
    vars.extend(collect_neg_free_vars(&state.infer, *neg_sig));
    for &(pos, neg) in args {
        vars.push(pos);
        vars.push(neg);
    }
    vars.sort_by_key(|tv| tv.0);
    vars.dedup();

    for tv in vars {
        subst.entry(tv).or_insert_with(|| state.fresh_tv());
    }
    let result = Some(EffectOpUse {
        pos_sig: subst_pos_id_map(&state.infer, *pos_sig, subst),
        neg_sig: subst_neg_id_map(&state.infer, *neg_sig, subst),
        args: args
            .into_iter()
            .map(|&(pos, neg)| {
                (
                    subst.get(&pos).copied().unwrap_or(pos),
                    subst.get(&neg).copied().unwrap_or(neg),
                )
            })
            .collect(),
    });
    state.lower_detail.instantiate_effect_op_use += start.elapsed();
    result
}

fn resolve_effect_op_def(state: &LowerState, op_path: &Path) -> Option<crate::ids::DefId> {
    let def = state.ctx.resolve_path_value(op_path)?;
    if state.effect_op_args.contains_key(&def) {
        return Some(def);
    }

    let canonical = state
        .ctx
        .canonical_value_paths()
        .get(&def)
        .cloned()
        .unwrap_or_else(|| op_path.clone());
    state.same_path_effect_op_for_path(&canonical)
}

fn lower_catch_arm(
    state: &mut LowerState,
    node: &SyntaxNode,
    resume_result: (crate::ids::TypeVar, crate::ids::TypeVar),
) -> RawLoweredCatchArm {
    use crate::ast::expr::{PatKind, TypedPat};
    let start = Instant::now();

    let tv = state.fresh_tv();
    let pats: Vec<_> = node
        .children()
        .filter(|c| {
            matches!(
                c.kind(),
                SyntaxKind::Pattern
                    | SyntaxKind::PatOr
                    | SyntaxKind::PatAs
                    | SyntaxKind::PatParenGroup
            )
        })
        .collect();

    state.ctx.push_local();
    let mut guard;
    let mut guard_eff = None;
    let kind = if pats.len() >= 2 {
        let op_pat = pats[0].clone();
        let k_pat = pats[1].clone();
        let path_start = Instant::now();
        let op_path = extract_catch_effect_path(&op_pat).unwrap_or_else(|| Path {
            segments: vec![Name("<unknown>".to_string())],
        });
        state.lower_detail.extract_catch_effect_path += path_start.elapsed();

        let payload_pat = lower_catch_effect_payload_pat(state, &op_pat);

        let k = state.fresh_def();
        let k_tv = state.fresh_tv();
        state.register_def_tv(k, k_tv);
        state.mark_continuation_def(k);
        state.register_continuation_result_eff_tv(k, resume_result.1);
        if let Some(owner) = state.current_owner {
            state.register_def_owner(k, owner);
        }
        if let Some(k_name) = simple_ident_name(&k_pat) {
            state.register_def_name(k, k_name.clone());
            state.ctx.bind_local(k_name, k);
        }

        guard = lower_arm_guard(state, node);
        let body = node
            .children()
            .find(|c| {
                matches!(
                    c.kind(),
                    SyntaxKind::Expr | SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                )
            })
            .map(|c| lower_expr(state, &c))
            .unwrap_or_else(|| unit_expr(state));
        if let Some(guard_expr) = guard.take() {
            let cause = ConstraintCause {
                span: Some(node.text_range()),
                reason: ConstraintReason::CatchGuard,
            };
            let expected_bool_tv = fresh_exact_bool_tv(state, &cause);
            let expected_guard_eff = state.fresh_tv();
            guard_eff = Some(expected_guard_eff);
            guard = Some(
                state
                    .implicit_cast_boundary_with_effects(
                        guard_expr,
                        expected_bool_tv,
                        expected_guard_eff,
                        ExpectedEdgeKind::CatchGuard,
                        cause,
                        false,
                    )
                    .0,
            );
        }
        connect_pat_shape_and_locals(state, &payload_pat, body.eff);

        CatchArmKind::Effect {
            op_path,
            pat: payload_pat,
            k,
            body,
        }
    } else {
        let pat_node = pats.first().cloned();
        if let Some(pat_node) = &pat_node {
            bind_pattern_locals(state, pat_node);
        }
        let pat = pat_node
            .as_ref()
            .map(|c| lower_pat(state, c))
            .unwrap_or(TypedPat {
                tv: state.fresh_tv(),
                kind: PatKind::Wild,
            });

        guard = lower_arm_guard(state, node);
        let body = node
            .children()
            .find(|c| {
                matches!(
                    c.kind(),
                    SyntaxKind::Expr | SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                )
            })
            .map(|c| lower_expr(state, &c))
            .unwrap_or_else(|| unit_expr(state));
        if let Some(guard_expr) = guard.take() {
            let cause = ConstraintCause {
                span: Some(node.text_range()),
                reason: ConstraintReason::CatchGuard,
            };
            let expected_bool_tv = fresh_exact_bool_tv(state, &cause);
            let expected_guard_eff = state.fresh_tv();
            guard_eff = Some(expected_guard_eff);
            guard = Some(
                state
                    .implicit_cast_boundary_with_effects(
                        guard_expr,
                        expected_bool_tv,
                        expected_guard_eff,
                        ExpectedEdgeKind::CatchGuard,
                        cause,
                        false,
                    )
                    .0,
            );
        }
        connect_pat_shape_and_locals(state, &pat, body.eff);

        CatchArmKind::Value(pat, body)
    };
    state.ctx.pop_local();
    let result = RawLoweredCatchArm {
        arm: TypedCatchArm { tv, guard, kind },
        guard_eff,
    };
    state.lower_detail.lower_catch_arm += start.elapsed();
    result
}

fn fresh_exact_bool_tv(state: &mut LowerState, cause: &ConstraintCause) -> crate::ids::TypeVar {
    let tv = state.fresh_tv();
    state
        .infer
        .constrain_with_cause(prim_type("bool"), Neg::Var(tv), cause.clone());
    state
        .infer
        .constrain_with_cause(Pos::Var(tv), neg_prim_type("bool"), cause.clone());
    tv
}

fn extract_catch_effect_path(node: &SyntaxNode) -> Option<Path> {
    let mut segs = Vec::new();

    if let Some(tok) = node
        .children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::Ident)
    {
        segs.push(Name(tok.text().to_string()));
    }

    for child in node.children().filter(|c| c.kind() == SyntaxKind::PathSep) {
        if let Some(tok) = child
            .children_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|t| t.kind() == SyntaxKind::Ident)
        {
            segs.push(Name(tok.text().to_string()));
        }
    }

    if segs.is_empty() {
        None
    } else {
        Some(Path { segments: segs })
    }
}

fn effect_scope_path(path: &Path) -> Path {
    match path.segments.first() {
        Some(first) => Path {
            segments: vec![first.clone()],
        },
        None => path.clone(),
    }
}

fn lower_catch_effect_payload_pat(
    state: &mut LowerState,
    node: &SyntaxNode,
) -> crate::ast::expr::TypedPat {
    use crate::ast::expr::{PatKind, TypedPat};
    let start = Instant::now();

    let payloads = node
        .children()
        .filter(|c| matches!(c.kind(), SyntaxKind::ApplyML | SyntaxKind::ApplyC))
        .flat_map(|apply| {
            apply
                .children()
                .filter(|c| {
                    matches!(
                        c.kind(),
                        SyntaxKind::Pattern
                            | SyntaxKind::PatOr
                            | SyntaxKind::PatAs
                            | SyntaxKind::PatParenGroup
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let result = match payloads.len() {
        0 => TypedPat {
            tv: state.fresh_tv(),
            kind: PatKind::Wild,
        },
        1 => {
            bind_pattern_locals(state, &payloads[0]);
            lower_pat(state, &payloads[0])
        }
        _ => {
            for payload in &payloads {
                bind_pattern_locals(state, payload);
            }
            let pats = payloads
                .into_iter()
                .map(|payload| lower_pat(state, &payload))
                .collect::<Vec<_>>();
            TypedPat {
                tv: state.fresh_tv(),
                kind: PatKind::Tuple(pats),
            }
        }
    };
    state.lower_detail.lower_catch_effect_payload_pat += start.elapsed();
    result
}

fn simple_ident_name(node: &SyntaxNode) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::Ident)
        .map(|t| Name(t.text().to_string()))
}
