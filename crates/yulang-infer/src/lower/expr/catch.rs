use crate::profile::ProfileClock as Instant;
use std::collections::{HashMap, HashSet};

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{CatchArmKind, ExprKind, TypedCatchArm, TypedExpr};
use crate::diagnostic::{ConstraintCause, ConstraintReason, ExpectedEdgeKind};
use crate::lower::stmt::{bind_pattern_locals, connect_pat_shape_and_locals, lower_pat};
use crate::lower::{LowerState, SyntaxNode};
use crate::scheme::{
    collect_neg_free_vars, collect_pos_free_vars, subst_neg_id_map, subst_pos_id_map,
};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

use super::control::lower_arm_guard;
use super::{collect_child_arms, lower_expr, neg_prim_type, prim_type, unit_expr};

pub(super) fn lower_catch(state: &mut LowerState, node: &SyntaxNode) -> TypedExpr {
    let start = Instant::now();

    let result = (|| {
        let tv = state.fresh_tv();
        let eff = state.fresh_tv();

        let comp = node
            .children()
            .find(|c| c.kind() == SyntaxKind::Expr)
            .map(|c| lower_expr(state, &c))
            .unwrap_or_else(|| unit_expr(state));

        let arms: Vec<TypedCatchArm> = node
            .children()
            .filter(|c| c.kind() == SyntaxKind::CatchBlock)
            .flat_map(|b| collect_child_arms(&b, SyntaxKind::CatchArm))
            .map(|arm| lower_catch_arm(state, &arm, (comp.tv, comp.eff)))
            .collect();

        let mut saw_value_arm = false;
        let mut handled_ops = Vec::new();
        let mut handled_pos_ops = Vec::new();
        let mut effect_arg_substs: HashMap<
            Path,
            HashMap<crate::ids::TypeVar, crate::ids::TypeVar>,
        > = HashMap::new();
        for arm in &arms {
            match &arm.kind {
                CatchArmKind::Value(pat, body) => {
                    saw_value_arm = true;
                    state.record_expected_edge_with_effects(
                        body.tv,
                        tv,
                        Some(body.eff),
                        Some(eff),
                        ExpectedEdgeKind::CatchBranch,
                        ConstraintCause {
                            span: None,
                            reason: ConstraintReason::IfBranch,
                        },
                    );
                    state.infer.constrain(Pos::Var(body.tv), Neg::Var(tv));
                    state.infer.constrain(Pos::Var(body.eff), Neg::Var(eff));
                    state.infer.constrain(Pos::Var(comp.tv), Neg::Var(pat.tv));
                }
                CatchArmKind::Effect {
                    op_path,
                    pat,
                    k,
                    body,
                } => {
                    let op_def = state.ctx.resolve_path_value(op_path);
                    let effect_path = op_def
                        .and_then(|def| state.effect_op_effect_paths.get(&def).cloned())
                        .unwrap_or_else(|| effect_scope_path(op_path));
                    let op_use = op_def.and_then(|def| {
                        instantiate_effect_op_use(state, def, &effect_path, &mut effect_arg_substs)
                    });
                    let handled_atom = crate::types::EffectAtom {
                        path: effect_path.clone(),
                        args: op_use
                            .as_ref()
                            .map(|op| op.args.clone())
                            .unwrap_or_else(|| {
                                (0..state.effect_arities.get(&effect_path).copied().unwrap_or(0))
                                    .map(|_| {
                                        let pos = state.fresh_tv();
                                        let neg = state.fresh_tv();
                                        (pos, neg)
                                    })
                                    .collect()
                            }),
                    };
                    constrain_existing_comp_effect_atoms(state, comp.eff, &handled_atom);
                    let handled_op = Neg::Atom(handled_atom.clone());
                    handled_ops.push(handled_op.clone());
                    handled_pos_ops.push(Pos::Atom(handled_atom));

                    let resume_tv = state.fresh_tv();
                    let op_call_eff = state.fresh_tv();
                    if let Some(op_use) = op_use {
                        let pos_sig = state.infer.arena.get_pos(op_use.pos_sig);
                        let neg_sig = state.infer.arena.get_neg(op_use.neg_sig);
                        let (
                            Pos::Fun {
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
                        state.infer.constrain(op_ret_eff_pos, Neg::Var(op_call_eff));
                        state.infer.constrain(Pos::Var(op_call_eff), op_ret_eff_neg);
                        state.infer.constrain(op_ret_pos, Neg::Var(resume_tv));
                        state.infer.constrain(Pos::Var(resume_tv), op_ret_neg);
                        state.infer.constrain(
                            Pos::Var(op_call_eff),
                            state.neg_row(vec![handled_op.clone()], Neg::Top),
                        );
                    }

                    if let Some(&k_tv) = state.def_tvs.get(k) {
                        let k_arg_eff = state.fresh_tv();
                        let k_fun = state.pos_fun(
                            Neg::Var(resume_tv),
                            Neg::Var(k_arg_eff),
                            Pos::Var(comp.eff),
                            Pos::Var(comp.tv),
                        );
                        state.infer.constrain(k_fun.clone(), Neg::Var(k_tv));
                        state.infer.constrain(
                            Pos::Var(k_tv),
                            state.neg_fun(
                                Pos::Var(resume_tv),
                                Pos::Var(k_arg_eff),
                                Neg::Var(comp.eff),
                                Neg::Var(comp.tv),
                            ),
                        );
                    }

                    state.record_expected_edge_with_effects(
                        body.tv,
                        tv,
                        Some(body.eff),
                        Some(eff),
                        ExpectedEdgeKind::CatchBranch,
                        ConstraintCause {
                            span: None,
                            reason: ConstraintReason::IfBranch,
                        },
                    );
                    state.infer.constrain(Pos::Var(body.tv), Neg::Var(tv));
                    state.infer.constrain(Pos::Var(body.eff), Neg::Var(eff));
                }
            }
        }

        if !saw_value_arm {
            state.infer.constrain(Pos::Var(comp.tv), Neg::Var(tv));
            state.infer.constrain(Pos::Var(tv), Neg::Var(comp.tv));
        }

        if handled_ops.is_empty() {
            state.infer.constrain(Pos::Var(comp.eff), Neg::Var(eff));
        } else if saw_value_arm {
            let rest_eff = state.fresh_tv();
            state.infer.mark_through(rest_eff);
            state.infer.constrain(
                state.pos_row(handled_pos_ops, Pos::Var(rest_eff)),
                Neg::Var(comp.eff),
            );
            state.infer.constrain(
                Pos::Var(comp.eff),
                state.neg_row(handled_ops.clone(), Neg::Var(rest_eff)),
            );
            state.infer.constrain(Pos::Var(rest_eff), Neg::Var(eff));
        } else {
            let rest_eff = state.fresh_tv();
            state.infer.mark_through(rest_eff);
            state.infer.constrain(
                state.pos_row(handled_pos_ops, Pos::Var(rest_eff)),
                Neg::Var(comp.eff),
            );
            state.infer.constrain(
                Pos::Var(comp.eff),
                state.neg_row(handled_ops.clone(), Neg::Var(rest_eff)),
            );
            for arm in &arms {
                if let CatchArmKind::Effect { body, .. } = &arm.kind {
                    state.infer.constrain(
                        state.pos_row(vec![], Pos::Var(rest_eff)),
                        Neg::Var(body.eff),
                    );
                }
            }
        }

        TypedExpr {
            tv,
            eff,
            kind: ExprKind::Catch(Box::new(comp), arms),
        }
    })();
    state.lower_detail.lower_catch += start.elapsed();
    result
}

struct EffectOpUse {
    pos_sig: crate::ids::PosId,
    neg_sig: crate::ids::NegId,
    args: Vec<(crate::ids::TypeVar, crate::ids::TypeVar)>,
}

fn constrain_existing_comp_effect_atoms(
    state: &mut LowerState,
    comp_eff: crate::ids::TypeVar,
    handled_atom: &crate::types::EffectAtom,
) {
    let debug = std::env::var_os("YULANG_DEBUG_CATCH").is_some();
    if debug {
        eprintln!("-- constrain_existing_comp_effect_atoms --");
        eprintln!("comp_eff tv = {:?}", comp_eff);
        eprintln!("handled = {:?}", handled_atom);
        eprintln!("lowers = {:?}", state.infer.lowers_of(comp_eff));
        eprintln!("uppers = {:?}", state.infer.uppers_of(comp_eff));
        eprintln!(
            "compact lowers = {:?}",
            state.infer.compact_lower_instances_of(comp_eff)
        );
        debug_dump_effect_tv(state, comp_eff, 0, &mut HashSet::new());
    }
    let mut seen_tvs = HashSet::new();
    let mut seen_pos = HashSet::new();
    let mut seen_neg = HashSet::new();
    let mut matched = HashSet::new();
    seen_tvs.insert(comp_eff);

    for lower in state.infer.lower_refs_of(comp_eff) {
        collect_matching_effect_atoms_from_pos(
            state,
            lower,
            &handled_atom.path,
            handled_atom.args.len(),
            &mut seen_tvs,
            &mut seen_pos,
            &mut seen_neg,
            &mut matched,
        );
    }
    for upper in state.infer.upper_refs_of(comp_eff) {
        collect_matching_effect_atoms_from_neg(
            state,
            upper,
            &handled_atom.path,
            handled_atom.args.len(),
            &mut seen_tvs,
            &mut seen_pos,
            &mut seen_neg,
            &mut matched,
        );
    }

    if debug {
        eprintln!("matched = {:?}", matched);
    }
    for existing in matched {
        for ((handled_pos, handled_neg), (existing_pos, existing_neg)) in
            handled_atom.args.iter().zip(existing.args.iter())
        {
            state
                .infer
                .constrain(Pos::Var(*handled_pos), Neg::Var(*existing_neg));
            state
                .infer
                .constrain(Pos::Var(*existing_pos), Neg::Var(*handled_neg));
        }
    }
}

pub(super) fn debug_dump_effect_tv(
    state: &LowerState,
    tv: crate::ids::TypeVar,
    depth: usize,
    seen: &mut HashSet<crate::ids::TypeVar>,
) {
    if !seen.insert(tv) || depth > 3 {
        return;
    }
    let indent = "  ".repeat(depth);
    eprintln!("{indent}tv {tv:?}");
    eprintln!("{indent}  lowers {:?}", state.infer.lowers_of(tv));
    eprintln!("{indent}  uppers {:?}", state.infer.uppers_of(tv));
    eprintln!(
        "{indent}  compact {:?}",
        state.infer.compact_lower_instances_of(tv)
    );
    for lower in state.infer.lowers_of(tv) {
        if let Pos::Var(next) | Pos::Raw(next) = lower {
            debug_dump_effect_tv(state, next, depth + 1, seen);
        }
    }
    for upper in state.infer.uppers_of(tv) {
        if let Neg::Var(next) = upper {
            debug_dump_effect_tv(state, next, depth + 1, seen);
        }
    }
}

fn collect_matching_effect_atoms_from_pos(
    state: &LowerState,
    pos: crate::ids::PosId,
    effect_path: &Path,
    arity: usize,
    seen_tvs: &mut HashSet<crate::ids::TypeVar>,
    seen_pos: &mut HashSet<crate::ids::PosId>,
    seen_neg: &mut HashSet<crate::ids::NegId>,
    out: &mut HashSet<crate::types::EffectAtom>,
) {
    if !seen_pos.insert(pos) {
        return;
    }
    match state.infer.arena.get_pos(pos) {
        Pos::Atom(atom) if atom.path == *effect_path && atom.args.len() == arity => {
            out.insert(atom);
        }
        Pos::Var(tv) | Pos::Raw(tv) => {
            if seen_tvs.insert(tv) {
                for lower in state.infer.lower_refs_of(tv) {
                    collect_matching_effect_atoms_from_pos(
                        state,
                        lower,
                        effect_path,
                        arity,
                        seen_tvs,
                        seen_pos,
                        seen_neg,
                        out,
                    );
                }
                for instance in state.infer.compact_lower_instances_of(tv) {
                    let body = state.infer.materialize_compact_lower_instance(&instance);
                    collect_matching_effect_atoms_from_pos(
                        state,
                        body,
                        effect_path,
                        arity,
                        seen_tvs,
                        seen_pos,
                        seen_neg,
                        out,
                    );
                }
                for upper in state.infer.upper_refs_of(tv) {
                    collect_matching_effect_atoms_from_neg(
                        state,
                        upper,
                        effect_path,
                        arity,
                        seen_tvs,
                        seen_pos,
                        seen_neg,
                        out,
                    );
                }
            }
        }
        Pos::Row(items, tail) => {
            for item in items {
                collect_matching_effect_atoms_from_pos(
                    state,
                    item,
                    effect_path,
                    arity,
                    seen_tvs,
                    seen_pos,
                    seen_neg,
                    out,
                );
            }
            collect_matching_effect_atoms_from_pos(
                state,
                tail,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
        }
        Pos::Union(a, b) => {
            collect_matching_effect_atoms_from_pos(
                state,
                a,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
            collect_matching_effect_atoms_from_pos(
                state,
                b,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
        }
        Pos::Fun {
            arg_eff, ret_eff, ..
        } => {
            collect_matching_effect_atoms_from_neg(
                state,
                arg_eff,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
            collect_matching_effect_atoms_from_pos(
                state,
                ret_eff,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
        }
        Pos::Forall(_, body) => {
            collect_matching_effect_atoms_from_pos(
                state,
                body,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
        }
        _ => {}
    }
}

fn collect_matching_effect_atoms_from_neg(
    state: &LowerState,
    neg: crate::ids::NegId,
    effect_path: &Path,
    arity: usize,
    seen_tvs: &mut HashSet<crate::ids::TypeVar>,
    seen_pos: &mut HashSet<crate::ids::PosId>,
    seen_neg: &mut HashSet<crate::ids::NegId>,
    out: &mut HashSet<crate::types::EffectAtom>,
) {
    if !seen_neg.insert(neg) {
        return;
    }
    match state.infer.arena.get_neg(neg) {
        Neg::Atom(atom) if atom.path == *effect_path && atom.args.len() == arity => {
            out.insert(atom);
        }
        Neg::Var(tv) => {
            if seen_tvs.insert(tv) {
                for lower in state.infer.lower_refs_of(tv) {
                    collect_matching_effect_atoms_from_pos(
                        state,
                        lower,
                        effect_path,
                        arity,
                        seen_tvs,
                        seen_pos,
                        seen_neg,
                        out,
                    );
                }
                for instance in state.infer.compact_lower_instances_of(tv) {
                    let body = state.infer.materialize_compact_lower_instance(&instance);
                    collect_matching_effect_atoms_from_pos(
                        state,
                        body,
                        effect_path,
                        arity,
                        seen_tvs,
                        seen_pos,
                        seen_neg,
                        out,
                    );
                }
                for upper in state.infer.upper_refs_of(tv) {
                    collect_matching_effect_atoms_from_neg(
                        state,
                        upper,
                        effect_path,
                        arity,
                        seen_tvs,
                        seen_pos,
                        seen_neg,
                        out,
                    );
                }
            }
        }
        Neg::Row(items, tail) => {
            for item in items {
                collect_matching_effect_atoms_from_neg(
                    state,
                    item,
                    effect_path,
                    arity,
                    seen_tvs,
                    seen_pos,
                    seen_neg,
                    out,
                );
            }
            collect_matching_effect_atoms_from_neg(
                state,
                tail,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
        }
        Neg::Intersection(a, b) => {
            collect_matching_effect_atoms_from_neg(
                state,
                a,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
            collect_matching_effect_atoms_from_neg(
                state,
                b,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
        }
        Neg::Fun {
            arg_eff, ret_eff, ..
        } => {
            collect_matching_effect_atoms_from_pos(
                state,
                arg_eff,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
            collect_matching_effect_atoms_from_neg(
                state,
                ret_eff,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
        }
        Neg::Forall(_, body) => {
            collect_matching_effect_atoms_from_neg(
                state,
                body,
                effect_path,
                arity,
                seen_tvs,
                seen_pos,
                seen_neg,
                out,
            );
        }
        _ => {}
    }
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

fn lower_catch_arm(
    state: &mut LowerState,
    node: &SyntaxNode,
    _resume_result: (crate::ids::TypeVar, crate::ids::TypeVar),
) -> crate::ast::expr::TypedCatchArm {
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
    let guard = lower_arm_guard(state, node);
    let kind = if pats.len() >= 2 {
        let op_pat = pats[0].clone();
        let k_pat = pats[1].clone();
        let path_start = Instant::now();
        let op_path = extract_catch_effect_path(&op_pat).unwrap_or_else(|| Path {
            segments: vec![Name("<unknown>".to_string())],
        });
        state.lower_detail.extract_catch_effect_path += path_start.elapsed();

        bind_pattern_locals(state, &op_pat);
        let payload_pat = lower_catch_effect_payload_pat(state, &op_pat);

        let k = state.fresh_def();
        let k_tv = state.fresh_tv();
        state.register_def_tv(k, k_tv);
        state.mark_continuation_def(k);
        if let Some(owner) = state.current_owner {
            state.register_def_owner(k, owner);
        }
        if let Some(k_name) = simple_ident_name(&k_pat) {
            state.register_def_name(k, k_name.clone());
            state.ctx.bind_local(k_name, k);
        }

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
        if let Some(guard) = guard.as_ref() {
            let cause = ConstraintCause {
                span: Some(node.text_range()),
                reason: ConstraintReason::IfCondition,
            };
            let expected_bool_tv = fresh_exact_bool_tv(state);
            state.record_expected_edge_with_effects(
                guard.tv,
                expected_bool_tv,
                Some(guard.eff),
                Some(body.eff),
                ExpectedEdgeKind::CatchGuard,
                cause.clone(),
            );
            state.infer.constrain_with_cause(
                Pos::Var(guard.tv),
                neg_prim_type("bool"),
                cause.clone(),
            );
            state
                .infer
                .constrain_with_cause(prim_type("bool"), Neg::Var(guard.tv), cause);
            state
                .infer
                .constrain(Pos::Var(guard.eff), Neg::Var(body.eff));
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
        if let Some(guard) = guard.as_ref() {
            let cause = ConstraintCause {
                span: Some(node.text_range()),
                reason: ConstraintReason::IfCondition,
            };
            let expected_bool_tv = fresh_exact_bool_tv(state);
            state.record_expected_edge_with_effects(
                guard.tv,
                expected_bool_tv,
                Some(guard.eff),
                Some(body.eff),
                ExpectedEdgeKind::CatchGuard,
                cause.clone(),
            );
            state.infer.constrain_with_cause(
                Pos::Var(guard.tv),
                neg_prim_type("bool"),
                cause.clone(),
            );
            state
                .infer
                .constrain_with_cause(prim_type("bool"), Neg::Var(guard.tv), cause);
            state
                .infer
                .constrain(Pos::Var(guard.eff), Neg::Var(body.eff));
        }
        connect_pat_shape_and_locals(state, &pat, body.eff);

        CatchArmKind::Value(pat, body)
    };
    state.ctx.pop_local();
    let result = TypedCatchArm { tv, guard, kind };
    state.lower_detail.lower_catch_arm += start.elapsed();
    result
}

fn fresh_exact_bool_tv(state: &mut LowerState) -> crate::ids::TypeVar {
    let tv = state.fresh_tv();
    state.infer.constrain(prim_type("bool"), Neg::Var(tv));
    state.infer.constrain(Pos::Var(tv), neg_prim_type("bool"));
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
