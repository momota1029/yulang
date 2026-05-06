use yulang_core_ir as core_ir;
use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, Lit, PatKind, TypedExpr, TypedPat};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

pub(crate) fn lower_struct_with_bindings(
    state: &mut LowerState,
    node: &SyntaxNode,
    struct_path: &Path,
    type_param_names: &[String],
    type_arg_tvs: &[crate::ids::TypeVar],
) {
    let Some(with_block) = super::super::child_node(node, SyntaxKind::IndentBlock)
        .or_else(|| super::super::child_node(node, SyntaxKind::BraceGroup))
    else {
        return;
    };

    for item in with_block.children() {
        match item.kind() {
            SyntaxKind::Binding => {
                lower_struct_with_binding(state, &item, struct_path, type_arg_tvs);
            }
            SyntaxKind::ImplDecl => {
                super::super::lower_attached_impl_decl(state, &item, struct_path, type_param_names);
            }
            _ => {}
        }
    }
}

pub(crate) fn lower_struct_with_binding(
    state: &mut LowerState,
    binding: &SyntaxNode,
    struct_path: &Path,
    type_arg_tvs: &[crate::ids::TypeVar],
) -> Option<()> {
    let header = super::super::child_node(binding, SyntaxKind::BindingHeader)?;
    let pattern = super::super::child_node(&header, SyntaxKind::Pattern)?;
    let method_name = pattern
        .children()
        .find(|c| c.kind() == SyntaxKind::Field)
        .and_then(|field| {
            field
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find(|t| t.kind() == SyntaxKind::DotField)
                .map(|t| Name(t.text().trim_start_matches('.').trim().to_string()))
        })?;
    let recv_name = super::super::ident_or_sigil_name(&pattern)?;
    let receiver_is_ref = recv_name.0.starts_with('&');
    let type_expr = super::super::child_node(&pattern, SyntaxKind::TypeAnn)
        .and_then(|ann| super::super::child_node(&ann, SyntaxKind::TypeExpr));

    let method_def = state.fresh_def();
    let method_tv = state.fresh_tv();
    let binding_name = if receiver_is_ref {
        Name(format!("#ref-method:{}:{}", method_name.0, method_def.0))
    } else {
        method_name.clone()
    };
    state.register_def_tv(method_def, method_tv);
    state.register_def_name(method_def, binding_name.clone());
    state.insert_value(state.ctx.current_module, binding_name, method_def);
    if receiver_is_ref {
        state
            .infer
            .register_ref_type_method(struct_path.clone(), method_name.clone(), method_def);
    }

    let mut arg_pats: Vec<super::super::ArgPatInfo> = super::super::collect_header_args(&pattern)
        .into_iter()
        .map(|arg| super::super::make_arg_pat_info(state, arg))
        .collect();
    if arg_pats.first().is_some_and(|arg_pat| {
        arg_pat
            .local_bindings
            .iter()
            .any(|(name, _)| *name == recv_name)
    }) {
        arg_pats.remove(0);
    }
    for arg_pat in &arg_pats {
        state.register_def_owner(arg_pat.def, method_def);
        for (_, def) in &arg_pat.local_bindings {
            state.register_def_owner(*def, method_def);
        }
    }

    let recv_def = state.fresh_def();
    let recv_tv = state.fresh_tv();
    state.register_def_tv(recv_def, recv_tv);
    state.register_def_name(recv_def, recv_name.clone());
    state.register_def_owner(recv_def, method_def);
    if receiver_is_ref {
        constrain_ref_method_receiver(state, recv_tv, struct_path, type_arg_tvs);
    } else {
        constrain_value_method_receiver(state, recv_tv, struct_path, type_arg_tvs);
    }

    let body_node = super::super::child_node(binding, SyntaxKind::BindingBody);
    let body = if let Some(body_node) = body_node {
        state.ctx.push_local();
        state.ctx.bind_local(recv_name.clone(), recv_def);
        for arg_pat in &arg_pats {
            for (name, def) in &arg_pat.local_bindings {
                state.ctx.bind_local(name.clone(), *def);
            }
        }
        let body = state.with_owner(method_def, |state| {
            super::super::lower_binding_body(state, &body_node)
        });
        state.ctx.pop_local();
        body
    } else {
        let tv = state.fresh_tv();
        let eff = state.fresh_tv();
        TypedExpr {
            tv,
            eff,
            kind: ExprKind::Lit(Lit::Unit),
        }
    };
    let mut all_arg_pats = Vec::with_capacity(arg_pats.len() + 1);
    all_arg_pats.push(super::super::ArgPatInfo {
        def: recv_def,
        tv: recv_tv,
        arg_eff_tv: state.fresh_exact_pure_eff_tv(),
        read_eff_tv: None,
        pat: Some(TypedPat {
            tv: recv_tv,
            kind: PatKind::UnresolvedName(recv_name.clone()),
        }),
        local_bindings: vec![(recv_name, recv_def)],
        ann: None,
        unit_arg: false,
    });
    all_arg_pats.extend(arg_pats);
    let body = super::super::wrap_header_lambdas(state, body, all_arg_pats);
    state.principal_bodies.insert(method_def, body.clone());
    state
        .infer
        .constrain(Pos::Var(body.tv), Neg::Var(method_tv));
    state
        .infer
        .constrain(Pos::Var(method_tv), Neg::Var(body.tv));
    if let Some(type_expr) = type_expr {
        if let Some(sig) = crate::lower::signature::parse_sig_type_expr(&type_expr) {
            let pos_vars = state.current_type_scope().cloned().unwrap_or_default();
            let mut neg_vars = pos_vars.clone();
            let recv_pos = state.infer.alloc_pos(state.pos_con(
                struct_path.clone(),
                super::super::invariant_args(type_arg_tvs),
            ));
            let ret_neg =
                crate::lower::signature::lower_pure_sig_neg_id(state, &sig, &mut neg_vars);
            let neg_sig = state.infer.alloc_neg(Neg::Fun {
                arg: recv_pos,
                arg_eff: state.infer.arena.empty_pos_row,
                ret_eff: state.infer.arena.empty_neg_row,
                ret: ret_neg,
            });
            state.infer.constrain(Pos::Var(method_tv), neg_sig);
            state.runtime_export_schemes.insert(
                method_def,
                core_ir::Scheme {
                    requirements: Vec::new(),
                    body: core_ir::Type::Fun {
                        param: Box::new(super::super::export_runtime_struct_receiver_type(
                            state,
                            struct_path,
                            type_arg_tvs,
                        )),
                        param_effect: Box::new(core_ir::Type::Never),
                        ret_effect: Box::new(core_ir::Type::Never),
                        ret: Box::new(super::super::export_runtime_struct_method_type(state, &sig)),
                    },
                },
            );
        }
    }
    Some(())
}

fn constrain_value_method_receiver(
    state: &mut LowerState,
    recv_tv: crate::ids::TypeVar,
    struct_path: &Path,
    type_arg_tvs: &[crate::ids::TypeVar],
) {
    state.infer.constrain(
        state.pos_con(
            struct_path.clone(),
            super::super::invariant_args(type_arg_tvs),
        ),
        Neg::Var(recv_tv),
    );
    state.infer.constrain(
        Pos::Var(recv_tv),
        state.neg_con(
            struct_path.clone(),
            super::super::invariant_args(type_arg_tvs),
        ),
    );
}

fn constrain_ref_method_receiver(
    state: &mut LowerState,
    recv_tv: crate::ids::TypeVar,
    struct_path: &Path,
    type_arg_tvs: &[crate::ids::TypeVar],
) {
    let eff_tv = state.fresh_tv();
    let eff_tail_tv = state.fresh_tv();
    let value_tv = state.fresh_tv();
    state.infer.mark_through(eff_tail_tv);
    state.infer.constrain(
        Pos::Row(Vec::new(), state.infer.alloc_pos(Pos::Var(eff_tail_tv))),
        Neg::Var(eff_tv),
    );
    state.infer.constrain(
        Pos::Var(eff_tv),
        Neg::Row(Vec::new(), state.infer.alloc_neg(Neg::Var(eff_tail_tv))),
    );
    constrain_value_method_receiver(state, value_tv, struct_path, type_arg_tvs);
    let ref_args = [eff_tv, value_tv];
    let ref_path = std_var_ref_path();
    state.infer.constrain(
        state.pos_con(ref_path.clone(), super::super::invariant_args(&ref_args)),
        Neg::Var(recv_tv),
    );
    state.infer.constrain(
        Pos::Var(recv_tv),
        state.neg_con(ref_path, super::super::invariant_args(&ref_args)),
    );
}

fn std_var_ref_path() -> Path {
    Path {
        segments: vec![
            Name("std".to_string()),
            Name("var".to_string()),
            Name("ref".to_string()),
        ],
    }
}
