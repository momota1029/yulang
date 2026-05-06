use crate::profile::ProfileClock as Instant;
use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{PatKind, TypedExpr, TypedPat, TypedStmt};
use crate::ids::TypeVar;
use crate::lower::{LowerState, SyntaxNode};

use super::super::GlobalExtensionMethodHeader;
use super::HeaderArg;

/// `my pat = body` / `our name = body` を TypedStmt::Let に lower する。
///
/// `my f x y = body` のような関数定義形式は `Lam(x, Lam(y, body))` に変換する。
pub(crate) fn lower_binding(state: &mut LowerState, node: &SyntaxNode) -> Option<TypedStmt> {
    let start = Instant::now();
    let result = (|| {
        let header = super::super::child_node(node, SyntaxKind::BindingHeader)
            .or_else(|| super::super::child_node(node, SyntaxKind::OpDefHeader))?;
        let type_scope = crate::lower::signature::fresh_type_scope(
            state,
            &super::super::binding_sig_var_names(&header),
        );
        lower_binding_with_type_scope(state, node, type_scope)
    })();
    state.lower_detail.lower_binding += start.elapsed();
    result
}

pub(crate) fn lower_binding_with_type_scope(
    state: &mut LowerState,
    node: &SyntaxNode,
    type_scope: HashMap<String, TypeVar>,
) -> Option<TypedStmt> {
    let header = super::super::child_node(node, SyntaxKind::BindingHeader)
        .or_else(|| super::super::child_node(node, SyntaxKind::OpDefHeader))?;
    state.with_type_scope(type_scope, |state| {
        if let Some(info) = super::super::global_extension_method_header(&header) {
            return lower_dotted_method_binding(state, node, &header, &info);
        }
        let body_node = super::super::child_node(node, SyntaxKind::BindingBody)
            .or_else(|| super::super::child_node(node, SyntaxKind::OpDefBody));
        let body_span = body_node.as_ref().map(|body| body.text_range());

        let lhs_start = Instant::now();
        let (bind_pat, arg_pats) = super::super::extract_binding_lhs(node, state, &header)?;
        state.lower_detail.extract_binding_lhs += lhs_start.elapsed();

        let owner = match &bind_pat.kind {
            PatKind::UnresolvedName(name) => state.ctx.resolve_value(name),
            PatKind::As(_, def) => Some(*def),
            _ => None,
        };
        if let Some(owner) = owner {
            super::super::preconstrain_recursive_binding_header_shape(state, owner, &arg_pats);
        }

        let raw_body = if let Some(body) = body_node {
            let scope_start = Instant::now();
            state.ctx.push_local();
            for arg_pat in &arg_pats {
                for (name, def) in &arg_pat.local_bindings {
                    state.ctx.bind_local(name.clone(), *def);
                }
            }
            if let Some(owner) = owner {
                if let Some(&tv) = state.provisional_self_root_tvs.get(&owner) {
                    let eff_tv = state
                        .def_eff_tvs
                        .get(&owner)
                        .copied()
                        .unwrap_or_else(|| state.fresh_exact_pure_eff_tv());
                    state.activate_recursive_self_instance(
                        owner,
                        crate::lower::ActiveRecursiveSelfInstance { tv, eff_tv },
                    );
                }
            }
            if let Some(owner) = owner {
                for arg_pat in &arg_pats {
                    state.register_def_owner(arg_pat.def, owner);
                    for (_, def) in &arg_pat.local_bindings {
                        state.register_def_owner(*def, owner);
                    }
                }
            }
            state.lower_detail.lower_binding_scope += scope_start.elapsed();
            let body = if let Some(owner) = owner {
                state.with_owner(owner, |state| {
                    super::super::lower_binding_body(state, &body)
                })
            } else {
                super::super::lower_binding_body(state, &body)
            };
            if let Some(owner) = owner {
                state.deactivate_recursive_self_instance(owner);
            }
            state.ctx.pop_local();
            body
        } else {
            let tv = state.fresh_tv();
            let eff = state.fresh_tv();
            TypedExpr {
                tv,
                eff,
                kind: crate::ast::expr::ExprKind::Lit(crate::ast::expr::Lit::Unit),
            }
        };

        let cast_body = if arg_pats.is_empty() {
            super::super::apply_binding_type_annotation_cast(state, &header, raw_body)
        } else {
            super::super::connect_binding_type_annotation(state, &header, raw_body.tv);
            raw_body
        };
        let body_expr = super::super::wrap_header_lambdas(state, cast_body, arg_pats);
        if let Some(def) = owner {
            state.principal_bodies.insert(def, body_expr.clone());
        }
        let self_used = owner
            .map(|owner| state.take_recursive_self_use(owner))
            .unwrap_or(false);
        if self_used {
            if let Some(owner) = owner {
                state.mark_recursive_binding(owner);
            }
        }
        super::super::connect_let_pattern(
            state,
            &bind_pat,
            body_expr.tv,
            body_expr.eff,
            body_span,
            self_used,
        );
        Some(TypedStmt::Let(bind_pat, body_expr))
    })
}

fn lower_dotted_method_binding(
    state: &mut LowerState,
    node: &SyntaxNode,
    header: &SyntaxNode,
    info: &GlobalExtensionMethodHeader,
) -> Option<TypedStmt> {
    let body_node = super::super::child_node(node, SyntaxKind::BindingBody)
        .or_else(|| super::super::child_node(node, SyntaxKind::OpDefBody));
    let body_span = body_node.as_ref().map(|body| body.text_range());
    let effect_path = state.current_act_effect_path.clone();
    let def = if effect_path.is_some() {
        super::super::current_module_effect_method_def(state, &info.name)?
    } else {
        super::super::current_module_extension_method_def(state, &info.name)?
    };
    let hidden_name = if let Some(effect_path) = &effect_path {
        super::super::effect_method_hidden_name(effect_path, &info.name, def)
    } else {
        super::super::extension_method_hidden_name(&info.name, def)
    };

    let mut arg_pats = Vec::new();
    arg_pats.push(super::super::make_arg_pat_info(
        state,
        HeaderArg::Pattern(info.recv_pat.clone()),
    ));
    arg_pats.extend(
        super::super::collect_header_args(&info.full_pat)
            .into_iter()
            .map(|header_arg| super::super::make_arg_pat_info(state, header_arg)),
    );
    let receiver_expects_computation = arg_pats
        .first()
        .and_then(|arg_pat| arg_pat.ann.as_ref())
        .and_then(|ann| ann.eff.as_ref())
        .is_some();
    if effect_path.is_some() {
        state
            .infer
            .set_effect_method_receiver_expects_computation(def, receiver_expects_computation);
    } else {
        state
            .infer
            .set_extension_method_receiver_expects_computation(def, receiver_expects_computation);
    }

    super::super::preconstrain_recursive_binding_header_shape(state, def, &arg_pats);

    let raw_body = if let Some(body) = body_node {
        state.ctx.push_local();
        for arg_pat in &arg_pats {
            for (name, def) in &arg_pat.local_bindings {
                state.ctx.bind_local(name.clone(), *def);
            }
        }
        if let Some(&tv) = state.provisional_self_root_tvs.get(&def) {
            let eff_tv = state
                .def_eff_tvs
                .get(&def)
                .copied()
                .unwrap_or_else(|| state.fresh_exact_pure_eff_tv());
            state.activate_recursive_self_instance(
                def,
                crate::lower::ActiveRecursiveSelfInstance { tv, eff_tv },
            );
        }
        for arg_pat in &arg_pats {
            state.register_def_owner(arg_pat.def, def);
            for (_, local_def) in &arg_pat.local_bindings {
                state.register_def_owner(*local_def, def);
            }
        }
        let body = state.with_owner(def, |state| super::super::lower_binding_body(state, &body));
        state.deactivate_recursive_self_instance(def);
        state.ctx.pop_local();
        body
    } else {
        let tv = state.fresh_tv();
        let eff = state.fresh_tv();
        TypedExpr {
            tv,
            eff,
            kind: crate::ast::expr::ExprKind::Lit(crate::ast::expr::Lit::Unit),
        }
    };

    let cast_body = if arg_pats.is_empty() {
        super::super::apply_binding_type_annotation_cast(state, header, raw_body)
    } else {
        super::super::connect_binding_type_annotation(state, header, raw_body.tv);
        raw_body
    };
    let body_expr = super::super::wrap_header_lambdas(state, cast_body, arg_pats);
    state.principal_bodies.insert(def, body_expr.clone());
    let bind_pat = TypedPat {
        tv: state.fresh_tv(),
        kind: PatKind::UnresolvedName(hidden_name),
    };
    let self_used = state.take_recursive_self_use(def);
    if self_used {
        state.mark_recursive_binding(def);
    }
    super::super::connect_let_pattern(
        state,
        &bind_pat,
        body_expr.tv,
        body_expr.eff,
        body_span,
        self_used,
    );
    Some(TypedStmt::Let(bind_pat, body_expr))
}
