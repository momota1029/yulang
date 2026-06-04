use crate::profile::ProfileClock as Instant;
use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, PatKind, TypedExpr, TypedMatchArm, TypedPat, TypedStmt};
use crate::ids::TypeVar;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Path;

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
        let type_scope =
            fresh_binding_type_scope(state, &super::super::binding_sig_var_names(&header));
        lower_binding_with_type_scope(state, node, type_scope)
    })();
    state.lower_detail.lower_binding += start.elapsed();
    result
}

fn fresh_binding_type_scope(state: &LowerState, names: &[String]) -> HashMap<String, TypeVar> {
    let mut out = HashMap::new();
    let level = state.current_level.saturating_add(1);
    for name in names {
        out.entry(name.clone())
            .or_insert_with(|| state.fresh_tv_at(level));
    }
    out
}

pub(crate) fn lower_binding_with_type_scope(
    state: &mut LowerState,
    node: &SyntaxNode,
    type_scope: HashMap<String, TypeVar>,
) -> Option<TypedStmt> {
    let header = super::super::child_node(node, SyntaxKind::BindingHeader)
        .or_else(|| super::super::child_node(node, SyntaxKind::OpDefHeader))?;
    // 論文の typeLetRhs: named binding の RHS は lvl+1 で型付けする。
    // body 内で生まれる変数（catch residual など）が高レベルになり、
    // 外側依存（引数・外側 binding 参照）は低レベルのまま → constrain で extrude が低レベルコピーを作る。
    // 量化判定そのものは SCC + non_generic に任せる（approach B: level は extrude 駆動のみ）。
    state.enter_let();
    let result = state.with_type_scope(type_scope, |state| {
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
            PatKind::As(inner, def) if matches!(inner.kind, PatKind::Wild) => Some(*def),
            _ => None,
        };
        if let Some(owner) = owner {
            super::super::preconstrain_recursive_binding_header_shape(
                state,
                owner,
                &arg_pats,
                Some(&header),
            );
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

        super::super::connect_binding_body_effect_annotation(state, &header, raw_body.eff);
        let cast_body = super::super::apply_binding_type_annotation_cast(state, &header, raw_body);
        let body_expr = super::super::wrap_header_lambdas(state, cast_body, arg_pats);
        if let Some(def) = owner {
            state.insert_principal_body(def, body_expr.clone());
        }
        let self_used = owner
            .map(|owner| state.take_recursive_self_use(owner))
            .unwrap_or(false);
        if self_used {
            if let Some(owner) = owner {
                state.mark_recursive_binding(owner);
            }
        }
        insert_top_level_record_alias_principal_body(state, &bind_pat, &body_expr);
        super::super::connect_let_pattern(
            state,
            &bind_pat,
            body_expr.tv,
            body_expr.eff,
            body_span,
            self_used,
        );
        if owner.is_none() && state.current_owner.is_none() {
            insert_destructured_binding_principal_bodies(state, &bind_pat, &body_expr);
        }
        Some(TypedStmt::Let(bind_pat, body_expr))
    });
    state.leave_let();
    result
}

fn insert_destructured_binding_principal_bodies(
    state: &mut LowerState,
    bind_pat: &TypedPat,
    body_expr: &TypedExpr,
) {
    if matches!(bind_pat.kind, PatKind::UnresolvedName(_)) {
        return;
    }

    let mut defs = Vec::new();
    collect_destructured_binding_defs(state, bind_pat, &mut defs);
    for def in defs {
        if state.principal_bodies.contains_key(&def) {
            continue;
        }
        let Some(&tv) = state.def_tvs.get(&def) else {
            continue;
        };
        let value = TypedExpr {
            tv,
            eff: state.fresh_exact_pure_eff_tv(),
            kind: ExprKind::Var(def),
        };
        let body = TypedExpr {
            tv,
            eff: body_expr.eff,
            kind: ExprKind::Match(
                Box::new(body_expr.clone()),
                vec![TypedMatchArm {
                    pat: bind_pat.clone(),
                    guard: None,
                    body: value,
                }],
            ),
        };
        state.insert_principal_body(def, body);
    }
}

fn insert_top_level_record_alias_principal_body(
    state: &mut LowerState,
    bind_pat: &TypedPat,
    body_expr: &TypedExpr,
) {
    let PatKind::As(inner, def) = &bind_pat.kind else {
        return;
    };
    if matches!(inner.kind, PatKind::Record { .. }) {
        let path = Path {
            segments: Vec::new(),
        };
        let copied = crate::lower::stmt::act::transform_copied_principal_body_with_subst(
            state,
            body_expr,
            &HashMap::new(),
            &[],
            &path,
            &[],
            &path,
            &[],
        )
        .body;
        state.register_def_tv(*def, copied.tv);
        state.insert_principal_body(*def, copied);
    }
}

fn collect_destructured_binding_defs(
    state: &LowerState,
    pat: &TypedPat,
    out: &mut Vec<crate::ids::DefId>,
) {
    match &pat.kind {
        PatKind::UnresolvedName(name) => {
            if let Some(def) = state.ctx.resolve_bound_value(name)
                && !out.contains(&def)
            {
                out.push(def);
            }
        }
        PatKind::As(inner, def) => {
            collect_destructured_binding_defs(state, inner, out);
            if !out.contains(def) {
                out.push(*def);
            }
        }
        PatKind::Tuple(items) | PatKind::PolyVariant(_, items) => {
            for item in items {
                collect_destructured_binding_defs(state, item, out);
            }
        }
        PatKind::List {
            prefix,
            spread,
            suffix,
        } => {
            for item in prefix {
                collect_destructured_binding_defs(state, item, out);
            }
            if let Some(spread) = spread {
                collect_destructured_binding_defs(state, spread, out);
            }
            for item in suffix {
                collect_destructured_binding_defs(state, item, out);
            }
        }
        PatKind::Record { spread, fields } => {
            for field in fields {
                collect_destructured_binding_defs(state, &field.pat, out);
            }
            if let Some(spread) = spread {
                match spread {
                    crate::ast::expr::RecordPatSpread::Head(pat)
                    | crate::ast::expr::RecordPatSpread::Tail(pat) => {
                        collect_destructured_binding_defs(state, pat, out);
                    }
                }
            }
        }
        PatKind::Con(_, Some(payload)) => {
            collect_destructured_binding_defs(state, payload, out);
        }
        PatKind::Or(lhs, rhs) => {
            collect_destructured_binding_defs(state, lhs, out);
            collect_destructured_binding_defs(state, rhs, out);
        }
        PatKind::Wild | PatKind::Lit(_) | PatKind::Con(_, None) => {}
    }
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

    super::super::preconstrain_recursive_binding_header_shape(state, def, &arg_pats, Some(header));

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

    super::super::connect_binding_body_effect_annotation(state, header, raw_body.eff);
    let cast_body = super::super::apply_binding_type_annotation_cast(state, header, raw_body);
    let body_expr = super::super::wrap_header_lambdas(state, cast_body, arg_pats);
    state.insert_principal_body(def, body_expr.clone());
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
