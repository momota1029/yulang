use super::*;

use crate::types::{Neg, Pos};

/// `cast(x: A): B = body` を標準 `Cast A` impl として lowering する。
///
/// cast 宣言は暗黙の変換規則を増やすための定義で、使用側の特別構文は持たない。
/// 最初の核では source / target とも nominal 型だけを受け付ける。
pub(crate) fn lower_cast_decl(state: &mut LowerState, node: &SyntaxNode) {
    let impl_def = state.fresh_def();
    let Some(pattern) = child_node(node, SyntaxKind::Pattern) else {
        return;
    };
    let Some(source_type_expr) = child_node(&pattern, SyntaxKind::TypeAnn)
        .and_then(|ann| child_node(&ann, SyntaxKind::TypeExpr))
    else {
        return;
    };
    let target_anns = child_nodes(node, SyntaxKind::TypeAnn);
    let Some(target_type_expr) = target_anns
        .first()
        .and_then(|ann| child_node(ann, SyntaxKind::TypeExpr))
    else {
        return;
    };
    let Some(source_sig) = parse_sig_type_expr(&source_type_expr) else {
        return;
    };
    let Some(target_sig) = parse_sig_type_expr(&target_type_expr) else {
        return;
    };
    if !cast_sig_is_nominal(&source_sig) || !cast_sig_is_nominal(&target_sig) {
        return;
    }
    let Some(body_node) = child_node(node, SyntaxKind::BindingBody) else {
        return;
    };

    let role = cast_role_path(state);
    let role_infos = state.infer.role_arg_infos_of(&role);
    let assoc_eqs = HashMap::from([("to".to_string(), target_sig.clone())]);
    let mut impl_scope_names = Vec::new();
    collect_cast_sig_vars(&source_sig, &mut impl_scope_names);
    collect_cast_sig_vars(&target_sig, &mut impl_scope_names);
    for info in &role_infos {
        if !impl_scope_names.contains(&info.name) {
            impl_scope_names.push(info.name.clone());
        }
    }
    let impl_scope = fresh_type_scope(state, &impl_scope_names);
    let cast_name = Name("cast".to_string());
    let method_def = state.fresh_def();
    let method_tv = state.fresh_tv();
    state.register_def_tv(method_def, method_tv);
    state.mark_let_bound_def(method_def);
    state.register_def_owner(method_def, impl_def);
    state.register_def_name(method_def, cast_name.clone());

    let helper_module = state.ctx.modules.new_module();
    state.insert_module(
        state.ctx.current_module,
        Name(format!("&cast#{}", impl_def.0)),
        helper_module,
    );
    state.insert_value(helper_module, cast_name.clone(), method_def);

    state.with_type_scope(impl_scope.clone(), |state| {
        state.with_owner(impl_def, |state| {
            lower_cast_method_body(
                state,
                method_def,
                method_tv,
                &pattern,
                &body_node,
                &source_sig,
                &target_sig,
                &impl_scope,
            );
        });
    });

    let prerequisites = compact_role_constraints(&state.infer, impl_def);
    let (args, compact_args) = render_cast_impl_args(
        state,
        &role_infos,
        std::slice::from_ref(&source_sig),
        &assoc_eqs,
        &impl_scope,
    );
    state.infer.register_role_impl_candidate(RoleImplCandidate {
        role,
        args,
        compact_args,
        prerequisites,
        member_defs: HashMap::from([(cast_name, method_def)]),
        origins: impl_candidate_origins(state, node.text_range()),
    });
}

pub(crate) fn lower_synthetic_variant_cast(
    state: &mut LowerState,
    source_sig: &SigType,
    target_sig: &SigType,
    variant_name: &Name,
) {
    if !cast_sig_is_nominal(source_sig) || !cast_sig_is_nominal(target_sig) {
        return;
    }

    let impl_def = state.fresh_def();
    let role = cast_role_path(state);
    let role_infos = state.infer.role_arg_infos_of(&role);
    let assoc_eqs = HashMap::from([("to".to_string(), target_sig.clone())]);
    let mut impl_scope_names = Vec::new();
    collect_cast_sig_vars(source_sig, &mut impl_scope_names);
    collect_cast_sig_vars(target_sig, &mut impl_scope_names);
    for info in &role_infos {
        if !impl_scope_names.contains(&info.name) {
            impl_scope_names.push(info.name.clone());
        }
    }
    let impl_scope = fresh_type_scope(state, &impl_scope_names);
    let cast_name = Name("cast".to_string());
    let method_def = state.fresh_def();
    let method_tv = state.fresh_tv();
    state.register_def_tv(method_def, method_tv);
    state.mark_let_bound_def(method_def);
    state.register_def_owner(method_def, impl_def);
    state.register_def_name(method_def, cast_name.clone());

    let helper_module = state.ctx.modules.new_module();
    state.insert_module(
        state.ctx.current_module,
        Name(format!("&cast#{}", impl_def.0)),
        helper_module,
    );
    state.insert_value(helper_module, cast_name.clone(), method_def);

    state.with_type_scope(impl_scope.clone(), |state| {
        state.with_owner(impl_def, |state| {
            lower_synthetic_variant_cast_body(
                state,
                method_def,
                method_tv,
                source_sig,
                target_sig,
                variant_name,
                &impl_scope,
            );
        });
    });

    let prerequisites = compact_role_constraints(&state.infer, impl_def);
    let (args, compact_args) = render_cast_impl_args(
        state,
        &role_infos,
        std::slice::from_ref(source_sig),
        &assoc_eqs,
        &impl_scope,
    );
    state.infer.register_role_impl_candidate(RoleImplCandidate {
        role,
        args,
        compact_args,
        prerequisites,
        member_defs: HashMap::from([(cast_name, method_def)]),
        origins: impl_candidate_origins(state, source_sig.span()),
    });
}

fn lower_synthetic_variant_cast_body(
    state: &mut LowerState,
    method_def: crate::ids::DefId,
    method_tv: TypeVar,
    source_sig: &SigType,
    target_sig: &SigType,
    variant_name: &Name,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let arg_def = state.fresh_def();
    let arg_tv = state.fresh_tv();
    let arg_name = Name("value".to_string());
    state.register_def_tv(arg_def, arg_tv);
    state.register_def_name(arg_def, arg_name.clone());
    state.register_def_owner(arg_def, method_def);
    constrain_cast_arg_source(state, arg_tv, source_sig, impl_scope);

    let variant_tv = state.fresh_tv();
    let ret_tv = state.fresh_tv();
    let arg_expr = TypedExpr {
        tv: arg_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::Var(arg_def),
    };
    let variant = TypedExpr {
        tv: variant_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::PolyVariant(
            variant_name.clone(),
            vec![arg_expr],
            crate::ast::expr::PolyVariantOrigin::Constructor,
        ),
    };
    state.infer.constrain(
        state.pos_variant(vec![(variant_name.clone(), vec![Pos::Var(arg_tv)])]),
        Neg::Var(variant_tv),
    );
    state.infer.constrain(
        Pos::Var(variant_tv),
        Neg::PolyVariant(vec![(
            variant_name.clone(),
            vec![state.infer.alloc_neg(Neg::Var(arg_tv))],
        )]),
    );
    constrain_cast_result_target(state, ret_tv, target_sig, impl_scope);
    let body_eff = state.fresh_exact_pure_eff_tv();
    let body = state.representation_coerce(variant_tv, ret_tv, body_eff, variant);
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    let principal_body = wrap_header_lambdas(
        state,
        body.clone(),
        vec![ArgPatInfo {
            def: arg_def,
            tv: arg_tv,
            arg_eff_tv,
            read_eff_tv: None,
            pat: Some(TypedPat {
                tv: arg_tv,
                kind: crate::ast::expr::PatKind::UnresolvedName(arg_name.clone()),
            }),
            local_bindings: vec![(arg_name, arg_def)],
            ann: None,
            ann_non_generic_tvs: Vec::new(),
            unit_arg: false,
        }],
    );
    state.insert_principal_body(method_def, principal_body.clone());
    state
        .infer
        .constrain(Pos::Var(principal_body.tv), Neg::Var(method_tv));
    state
        .infer
        .constrain(Pos::Var(method_tv), Neg::Var(principal_body.tv));
    state.runtime_export_schemes.insert(
        method_def,
        runtime_export_scheme(state, source_sig, target_sig),
    );
}

fn cast_sig_is_nominal(sig: &SigType) -> bool {
    matches!(sig, SigType::Prim { .. } | SigType::Apply { .. })
}

fn cast_role_path(state: &LowerState) -> Path {
    canonical_role_path(
        state,
        &Path {
            segments: vec![Name("Cast".to_string())],
        },
    )
}

pub(super) fn collect_cast_sig_vars(sig: &SigType, out: &mut Vec<String>) {
    let mut set = HashSet::new();
    collect_all_sig_vars(sig, &mut set);
    for name in set {
        if !out.contains(&name) {
            out.push(name);
        }
    }
}

fn lower_cast_method_body(
    state: &mut LowerState,
    method_def: crate::ids::DefId,
    method_tv: TypeVar,
    pattern: &SyntaxNode,
    body_node: &SyntaxNode,
    source_sig: &SigType,
    target_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let arg = make_arg_pat_info(state, HeaderArg::Pattern(pattern.clone()));
    state.register_def_owner(arg.def, method_def);
    for (_, def) in &arg.local_bindings {
        state.register_def_owner(*def, method_def);
    }
    constrain_cast_arg_source(state, arg.tv, source_sig, impl_scope);

    state.ctx.push_local();
    for (name, def) in &arg.local_bindings {
        state.ctx.bind_local(name.clone(), *def);
    }
    let body = state.with_owner(method_def, |state| lower_binding_body(state, body_node));
    state.ctx.pop_local();
    constrain_cast_result_target(state, body.tv, target_sig, impl_scope);

    let principal_body = wrap_header_lambdas(state, body.clone(), vec![arg]);
    state.insert_principal_body(method_def, principal_body.clone());
    state
        .infer
        .constrain(Pos::Var(principal_body.tv), Neg::Var(method_tv));
    state
        .infer
        .constrain(Pos::Var(method_tv), Neg::Var(principal_body.tv));
    state.runtime_export_schemes.insert(
        method_def,
        runtime_export_scheme(state, source_sig, target_sig),
    );
}

pub(super) fn constrain_cast_arg_source(
    state: &mut LowerState,
    arg_tv: TypeVar,
    source_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let mut pos_vars = impl_scope.clone();
    let mut neg_vars = impl_scope.clone();
    let source_pos = lower_pure_sig_pos_id(state, source_sig, &mut pos_vars);
    let source_neg = lower_pure_sig_neg_id(state, source_sig, &mut neg_vars);
    state.infer.constrain(source_pos, Neg::Var(arg_tv));
    state.infer.constrain(Pos::Var(arg_tv), source_neg);
}

pub(super) fn constrain_cast_result_target(
    state: &mut LowerState,
    body_tv: TypeVar,
    target_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let mut pos_vars = impl_scope.clone();
    let mut neg_vars = impl_scope.clone();
    let target_pos = lower_pure_sig_pos_id(state, target_sig, &mut pos_vars);
    let target_neg = lower_pure_sig_neg_id(state, target_sig, &mut neg_vars);
    state.infer.constrain(Pos::Var(body_tv), target_neg);
    state.infer.constrain(target_pos, Neg::Var(body_tv));
}

pub(super) fn render_cast_impl_args(
    state: &mut LowerState,
    role_infos: &[RoleArgInfo],
    input_args: &[SigType],
    assoc_eqs: &HashMap<String, SigType>,
    impl_scope: &HashMap<String, TypeVar>,
) -> (Vec<String>, Vec<crate::simplify::compact::CompactType>) {
    if role_infos.is_empty() {
        let rendered = input_args
            .iter()
            .map(|sig| render_impl_arg_pattern(state, sig, impl_scope))
            .collect();
        let compact = input_args
            .iter()
            .map(|sig| compact_impl_arg_pattern(state, sig, impl_scope))
            .collect();
        return (rendered, compact);
    }

    let mut rendered = Vec::with_capacity(role_infos.len());
    let mut compact = Vec::with_capacity(role_infos.len());
    let mut input_iter = input_args.iter();
    for info in role_infos {
        let sig = if info.is_input {
            input_iter.next()
        } else {
            assoc_eqs.get(&info.name)
        };
        let Some(sig) = sig else {
            continue;
        };
        let rendered_sig = render_impl_arg_pattern(state, sig, impl_scope);
        let compact_sig = compact_impl_arg_pattern(state, sig, impl_scope);
        if info.is_input {
            rendered.push(rendered_sig);
        } else {
            rendered.push(format!("{} = {}", info.name, rendered_sig));
        }
        compact.push(compact_sig);
    }
    (rendered, compact)
}
