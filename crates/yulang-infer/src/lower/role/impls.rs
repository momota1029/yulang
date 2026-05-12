use super::*;

use crate::types::{EffectAtom, Neg, Pos};

#[derive(Debug, Clone)]
pub struct ErrorThrowVariant {
    pub(crate) payload_sig: Option<SigType>,
    pub(crate) constructor_def: crate::ids::DefId,
    pub(crate) operation_def: crate::ids::DefId,
}

#[derive(Debug, Clone)]
pub(crate) struct ErrorUpSource {
    pub(crate) source_sig: SigType,
    pub(crate) target_operation_def: crate::ids::DefId,
}

pub(crate) fn lower_impl_decl(state: &mut LowerState, node: &SyntaxNode) {
    lower_impl_decl_with_receiver(state, node, None, &[]);
}

pub(crate) fn lower_attached_impl_decl(
    state: &mut LowerState,
    node: &SyntaxNode,
    receiver_path: &Path,
    receiver_type_param_names: &[String],
) {
    lower_impl_decl_with_receiver(
        state,
        node,
        Some(attached_impl_receiver_sig(
            receiver_path,
            receiver_type_param_names,
            node.text_range(),
        )),
        receiver_type_param_names,
    );
}

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
    });
}

pub(crate) fn lower_synthetic_error_throw(
    state: &mut LowerState,
    error_sig: &SigType,
    variants: Vec<ErrorThrowVariant>,
) {
    if variants.is_empty() {
        return;
    }

    let impl_def = state.fresh_def();
    let role = throw_role_path(state);
    let role_infos = state.infer.role_arg_infos_of(&role);
    let mut impl_scope_names = Vec::new();
    collect_cast_sig_vars(error_sig, &mut impl_scope_names);
    for info in &role_infos {
        if !impl_scope_names.contains(&info.name) {
            impl_scope_names.push(info.name.clone());
        }
    }
    let impl_scope = fresh_type_scope(state, &impl_scope_names);
    let throw_name = Name("throw".to_string());
    let method_def = state.fresh_def();
    let method_tv = state.fresh_tv();
    state.register_def_tv(method_def, method_tv);
    state.mark_let_bound_def(method_def);
    state.register_def_owner(method_def, impl_def);
    state.register_def_name(method_def, throw_name.clone());

    let helper_module = state.ctx.modules.new_module();
    state.insert_module(
        state.ctx.current_module,
        Name(format!("&throw#{}", impl_def.0)),
        helper_module,
    );
    state.insert_value(helper_module, throw_name.clone(), method_def);

    state.with_type_scope(impl_scope.clone(), |state| {
        state.with_owner(impl_def, |state| {
            lower_synthetic_error_throw_body(
                state,
                method_def,
                method_tv,
                error_sig,
                &variants,
                &impl_scope,
            );
        });
    });

    let prerequisites = compact_role_constraints(&state.infer, impl_def);
    let throws_sig = SigType::Row {
        row: SigRow {
            items: vec![error_sig.clone()],
            tail: None,
        },
        span: error_sig.span(),
    };
    let assoc_eqs = HashMap::from([("throws".to_string(), throws_sig)]);
    let (args, compact_args) = render_cast_impl_args(
        state,
        &role_infos,
        std::slice::from_ref(error_sig),
        &assoc_eqs,
        &impl_scope,
    );
    state.infer.register_role_impl_candidate(RoleImplCandidate {
        role,
        args,
        compact_args,
        prerequisites,
        member_defs: HashMap::from([(throw_name, method_def)]),
    });
}

pub(crate) fn lower_synthetic_error_wrap(
    state: &mut LowerState,
    error_sig: &SigType,
    variants: &[ErrorThrowVariant],
    visibility: crate::symbols::Visibility,
) {
    if variants.is_empty() {
        return;
    }
    let Some(result_ok_def) = resolve_std_result_constructor(state, "ok") else {
        return;
    };
    let Some(result_err_def) = resolve_std_result_constructor(state, "err") else {
        return;
    };

    let wrap_name = Name("wrap".to_string());
    let wrap_def = state.fresh_def();
    let wrap_tv = state.fresh_tv();
    state.register_def_tv(wrap_def, wrap_tv);
    state.mark_let_bound_def(wrap_def);
    state.register_def_name(wrap_def, wrap_name.clone());
    state.insert_value_with_visibility(state.ctx.current_module, wrap_name, wrap_def, visibility);

    let mut scope_names = Vec::new();
    collect_cast_sig_vars(error_sig, &mut scope_names);
    let impl_scope = fresh_type_scope(state, &scope_names);
    state.with_owner(wrap_def, |state| {
        lower_synthetic_error_wrap_body(
            state,
            wrap_def,
            wrap_tv,
            error_sig,
            variants,
            result_ok_def,
            result_err_def,
            &impl_scope,
        );
    });
}

pub(crate) fn lower_synthetic_error_up(
    state: &mut LowerState,
    error_sig: &SigType,
    sources: &[ErrorUpSource],
    visibility: crate::symbols::Visibility,
) {
    if sources.is_empty() {
        return;
    }

    let up_name = Name("up".to_string());
    let up_def = state.fresh_def();
    let up_tv = state.fresh_tv();
    state.register_def_tv(up_def, up_tv);
    state.mark_let_bound_def(up_def);
    state.register_def_name(up_def, up_name.clone());
    state.insert_value_with_visibility(state.ctx.current_module, up_name, up_def, visibility);

    let mut scope_names = Vec::new();
    collect_cast_sig_vars(error_sig, &mut scope_names);
    for source in sources {
        collect_cast_sig_vars(&source.source_sig, &mut scope_names);
    }
    let impl_scope = fresh_type_scope(state, &scope_names);
    state.with_owner(up_def, |state| {
        lower_synthetic_error_up_body(state, up_def, up_tv, error_sig, sources, &impl_scope);
    });
}

fn lower_impl_decl_with_receiver(
    state: &mut LowerState,
    node: &SyntaxNode,
    attached_receiver: Option<SigType>,
    attached_receiver_type_param_names: &[String],
) {
    let impl_def = state.fresh_def();
    let Some(head) = child_node(node, SyntaxKind::TypeExpr) else {
        return;
    };
    let Some(mut sig) = parse_sig_type_expr(&head) else {
        return;
    };
    if let Some(receiver) = attached_receiver {
        sig = attach_impl_receiver_sig(sig, receiver);
    }
    let Some((role, args)) = sig_type_head(&sig) else {
        return;
    };
    let role = canonical_role_path(state, &role);
    let assoc_eqs = collect_impl_assoc_type_equations(node);
    let role_infos = state.infer.role_arg_infos_of(&role);
    let mut impl_scope_names = binding_sig_var_names(node);
    for name in attached_receiver_type_param_names {
        if !impl_scope_names.contains(name) {
            impl_scope_names.push(name.clone());
        }
    }
    for info in &role_infos {
        if !impl_scope_names.contains(&info.name) {
            impl_scope_names.push(info.name.clone());
        }
    }
    let impl_scope = fresh_type_scope(state, &impl_scope_names);
    let role_sig_bindings = collect_impl_role_sig_bindings(&role_infos, &args, &assoc_eqs);
    let member_defs = if let Some(body) = child_node(node, SyntaxKind::IndentBlock)
        .or_else(|| child_node(node, SyntaxKind::BraceGroup))
    {
        state.with_type_scope(impl_scope.clone(), |state| {
            state.with_owner(impl_def, |state| {
                let mut items = Vec::new();
                collect_block_items(&body, &mut items);
                let member_defs = lower_impl_body(
                    state,
                    &items,
                    impl_def,
                    &role,
                    &role_infos,
                    &impl_scope,
                    &role_sig_bindings,
                );
                for item in items {
                    if item.kind() == SyntaxKind::WhereClause {
                        lower_where_clause(state, &item);
                    }
                }
                member_defs
            })
        })
    } else {
        HashMap::new()
    };
    let prerequisites = compact_role_constraints(&state.infer, impl_def);
    let (args, compact_args) = if role_infos.is_empty() {
        let rendered = args
            .iter()
            .map(|sig| render_impl_arg_pattern(state, sig, &impl_scope))
            .collect::<Vec<_>>();
        let compact = args
            .iter()
            .map(|sig| compact_impl_arg_pattern(state, sig, &impl_scope))
            .collect::<Vec<_>>();
        (rendered, compact)
    } else {
        let mut rendered = Vec::with_capacity(role_infos.len());
        let mut compact = Vec::with_capacity(role_infos.len());
        let mut input_iter = args.iter();
        for info in &role_infos {
            if info.is_input {
                let Some(sig) = input_iter.next() else {
                    return;
                };
                let rendered_sig = render_impl_arg_pattern(state, sig, &impl_scope);
                let compact_sig = compact_impl_arg_pattern(state, sig, &impl_scope);
                rendered.push(rendered_sig);
                compact.push(compact_sig);
            } else {
                let Some(sig) = assoc_eqs.get(&info.name) else {
                    return;
                };
                let rendered_sig = render_impl_arg_pattern(state, sig, &impl_scope);
                let compact_sig = compact_impl_arg_pattern(state, sig, &impl_scope);
                rendered.push(format!("{} = {}", info.name, rendered_sig));
                compact.push(compact_sig);
            }
        }
        (rendered, compact)
    };
    state.infer.register_role_impl_candidate(RoleImplCandidate {
        role,
        args,
        compact_args,
        prerequisites,
        member_defs,
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

fn lower_synthetic_error_throw_body(
    state: &mut LowerState,
    method_def: crate::ids::DefId,
    method_tv: TypeVar,
    error_sig: &SigType,
    variants: &[ErrorThrowVariant],
    impl_scope: &HashMap<String, TypeVar>,
) {
    let arg_def = state.fresh_def();
    let arg_tv = state.fresh_tv();
    let arg_name = Name("error".to_string());
    state.register_def_tv(arg_def, arg_tv);
    state.register_def_name(arg_def, arg_name.clone());
    state.register_def_owner(arg_def, method_def);
    constrain_cast_arg_source(state, arg_tv, error_sig, impl_scope);

    let match_tv = state.fresh_tv();
    let match_eff = state.fresh_tv();
    constrain_exact_error_effect(state, match_eff, error_sig, impl_scope);
    let scrutinee = TypedExpr {
        tv: arg_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::Var(arg_def),
    };
    let arms = variants
        .iter()
        .map(|variant| {
            synthetic_error_throw_arm(state, variant, arg_tv, match_tv, match_eff, method_def)
        })
        .collect::<Vec<_>>();
    let body = TypedExpr {
        tv: match_tv,
        eff: match_eff,
        kind: ExprKind::Match(Box::new(scrutinee), arms),
    };
    constrain_cast_result_target(state, body.tv, &never_sig(error_sig.span()), impl_scope);

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
                kind: PatKind::UnresolvedName(arg_name.clone()),
            }),
            local_bindings: vec![(arg_name, arg_def)],
            ann: None,
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
    let constrained_sig = state.infer.alloc_pos(Pos::Fun {
        arg: state.infer.alloc_neg(Neg::Var(arg_tv)),
        arg_eff: state.infer.arena.empty_neg_row,
        ret_eff: state.infer.alloc_pos(Pos::Var(body.eff)),
        ret: state.infer.alloc_pos(Pos::Var(body.tv)),
    });
    state.infer.constrain(constrained_sig, Neg::Var(method_tv));
    state.infer.constrain(
        Pos::Var(method_tv),
        state.infer.alloc_neg(Neg::Fun {
            arg: state.infer.alloc_pos(Pos::Var(arg_tv)),
            arg_eff: state.infer.arena.empty_pos_row,
            ret_eff: state.infer.alloc_neg(Neg::Var(body.eff)),
            ret: state.infer.alloc_neg(Neg::Var(body.tv)),
        }),
    );
    store_synthetic_error_throw_scheme(state, method_def, error_sig, impl_scope);
    state.runtime_export_schemes.insert(
        method_def,
        synthetic_error_throw_runtime_scheme(state, error_sig),
    );
}

fn lower_synthetic_error_wrap_body(
    state: &mut LowerState,
    wrap_def: crate::ids::DefId,
    wrap_tv: TypeVar,
    error_sig: &SigType,
    variants: &[ErrorThrowVariant],
    result_ok_def: crate::ids::DefId,
    result_err_def: crate::ids::DefId,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let action_def = state.fresh_def();
    let action_tv = state.fresh_tv();
    let action_eff = state.fresh_tv();
    let action_name = Name("action".to_string());
    state.register_def_tv(action_def, action_tv);
    state.register_def_eff_tv(action_def, action_eff);
    state.register_def_name(action_def, action_name.clone());
    state.register_def_owner(action_def, wrap_def);

    let result_tv = state.fresh_tv();
    let result_eff = state.fresh_tv();
    constrain_error_wrap_effect(state, action_eff, result_eff, error_sig, impl_scope);
    constrain_error_wrap_result(state, result_tv, error_sig, impl_scope);

    let comp = TypedExpr {
        tv: action_tv,
        eff: action_eff,
        kind: ExprKind::Var(action_def),
    };
    let mut arms = variants
        .iter()
        .filter_map(|variant| {
            synthetic_error_wrap_effect_arm(
                state,
                variant,
                result_tv,
                result_eff,
                result_err_def,
                wrap_def,
                impl_scope,
            )
        })
        .collect::<Vec<_>>();
    arms.push(synthetic_error_wrap_value_arm(
        state,
        action_tv,
        result_tv,
        result_eff,
        result_ok_def,
        wrap_def,
    ));
    let body = TypedExpr {
        tv: result_tv,
        eff: result_eff,
        kind: ExprKind::Catch(Box::new(comp), arms),
    };

    let principal_body = wrap_header_lambdas(
        state,
        body.clone(),
        vec![ArgPatInfo {
            def: action_def,
            tv: action_tv,
            arg_eff_tv: action_eff,
            read_eff_tv: Some(action_eff),
            pat: Some(TypedPat {
                tv: action_tv,
                kind: PatKind::UnresolvedName(action_name.clone()),
            }),
            local_bindings: vec![(action_name, action_def)],
            ann: None,
            unit_arg: false,
        }],
    );
    state.insert_principal_body(wrap_def, principal_body.clone());
    state
        .infer
        .constrain(Pos::Var(principal_body.tv), Neg::Var(wrap_tv));
    state
        .infer
        .constrain(Pos::Var(wrap_tv), Neg::Var(principal_body.tv));
}

fn lower_synthetic_error_up_body(
    state: &mut LowerState,
    up_def: crate::ids::DefId,
    up_tv: TypeVar,
    error_sig: &SigType,
    sources: &[ErrorUpSource],
    impl_scope: &HashMap<String, TypeVar>,
) {
    let action_def = state.fresh_def();
    let action_tv = state.fresh_tv();
    let action_eff = state.fresh_tv();
    let action_name = Name("action".to_string());
    state.register_def_tv(action_def, action_tv);
    state.register_def_eff_tv(action_def, action_eff);
    state.register_def_name(action_def, action_name.clone());
    state.register_def_owner(action_def, up_def);

    let result_tv = state.fresh_tv();
    let result_eff = state.fresh_tv();
    constrain_error_up_effect(
        state, action_eff, result_eff, error_sig, sources, impl_scope,
    );

    let comp = TypedExpr {
        tv: action_tv,
        eff: action_eff,
        kind: ExprKind::Var(action_def),
    };
    let mut arms = sources
        .iter()
        .flat_map(|source| {
            synthetic_error_up_effect_arms(state, source, result_tv, result_eff, up_def)
        })
        .collect::<Vec<_>>();
    arms.push(synthetic_error_up_value_arm(
        state, action_tv, result_tv, result_eff, up_def,
    ));
    let body = TypedExpr {
        tv: result_tv,
        eff: result_eff,
        kind: ExprKind::Catch(Box::new(comp), arms),
    };

    let principal_body = wrap_header_lambdas(
        state,
        body.clone(),
        vec![ArgPatInfo {
            def: action_def,
            tv: action_tv,
            arg_eff_tv: action_eff,
            read_eff_tv: Some(action_eff),
            pat: Some(TypedPat {
                tv: action_tv,
                kind: PatKind::UnresolvedName(action_name.clone()),
            }),
            local_bindings: vec![(action_name, action_def)],
            ann: None,
            unit_arg: false,
        }],
    );
    state.insert_principal_body(up_def, principal_body.clone());
    state
        .infer
        .constrain(Pos::Var(principal_body.tv), Neg::Var(up_tv));
    state
        .infer
        .constrain(Pos::Var(up_tv), Neg::Var(principal_body.tv));
}

fn synthetic_error_wrap_value_arm(
    state: &mut LowerState,
    action_tv: TypeVar,
    result_tv: TypeVar,
    result_eff: TypeVar,
    result_ok_def: crate::ids::DefId,
    wrap_def: crate::ids::DefId,
) -> TypedCatchArm {
    let value_def = state.fresh_def();
    let value_tv = state.fresh_tv();
    let value_name = Name("value".to_string());
    state.register_def_tv(value_def, value_tv);
    state.register_def_name(value_def, value_name);
    state.register_def_owner(value_def, wrap_def);
    let pat = TypedPat {
        tv: value_tv,
        kind: PatKind::As(
            Box::new(TypedPat {
                tv: value_tv,
                kind: PatKind::Wild,
            }),
            value_def,
        ),
    };
    state.infer.constrain(Pos::Var(action_tv), Neg::Var(pat.tv));
    state.infer.constrain(Pos::Var(pat.tv), Neg::Var(action_tv));

    let ok = crate::lower::expr::resolve_bound_def_expr(state, result_ok_def);
    let value = TypedExpr {
        tv: value_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::Var(value_def),
    };
    let body = crate::lower::expr::make_app(state, ok, value);
    let body = state
        .implicit_cast_boundary_with_effects(
            body,
            result_tv,
            result_eff,
            ExpectedEdgeKind::CatchBranch,
            ConstraintCause {
                span: None,
                reason: ConstraintReason::CatchBranch,
            },
            true,
        )
        .0;
    crate::lower::stmt::connect_pat_shape_and_locals(state, &pat, body.eff);

    TypedCatchArm {
        tv: state.fresh_tv(),
        guard: None,
        kind: CatchArmKind::Value(pat, body),
    }
}

fn synthetic_error_up_value_arm(
    state: &mut LowerState,
    action_tv: TypeVar,
    result_tv: TypeVar,
    result_eff: TypeVar,
    up_def: crate::ids::DefId,
) -> TypedCatchArm {
    let value_def = state.fresh_def();
    let value_tv = state.fresh_tv();
    state.register_def_tv(value_def, value_tv);
    state.register_def_owner(value_def, up_def);
    let pat = TypedPat {
        tv: value_tv,
        kind: PatKind::As(
            Box::new(TypedPat {
                tv: value_tv,
                kind: PatKind::Wild,
            }),
            value_def,
        ),
    };
    state.infer.constrain(Pos::Var(action_tv), Neg::Var(pat.tv));
    state.infer.constrain(Pos::Var(pat.tv), Neg::Var(action_tv));

    let body = TypedExpr {
        tv: value_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::Var(value_def),
    };
    let body = state
        .implicit_cast_boundary_with_effects(
            body,
            result_tv,
            result_eff,
            ExpectedEdgeKind::CatchBranch,
            ConstraintCause {
                span: None,
                reason: ConstraintReason::CatchBranch,
            },
            true,
        )
        .0;
    crate::lower::stmt::connect_pat_shape_and_locals(state, &pat, body.eff);

    TypedCatchArm {
        tv: state.fresh_tv(),
        guard: None,
        kind: CatchArmKind::Value(pat, body),
    }
}

fn synthetic_error_up_effect_arms(
    state: &mut LowerState,
    source: &ErrorUpSource,
    result_tv: TypeVar,
    result_eff: TypeVar,
    up_def: crate::ids::DefId,
) -> Vec<TypedCatchArm> {
    let Some(source_path) = nominal_sig_effect_path(state, &source.source_sig) else {
        return Vec::new();
    };
    let variants = state
        .error_throw_variants
        .get(&source_path)
        .cloned()
        .unwrap_or_default();
    variants
        .iter()
        .filter_map(|variant| {
            synthetic_error_up_effect_arm(
                state,
                variant,
                source.target_operation_def,
                result_tv,
                result_eff,
                up_def,
            )
        })
        .collect()
}

fn synthetic_error_up_effect_arm(
    state: &mut LowerState,
    source_variant: &ErrorThrowVariant,
    target_operation_def: crate::ids::DefId,
    result_tv: TypeVar,
    result_eff: TypeVar,
    up_def: crate::ids::DefId,
) -> Option<TypedCatchArm> {
    let op_path = effect_operation_surface_path(state, source_variant.operation_def)?;
    let (pat, source_error_value) = if source_variant.payload_sig.is_some() {
        let payload_def = state.fresh_def();
        let payload_tv = state.fresh_tv();
        state.register_def_tv(payload_def, payload_tv);
        state.register_def_owner(payload_def, up_def);
        let pat = TypedPat {
            tv: payload_tv,
            kind: PatKind::As(
                Box::new(TypedPat {
                    tv: payload_tv,
                    kind: PatKind::Wild,
                }),
                payload_def,
            ),
        };
        let payload = TypedExpr {
            tv: payload_tv,
            eff: state.fresh_exact_pure_eff_tv(),
            kind: ExprKind::Var(payload_def),
        };
        let constructor =
            crate::lower::expr::resolve_bound_def_expr(state, source_variant.constructor_def);
        (
            pat,
            crate::lower::expr::make_app(state, constructor, payload),
        )
    } else {
        (
            TypedPat {
                tv: state.fresh_tv(),
                kind: PatKind::Lit(crate::ast::expr::Lit::Unit),
            },
            crate::lower::expr::resolve_bound_def_expr(state, source_variant.constructor_def),
        )
    };

    let target_op = crate::lower::expr::resolve_bound_def_expr(state, target_operation_def);
    let body = crate::lower::expr::make_app(state, target_op, source_error_value);
    let body = state
        .implicit_cast_boundary_with_effects(
            body,
            result_tv,
            result_eff,
            ExpectedEdgeKind::CatchBranch,
            ConstraintCause {
                span: None,
                reason: ConstraintReason::CatchBranch,
            },
            true,
        )
        .0;
    crate::lower::stmt::connect_pat_shape_and_locals(state, &pat, body.eff);

    let k = state.fresh_def();
    let k_tv = state.fresh_tv();
    state.register_def_tv(k, k_tv);
    state.mark_continuation_def(k);
    state.register_def_owner(k, up_def);

    Some(TypedCatchArm {
        tv: state.fresh_tv(),
        guard: None,
        kind: CatchArmKind::Effect {
            op_path,
            pat,
            k,
            body,
        },
    })
}

fn synthetic_error_wrap_effect_arm(
    state: &mut LowerState,
    variant: &ErrorThrowVariant,
    result_tv: TypeVar,
    result_eff: TypeVar,
    result_err_def: crate::ids::DefId,
    wrap_def: crate::ids::DefId,
    impl_scope: &HashMap<String, TypeVar>,
) -> Option<TypedCatchArm> {
    let op_path = effect_operation_surface_path(state, variant.operation_def)?;
    let (pat, error_value) = if let Some(payload_sig) = &variant.payload_sig {
        let payload_def = state.fresh_def();
        let payload_tv = state.fresh_tv();
        state.register_def_tv(payload_def, payload_tv);
        state.register_def_name(payload_def, Name("payload".to_string()));
        state.register_def_owner(payload_def, wrap_def);
        constrain_cast_arg_source(state, payload_tv, payload_sig, impl_scope);
        let pat = TypedPat {
            tv: payload_tv,
            kind: PatKind::As(
                Box::new(TypedPat {
                    tv: payload_tv,
                    kind: PatKind::Wild,
                }),
                payload_def,
            ),
        };
        let payload = TypedExpr {
            tv: payload_tv,
            eff: state.fresh_exact_pure_eff_tv(),
            kind: ExprKind::Var(payload_def),
        };
        let constructor =
            crate::lower::expr::resolve_bound_def_expr(state, variant.constructor_def);
        (
            pat,
            crate::lower::expr::make_app(state, constructor, payload),
        )
    } else {
        (
            TypedPat {
                tv: state.fresh_tv(),
                kind: PatKind::Lit(crate::ast::expr::Lit::Unit),
            },
            crate::lower::expr::resolve_bound_def_expr(state, variant.constructor_def),
        )
    };

    let err = crate::lower::expr::resolve_bound_def_expr(state, result_err_def);
    let body = crate::lower::expr::make_app(state, err, error_value);
    let body = state
        .implicit_cast_boundary_with_effects(
            body,
            result_tv,
            result_eff,
            ExpectedEdgeKind::CatchBranch,
            ConstraintCause {
                span: None,
                reason: ConstraintReason::CatchBranch,
            },
            true,
        )
        .0;
    crate::lower::stmt::connect_pat_shape_and_locals(state, &pat, body.eff);

    let k = state.fresh_def();
    let k_tv = state.fresh_tv();
    state.register_def_tv(k, k_tv);
    state.mark_continuation_def(k);
    state.register_def_owner(k, wrap_def);

    Some(TypedCatchArm {
        tv: state.fresh_tv(),
        guard: None,
        kind: CatchArmKind::Effect {
            op_path,
            pat,
            k,
            body,
        },
    })
}

fn constrain_error_wrap_effect(
    state: &mut LowerState,
    action_eff: TypeVar,
    result_eff: TypeVar,
    error_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let Some(atom) = effect_atom_from_sig(state, error_sig, impl_scope) else {
        return;
    };
    state.infer.constrain(
        state.pos_row(vec![Pos::Atom(atom.clone())], Pos::Bot),
        Neg::Var(action_eff),
    );
    state.infer.constrain(
        Pos::Var(action_eff),
        state.neg_row(vec![Neg::Atom(atom)], Neg::Top),
    );
    state
        .infer
        .constrain(state.pos_row(vec![], Pos::Bot), Neg::Var(result_eff));
    state
        .infer
        .constrain(Pos::Var(result_eff), state.neg_row(vec![], Neg::Top));
}

fn constrain_error_up_effect(
    state: &mut LowerState,
    action_eff: TypeVar,
    result_eff: TypeVar,
    error_sig: &SigType,
    sources: &[ErrorUpSource],
    impl_scope: &HashMap<String, TypeVar>,
) {
    let source_atoms = sources
        .iter()
        .filter_map(|source| effect_atom_from_sig(state, &source.source_sig, impl_scope))
        .collect::<Vec<_>>();
    if !source_atoms.is_empty() {
        state.infer.constrain(
            state.pos_row(
                source_atoms.iter().cloned().map(Pos::Atom).collect(),
                Pos::Bot,
            ),
            Neg::Var(action_eff),
        );
        state.infer.constrain(
            Pos::Var(action_eff),
            state.neg_row(source_atoms.into_iter().map(Neg::Atom).collect(), Neg::Top),
        );
    }

    let Some(target_atom) = effect_atom_from_sig(state, error_sig, impl_scope) else {
        return;
    };
    state.infer.constrain(
        state.pos_row(vec![Pos::Atom(target_atom.clone())], Pos::Bot),
        Neg::Var(result_eff),
    );
    state.infer.constrain(
        Pos::Var(result_eff),
        state.neg_row(vec![Neg::Atom(target_atom)], Neg::Top),
    );
}

fn constrain_error_wrap_result(
    state: &mut LowerState,
    result_tv: TypeVar,
    error_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let mut result_scope = impl_scope.clone();
    let ok_var = "__wrap_ok".to_string();
    result_scope
        .entry(ok_var.clone())
        .or_insert_with(|| state.fresh_tv());
    let target = SigType::Apply {
        path: Path {
            segments: vec![
                Name("std".to_string()),
                Name("result".to_string()),
                Name("result".to_string()),
            ],
        },
        args: vec![
            SigType::Var(SigVar {
                name: ok_var,
                span: error_sig.span(),
            }),
            error_sig.clone(),
        ],
        span: error_sig.span(),
    };
    let mut pos_scope = result_scope.clone();
    let mut neg_scope = result_scope;
    let target_pos = lower_pure_sig_pos_id(state, &target, &mut pos_scope);
    let target_neg = lower_pure_sig_neg_id(state, &target, &mut neg_scope);
    state.infer.constrain(target_pos, Neg::Var(result_tv));
    state.infer.constrain(Pos::Var(result_tv), target_neg);
}

fn synthetic_error_throw_arm(
    state: &mut LowerState,
    variant: &ErrorThrowVariant,
    scrutinee_tv: TypeVar,
    match_tv: TypeVar,
    match_eff: TypeVar,
    method_def: crate::ids::DefId,
) -> TypedMatchArm {
    let pat_tv = state.fresh_tv();
    let ctor_ref =
        crate::lower::stmt::resolve_pattern_constructor_ref(state, variant.constructor_def);
    let (pat, body) = if variant.payload_sig.is_some() {
        let payload_def = state.fresh_def();
        let payload_tv = state.fresh_tv();
        let payload_name = Name("value".to_string());
        state.register_def_tv(payload_def, payload_tv);
        state.register_def_name(payload_def, payload_name);
        state.register_def_owner(payload_def, method_def);
        let payload_pat = TypedPat {
            tv: payload_tv,
            kind: PatKind::As(
                Box::new(TypedPat {
                    tv: payload_tv,
                    kind: PatKind::Wild,
                }),
                payload_def,
            ),
        };
        let pat = TypedPat {
            tv: pat_tv,
            kind: PatKind::Con(ctor_ref, Some(Box::new(payload_pat))),
        };
        let op = crate::lower::expr::resolve_bound_def_expr(state, variant.operation_def);
        let payload = TypedExpr {
            tv: payload_tv,
            eff: state.fresh_exact_pure_eff_tv(),
            kind: ExprKind::Var(payload_def),
        };
        (pat, crate::lower::expr::make_app(state, op, payload))
    } else {
        (
            TypedPat {
                tv: pat_tv,
                kind: PatKind::Con(ctor_ref, None),
            },
            crate::lower::expr::resolve_bound_def_expr(state, variant.operation_def),
        )
    };

    crate::lower::stmt::connect_pat_shape_and_locals(state, &pat, match_eff);
    state
        .infer
        .constrain(Pos::Var(scrutinee_tv), Neg::Var(pat.tv));
    state
        .infer
        .constrain(Pos::Var(pat.tv), Neg::Var(scrutinee_tv));
    let body = state
        .implicit_cast_boundary_with_effects(
            body,
            match_tv,
            match_eff,
            ExpectedEdgeKind::MatchBranch,
            ConstraintCause::unknown(),
            true,
        )
        .0;

    TypedMatchArm {
        pat,
        guard: None,
        body,
    }
}

fn constrain_exact_error_effect(
    state: &mut LowerState,
    eff_tv: TypeVar,
    error_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let Some(atom) = effect_atom_from_sig(state, error_sig, impl_scope) else {
        return;
    };
    state.infer.constrain(
        state.pos_row(vec![Pos::Atom(atom.clone())], Pos::Bot),
        Neg::Var(eff_tv),
    );
    state.infer.constrain(
        Pos::Var(eff_tv),
        state.neg_row(vec![Neg::Atom(atom)], Neg::Top),
    );
}

fn store_synthetic_error_throw_scheme(
    state: &mut LowerState,
    method_def: crate::ids::DefId,
    error_sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) {
    let Some(atom) = effect_atom_from_sig(state, error_sig, impl_scope) else {
        return;
    };
    let mut pos_scope = impl_scope.clone();
    let mut neg_scope = impl_scope.clone();
    let arg = lower_pure_sig_neg_id(state, error_sig, &mut neg_scope);
    let ret = lower_pure_sig_pos_id(state, &never_sig(error_sig.span()), &mut pos_scope);
    let scheme_pos = state.infer.alloc_pos(Pos::Fun {
        arg,
        arg_eff: state.infer.arena.empty_neg_row,
        ret_eff: state
            .infer
            .alloc_pos(state.pos_row(vec![Pos::Atom(atom)], Pos::Bot)),
        ret,
    });
    state.infer.store_frozen_scheme(
        method_def,
        crate::scheme::freeze_pos_scheme(&state.infer, scheme_pos),
    );
}

fn synthetic_error_throw_runtime_scheme(
    state: &LowerState,
    error_sig: &SigType,
) -> typed_ir::Scheme {
    typed_ir::Scheme {
        requirements: Vec::new(),
        body: typed_ir::Type::Fun {
            param: Box::new(export_runtime_sig_type(state, error_sig)),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(core_error_effect_type(state, error_sig)),
            ret: Box::new(export_runtime_sig_type(state, &never_sig(error_sig.span()))),
        },
    }
}

fn core_error_effect_type(state: &LowerState, error_sig: &SigType) -> typed_ir::Type {
    typed_ir::Type::Row {
        items: vec![export_runtime_sig_type(state, error_sig)],
        tail: Box::new(typed_ir::Type::Never),
    }
}

fn effect_atom_from_sig(
    state: &mut LowerState,
    sig: &SigType,
    impl_scope: &HashMap<String, TypeVar>,
) -> Option<EffectAtom> {
    match sig {
        SigType::Prim { path, .. } => Some(EffectAtom {
            path: path.clone(),
            args: Vec::new(),
        }),
        SigType::Apply { path, args, .. } => {
            let mut scope = impl_scope.clone();
            Some(EffectAtom {
                path: path.clone(),
                args: args
                    .iter()
                    .map(|arg| {
                        crate::lower::signature::lower_sig_effect_arg(state, arg, &mut scope)
                    })
                    .collect(),
            })
        }
        _ => None,
    }
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

fn throw_role_path(state: &LowerState) -> Path {
    canonical_role_path(
        state,
        &Path {
            segments: vec![Name("Throw".to_string())],
        },
    )
}

fn resolve_std_result_constructor(state: &LowerState, name: &str) -> Option<crate::ids::DefId> {
    let std_path = Path {
        segments: vec![
            Name("std".to_string()),
            Name("result".to_string()),
            Name("result".to_string()),
            Name(name.to_string()),
        ],
    };
    state.ctx.resolve_path_value(&std_path).or_else(|| {
        state.ctx.resolve_path_value(&Path {
            segments: vec![Name("result".to_string()), Name(name.to_string())],
        })
    })
}

fn effect_operation_surface_path(
    state: &LowerState,
    operation_def: crate::ids::DefId,
) -> Option<Path> {
    let mut path = state
        .ctx
        .canonical_value_paths()
        .get(&operation_def)
        .cloned()?;
    let last = path.segments.last_mut()?;
    if let Some(surface) = last.0.strip_suffix("#effect") {
        *last = Name(surface.to_string());
    }
    Some(path)
}

fn nominal_sig_effect_path(state: &LowerState, sig: &SigType) -> Option<Path> {
    match sig {
        SigType::Prim { path, .. } | SigType::Apply { path, .. } => {
            Some(state.ctx.canonical_current_type_path(path))
        }
        _ => None,
    }
}

fn never_sig(span: rowan::TextRange) -> SigType {
    SigType::Prim {
        path: Path {
            segments: vec![Name("never".to_string())],
        },
        span,
    }
}

fn collect_cast_sig_vars(sig: &SigType, out: &mut Vec<String>) {
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

fn constrain_cast_arg_source(
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

fn constrain_cast_result_target(
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

fn render_cast_impl_args(
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

fn attached_impl_receiver_sig(
    path: &Path,
    type_param_names: &[String],
    span: rowan::TextRange,
) -> SigType {
    let args = type_param_names
        .iter()
        .map(|name| {
            SigType::Var(SigVar {
                name: name.clone(),
                span,
            })
        })
        .collect::<Vec<_>>();
    if args.is_empty() {
        SigType::Prim {
            path: path.clone(),
            span,
        }
    } else {
        SigType::Apply {
            path: path.clone(),
            args,
            span,
        }
    }
}

fn attach_impl_receiver_sig(sig: SigType, receiver: SigType) -> SigType {
    match sig {
        SigType::Prim { path, span } => SigType::Apply {
            path,
            args: vec![receiver],
            span,
        },
        SigType::Apply {
            path,
            mut args,
            span,
        } => {
            args.insert(0, receiver);
            SigType::Apply { path, args, span }
        }
        other => other,
    }
}

fn lower_impl_body(
    state: &mut LowerState,
    items: &[SyntaxNode],
    impl_def: crate::ids::DefId,
    role: &Path,
    role_infos: &[RoleArgInfo],
    impl_scope: &HashMap<String, TypeVar>,
    role_sig_bindings: &HashMap<String, SigType>,
) -> HashMap<Name, crate::ids::DefId> {
    let required_methods = state
        .infer
        .role_method_infos_of(role)
        .into_iter()
        .filter(|info| info.sig.is_some() && !info.has_default_body)
        .collect::<Vec<_>>();
    let mut required_by_name = HashMap::new();
    for info in required_methods {
        required_by_name.insert(info.name.clone(), info);
    }

    let helper_module = state.ctx.modules.new_module();
    state.insert_module(
        state.ctx.current_module,
        Name(format!("&impl#{}", impl_def.0)),
        helper_module,
    );
    let mut exported_member_defs = HashMap::new();

    state.ctx.push_local();
    let mut impl_members = Vec::new();
    for item in items {
        let Some(info) = impl_member_decl_info(item) else {
            continue;
        };
        match info.visibility {
            ImplMemberVisibility::My => {
                preregister_binding(state, item);
            }
            ImplMemberVisibility::Our => {
                let def = state.fresh_def();
                let tv = state.fresh_tv();
                state.register_def_tv(def, tv);
                state.mark_let_bound_def(def);
                state.register_def_owner(def, impl_def);
                state.ctx.bind_local(info.name.clone(), def);
                state.insert_value(helper_module, info.name.clone(), def);
                exported_member_defs.insert(info.name.clone(), def);
                impl_members.push((info, def));
            }
            ImplMemberVisibility::Other => {}
        }
    }

    for item in items {
        let Some(info) = impl_member_decl_info(item) else {
            continue;
        };
        if !matches!(info.visibility, ImplMemberVisibility::My)
            || item.kind() != SyntaxKind::Binding
        {
            continue;
        }
        let type_scope = impl_member_type_scope(state, item, impl_scope);
        let _ = lower_binding_with_type_scope(state, item, type_scope);
    }

    let implemented_names = impl_members
        .iter()
        .map(|(info, _)| info.name.clone())
        .collect::<HashSet<_>>();
    for (info, _) in &impl_members {
        if !required_by_name.contains_key(&info.name) {
            state.infer.report_synthetic_type_error(
                TypeErrorKind::UnknownImplMember {
                    role: path_string(role),
                    member: info.name.0.clone(),
                },
                format!("impl {}", path_string(role)),
            );
        }
    }
    for required in required_by_name.keys() {
        if !implemented_names.contains(required) {
            state.infer.report_synthetic_type_error(
                TypeErrorKind::MissingImplMember {
                    role: path_string(role),
                    member: required.0.clone(),
                },
                format!("impl {}", path_string(role)),
            );
        }
    }

    for (info, def) in impl_members {
        let Some(required) = required_by_name.get(&info.name) else {
            continue;
        };
        let type_scope = impl_member_type_scope(state, &info.node, impl_scope);
        if info.has_receiver {
            lower_impl_receiver_member(
                state,
                &info,
                required,
                def,
                &type_scope,
                role_infos,
                role_sig_bindings,
            );
            connect_impl_member_expected_type(
                state,
                def,
                required,
                &type_scope,
                role_infos,
                role_sig_bindings,
                Some(info.node.text_range()),
            );
        } else if info.node.kind() == SyntaxKind::Binding {
            let _ = lower_binding_with_type_scope(state, &info.node, type_scope.clone());
            connect_impl_member_expected_type(
                state,
                def,
                required,
                &type_scope,
                role_infos,
                role_sig_bindings,
                Some(info.node.text_range()),
            );
        }
    }
    state.ctx.pop_local();
    exported_member_defs
}

#[derive(Debug, Clone)]
struct ImplMemberInfo {
    name: Name,
    has_receiver: bool,
    recv_name: Option<Name>,
    node: SyntaxNode,
    visibility: ImplMemberVisibility,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ImplMemberVisibility {
    Our,
    My,
    Other,
}

fn impl_member_decl_info(node: &SyntaxNode) -> Option<ImplMemberInfo> {
    let (header_kind, visibility) = match node.kind() {
        SyntaxKind::Binding => (
            SyntaxKind::BindingHeader,
            impl_visibility(&child_node(node, SyntaxKind::BindingHeader)?),
        ),
        SyntaxKind::OpDef => (
            SyntaxKind::OpDefHeader,
            impl_visibility(&child_node(node, SyntaxKind::OpDefHeader)?),
        ),
        _ => return None,
    };
    let header = child_node(node, header_kind)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    let recv_name = ident_name(&pattern);
    let name = pattern
        .children()
        .find(|c| c.kind() == SyntaxKind::Field)
        .and_then(|field| {
            field
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find(|t| t.kind() == SyntaxKind::DotField)
                .map(|t| Name(t.text().trim_start_matches('.').trim().to_string()))
        })
        .or_else(|| header_value_name(&header))?;
    let has_receiver = pattern.children().any(|c| c.kind() == SyntaxKind::Field);
    Some(ImplMemberInfo {
        name,
        has_receiver,
        recv_name,
        node: node.clone(),
        visibility,
    })
}

fn impl_visibility(header: &SyntaxNode) -> ImplMemberVisibility {
    if has_token(header, SyntaxKind::Our) {
        ImplMemberVisibility::Our
    } else if has_token(header, SyntaxKind::My) {
        ImplMemberVisibility::My
    } else {
        ImplMemberVisibility::Other
    }
}

fn impl_member_type_scope(
    state: &mut LowerState,
    node: &SyntaxNode,
    impl_scope: &HashMap<String, TypeVar>,
) -> HashMap<String, TypeVar> {
    let header = child_node(node, SyntaxKind::BindingHeader)
        .or_else(|| child_node(node, SyntaxKind::OpDefHeader))
        .unwrap_or_else(|| node.clone());
    let mut scope = impl_scope.clone();
    for name in binding_sig_var_names(&header) {
        if !scope.contains_key(&name) {
            scope.insert(name, state.fresh_tv());
        }
    }
    scope
}

fn collect_impl_role_sig_bindings(
    role_infos: &[RoleArgInfo],
    input_args: &[SigType],
    assoc_eqs: &HashMap<String, SigType>,
) -> HashMap<String, SigType> {
    let mut out = HashMap::new();
    let mut input_iter = input_args.iter();
    for info in role_infos {
        if info.is_input {
            if let Some(sig) = input_iter.next() {
                out.insert(info.name.clone(), sig.clone());
            }
        } else if let Some(sig) = assoc_eqs.get(&info.name) {
            out.insert(info.name.clone(), sig.clone());
        }
    }
    out
}

fn connect_impl_member_expected_type(
    state: &mut LowerState,
    def: crate::ids::DefId,
    required: &RoleMethodInfo,
    type_scope: &HashMap<String, TypeVar>,
    role_infos: &[RoleArgInfo],
    role_sig_bindings: &HashMap<String, SigType>,
    span: Option<rowan::TextRange>,
) {
    let Some(&method_tv) = state.def_tvs.get(&def) else {
        return;
    };
    let mut role_pos_vars = type_scope.clone();
    let mut role_neg_vars = type_scope.clone();
    let role_constraint = RoleConstraint {
        role: required.role.clone(),
        args: role_infos
            .iter()
            .filter_map(|info| {
                let sig = role_sig_bindings.get(&info.name)?;
                Some(RoleConstraintArg {
                    pos: lower_pure_sig_pos_id(state, sig, &mut role_pos_vars),
                    neg: lower_pure_sig_neg_id(state, sig, &mut role_neg_vars),
                })
            })
            .collect(),
    };
    state.infer.add_role_constraint(def, role_constraint);
    let Some(required_sig) = required.sig.as_ref() else {
        return;
    };
    let expected_sig = substitute_role_sig_type(required_sig, role_sig_bindings);
    let (expected_eff, expected_ret) = match &expected_sig {
        SigType::EffectPrefixed { eff, ret, .. } => (Some(eff.clone()), ret.as_ref().clone()),
        other => (None, other.clone()),
    };
    let mut pos_vars = type_scope.clone();
    let mut neg_vars = type_scope.clone();
    let mut neg_sig = lower_pure_sig_neg_id(state, &expected_ret, &mut neg_vars);
    if required.has_receiver {
        let Some(receiver_name) = role_infos
            .iter()
            .find(|info| info.is_input)
            .map(|info| &info.name)
        else {
            return;
        };
        let Some(receiver_sig) = role_sig_bindings.get(receiver_name) else {
            return;
        };
        let recv_pos = lower_pure_sig_pos_id(state, receiver_sig, &mut pos_vars);
        let outer_ret_eff_neg = expected_eff
            .as_ref()
            .map(|row| crate::lower::signature::lower_sig_row_neg_id(state, row, &mut neg_vars))
            .unwrap_or(state.infer.arena.empty_neg_row);
        neg_sig = state.infer.alloc_neg(Neg::Fun {
            arg: recv_pos,
            arg_eff: state.infer.arena.empty_pos_row,
            ret_eff: outer_ret_eff_neg,
            ret: neg_sig,
        });
    }
    let cause = crate::diagnostic::ConstraintCause {
        span,
        reason: ConstraintReason::ImplMember,
    };
    state
        .infer
        .constrain_with_cause(Pos::Var(method_tv), neg_sig, cause);
}

fn lower_impl_receiver_member(
    state: &mut LowerState,
    info: &ImplMemberInfo,
    required: &RoleMethodInfo,
    method_def: crate::ids::DefId,
    type_scope: &HashMap<String, TypeVar>,
    role_infos: &[RoleArgInfo],
    role_sig_bindings: &HashMap<String, SigType>,
) {
    let Some(body_node) = child_node(&info.node, SyntaxKind::BindingBody) else {
        return;
    };
    let Some(header) = child_node(&info.node, SyntaxKind::BindingHeader) else {
        return;
    };
    let Some(pattern) = child_node(&header, SyntaxKind::Pattern) else {
        return;
    };
    let Some(recv_name) = &info.recv_name else {
        return;
    };
    let Some(receiver_name) = role_infos
        .iter()
        .find(|item| item.is_input)
        .map(|item| &item.name)
    else {
        return;
    };
    let Some(receiver_sig) = role_sig_bindings.get(receiver_name) else {
        return;
    };
    let Some(&method_tv) = state.def_tvs.get(&method_def) else {
        return;
    };

    state.with_type_scope(type_scope.clone(), |state| {
        let arg_pats: Vec<ArgPatInfo> = collect_header_args(&pattern)
            .into_iter()
            .map(|arg| make_arg_pat_info(state, arg))
            .collect();
        for arg_pat in &arg_pats {
            state.register_def_owner(arg_pat.def, method_def);
            for (_, def) in &arg_pat.local_bindings {
                state.register_def_owner(*def, method_def);
            }
        }

        let recv_def = state.fresh_def();
        let recv_tv = state.fresh_tv();
        state.register_def_tv(recv_def, recv_tv);
        state.register_def_owner(recv_def, method_def);
        let mut recv_pos_vars = type_scope.clone();
        let mut recv_neg_vars = type_scope.clone();
        let recv_pos = lower_pure_sig_pos_id(state, receiver_sig, &mut recv_pos_vars);
        let recv_neg = lower_pure_sig_neg_id(state, receiver_sig, &mut recv_neg_vars);
        state.infer.constrain(recv_pos, Neg::Var(recv_tv));
        state.infer.constrain(Pos::Var(recv_tv), recv_neg);

        state.ctx.push_local();
        state.ctx.bind_local(recv_name.clone(), recv_def);
        for arg_pat in &arg_pats {
            for (name, def) in &arg_pat.local_bindings {
                state.ctx.bind_local(name.clone(), *def);
            }
        }
        let body = state.with_owner(method_def, |state| lower_binding_body(state, &body_node));
        state.ctx.pop_local();
        let constrained_body = wrap_header_lambdas(state, body.clone(), arg_pats.clone());
        let Some(required_sig) = required.sig.as_ref() else {
            return;
        };
        let expected_sig = substitute_role_sig_type(required_sig, role_sig_bindings);
        let mut expected_pos_vars = type_scope.clone();
        let mut expected_neg_vars = type_scope.clone();
        let _expected_pos = lower_pure_sig_pos_id(state, &expected_sig, &mut expected_pos_vars);
        let expected_neg = lower_pure_sig_neg_id(state, &expected_sig, &mut expected_neg_vars);
        state
            .infer
            .constrain(Pos::Var(constrained_body.tv), expected_neg);
        let mut all_arg_pats = Vec::with_capacity(arg_pats.len() + 1);
        all_arg_pats.push(ArgPatInfo {
            def: recv_def,
            tv: recv_tv,
            arg_eff_tv: state.fresh_exact_pure_eff_tv(),
            read_eff_tv: None,
            pat: Some(TypedPat {
                tv: recv_tv,
                kind: crate::ast::expr::PatKind::UnresolvedName(recv_name.clone()),
            }),
            local_bindings: vec![(recv_name.clone(), recv_def)],
            ann: None,
            unit_arg: false,
        });
        all_arg_pats.extend(arg_pats);
        let principal_body = wrap_header_lambdas(state, body, all_arg_pats);
        state.insert_principal_body(method_def, principal_body);

        state.runtime_export_schemes.insert(
            method_def,
            runtime_export_scheme(state, receiver_sig, &expected_sig),
        );

        let constrained_sig = state.infer.alloc_pos(Pos::Fun {
            arg: state.infer.alloc_neg(Neg::Var(recv_tv)),
            arg_eff: state.infer.arena.empty_neg_row,
            ret_eff: state.infer.alloc_pos(Pos::Var(constrained_body.eff)),
            ret: state.infer.alloc_pos(Pos::Var(constrained_body.tv)),
        });
        state.infer.constrain(constrained_sig, Neg::Var(method_tv));
        state.infer.constrain(
            Pos::Var(method_tv),
            state.infer.alloc_neg(Neg::Fun {
                arg: state.infer.alloc_pos(Pos::Var(recv_tv)),
                arg_eff: state.infer.arena.empty_pos_row,
                ret_eff: state.infer.alloc_neg(Neg::Var(constrained_body.eff)),
                ret: state.infer.alloc_neg(Neg::Var(constrained_body.tv)),
            }),
        );
    });
}
