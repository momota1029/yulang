use super::*;

pub(crate) fn lower_role_decl(state: &mut LowerState, node: &SyntaxNode) {
    let Some(name) = child_node(node, SyntaxKind::TypeExpr).and_then(|head| ident_name(&head))
    else {
        return;
    };
    let mut role_path_segments = state.ctx.current_module_path().segments;
    role_path_segments.push(name.clone());
    let role_path = Path {
        segments: role_path_segments,
    };
    let input_names = act_type_param_names(node);
    let assoc_names = collect_role_assoc_type_names(node);
    let role_arg_names = input_names
        .iter()
        .cloned()
        .chain(assoc_names.iter().cloned())
        .collect::<Vec<_>>();
    let role_scope = fresh_type_scope(state, &role_arg_names);
    let role_arg_tvs = role_arg_names
        .iter()
        .filter_map(|name| role_scope.get(name).copied())
        .collect::<Vec<_>>();
    state.infer.register_role_arg_infos(
        role_path.clone(),
        input_names
            .iter()
            .cloned()
            .map(|name| RoleArgInfo {
                name,
                is_input: true,
            })
            .chain(assoc_names.iter().cloned().map(|name| RoleArgInfo {
                name,
                is_input: false,
            }))
            .collect(),
    );

    let role_def = state.fresh_def();
    let role_tv = state.fresh_tv();
    state.register_def_tv(role_def, role_tv);

    let mid = state.ctx.current_module;
    state.insert_type(mid, name.clone(), role_def);

    let saved = state.ctx.enter_module(name);
    state.mark_companion_module(state.ctx.current_module);
    let body_node = child_node(node, SyntaxKind::IndentBlock)
        .or_else(|| child_node(node, SyntaxKind::BraceGroup));
    if let Some(body) = body_node {
        state.with_type_scope(role_scope.clone(), |state| {
            state.with_owner(role_def, |state| {
                lower_role_body(
                    state,
                    &body,
                    &role_path,
                    &role_scope,
                    &role_arg_names,
                    &role_arg_tvs,
                );
            });
        });
    }
    state.ctx.leave_module(saved);
}

fn lower_role_body(
    state: &mut LowerState,
    node: &SyntaxNode,
    role_path: &Path,
    role_scope: &HashMap<String, TypeVar>,
    role_arg_names: &[String],
    role_arg_tvs: &[TypeVar],
) {
    let mut items = Vec::new();
    collect_block_items(node, &mut items);
    for item in &items {
        if item.kind() == SyntaxKind::WhereClause {
            lower_where_clause(state, item);
        }
    }
    for item in items {
        match item.kind() {
            SyntaxKind::Binding | SyntaxKind::OpDef => {
                lower_role_method_binding(
                    state,
                    &item,
                    role_path,
                    role_scope,
                    role_arg_names,
                    role_arg_tvs,
                );
            }
            _ => {}
        }
    }
}

fn lower_role_method_binding(
    state: &mut LowerState,
    binding: &SyntaxNode,
    role_path: &Path,
    role_scope: &HashMap<String, TypeVar>,
    role_arg_names: &[String],
    role_arg_tvs: &[TypeVar],
) -> Option<()> {
    let header_kind = match binding.kind() {
        SyntaxKind::Binding => SyntaxKind::BindingHeader,
        SyntaxKind::OpDef => SyntaxKind::OpDefHeader,
        _ => return None,
    };
    let header = child_node(binding, header_kind)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    let method_name = pattern
        .children()
        .find(|c| c.kind() == SyntaxKind::Field)
        .and_then(|field| {
            field
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find(|t| t.kind() == SyntaxKind::DotField)
                .map(|t| Name(t.text().trim_start_matches('.').trim().to_string()))
        })
        .or_else(|| ident_name(&pattern))?;
    let has_receiver = pattern.children().any(|c| c.kind() == SyntaxKind::Field);
    let type_expr = pattern
        .children()
        .find(|c| c.kind() == SyntaxKind::TypeAnn)
        .and_then(|ann| ann.children().find(|c| c.kind() == SyntaxKind::TypeExpr));
    let body_node = child_node(binding, SyntaxKind::BindingBody)
        .or_else(|| child_node(binding, SyntaxKind::OpDefBody));
    let sig = type_expr.as_ref().and_then(parse_sig_type_expr);
    if sig.is_none() && body_node.is_none() {
        return None;
    }

    let method_def = state.fresh_def();
    let method_tv = state.fresh_tv();
    state.register_def_tv(method_def, method_tv);
    state.insert_value(state.ctx.current_module, method_name.clone(), method_def);
    let role_constraint = RoleConstraint {
        role: role_path.clone(),
        args: role_arg_tvs
            .iter()
            .map(|tv| RoleConstraintArg {
                pos: state.infer.alloc_pos(crate::types::Pos::Var(*tv)),
                neg: state.infer.alloc_neg(crate::types::Neg::Var(*tv)),
            })
            .collect(),
    };
    state.infer.register_role_method(
        method_name.clone(),
        RoleMethodInfo {
            name: method_name.clone(),
            def: method_def,
            role: role_path.clone(),
            args: role_arg_tvs.to_vec(),
            sig: sig.clone(),
            has_receiver,
            has_default_body: body_node.is_some(),
        },
    );
    state.mark_selection_lookup_dirty();
    state.infer.add_role_constraint(method_def, role_constraint);
    if let Some(role_owner) = state.current_owner {
        for inherited in state.infer.role_constraints_of(role_owner) {
            state.infer.add_role_constraint(method_def, inherited);
        }
    }
    if let Some(sig) = sig.as_ref() {
        let mut pos_vars = role_scope.clone();
        let mut neg_vars = role_scope.clone();
        let mut input_names = collect_fun_input_sig_vars(sig);
        if has_receiver {
            if let Some(receiver_name) = role_arg_names.first().cloned() {
                input_names.insert(receiver_name);
            }
        }
        state.infer.mark_role_input_args(role_path, &input_names);

        let mut pos_sig = lower_pure_sig_pos_id(state, sig, &mut pos_vars);
        let mut neg_sig = lower_pure_sig_neg_id(state, sig, &mut neg_vars);
        if has_receiver {
            let Some(&recv_tv) = role_arg_tvs.first() else {
                return None;
            };
            pos_sig = state.infer.alloc_pos(crate::types::Pos::Fun {
                arg: state.infer.alloc_neg(crate::types::Neg::Var(recv_tv)),
                arg_eff: state.infer.arena.empty_neg_row,
                ret_eff: state.infer.arena.empty_pos_row,
                ret: pos_sig,
            });
            neg_sig = state.infer.alloc_neg(crate::types::Neg::Fun {
                arg: state.infer.alloc_pos(crate::types::Pos::Var(recv_tv)),
                arg_eff: state.infer.arena.empty_pos_row,
                ret_eff: state.infer.arena.empty_neg_row,
                ret: neg_sig,
            });
        }
        let frozen = freeze_pos_scheme_with_non_generic(
            &state.infer,
            pos_sig,
            &state.infer.non_generic_vars_of(method_def),
        );
        state.infer.store_frozen_scheme(method_def, frozen);
        state
            .infer
            .constrain(pos_sig, crate::types::Neg::Var(method_tv));
        state
            .infer
            .constrain(crate::types::Pos::Var(method_tv), neg_sig);
    }
    if body_node.is_some() {
        lower_role_method_default_body(
            state,
            binding,
            method_def,
            role_path,
            role_scope,
            role_arg_names,
            sig.as_ref(),
            has_receiver,
        );
    }
    Some(())
}

fn lower_role_method_default_body(
    state: &mut LowerState,
    binding: &SyntaxNode,
    method_def: crate::ids::DefId,
    role_path: &Path,
    role_scope: &HashMap<String, TypeVar>,
    role_arg_names: &[String],
    sig: Option<&SigType>,
    has_receiver: bool,
) {
    let Some(header) = child_node(binding, SyntaxKind::BindingHeader)
        .or_else(|| child_node(binding, SyntaxKind::OpDefHeader))
    else {
        return;
    };
    let Some(pattern) = child_node(&header, SyntaxKind::Pattern) else {
        return;
    };
    let Some(body_node) = child_node(binding, SyntaxKind::BindingBody)
        .or_else(|| child_node(binding, SyntaxKind::OpDefBody))
    else {
        return;
    };
    let Some(&method_tv) = state.def_tvs.get(&method_def) else {
        return;
    };
    let recv_name = ident_name(&pattern);
    state.with_type_scope(role_scope.clone(), |state| {
        let mut arg_pats: Vec<ArgPatInfo> = collect_header_args(&pattern)
            .into_iter()
            .map(|arg| make_arg_pat_info(state, arg))
            .collect();
        if let Some(recv_name) = recv_name.as_ref() {
            if arg_pats.first().is_some_and(|arg_pat| {
                arg_pat
                    .local_bindings
                    .iter()
                    .any(|(name, _)| name == recv_name)
            }) {
                arg_pats.remove(0);
            }
        }
        for arg_pat in &arg_pats {
            state.register_def_owner(arg_pat.def, method_def);
            for (_, def) in &arg_pat.local_bindings {
                state.register_def_owner(*def, method_def);
            }
        }

        let mut recv_info = None;
        if has_receiver {
            let Some(recv_name) = recv_name.clone() else {
                return;
            };
            let Some(receiver_arg_name) = role_arg_names.first() else {
                return;
            };
            let Some(&receiver_role_tv) = role_scope.get(receiver_arg_name) else {
                return;
            };
            let recv_def = state.fresh_def();
            let recv_tv = state.fresh_tv();
            state.register_def_tv(recv_def, recv_tv);
            state.register_def_owner(recv_def, method_def);
            state.infer.constrain(
                crate::types::Pos::Var(receiver_role_tv),
                crate::types::Neg::Var(recv_tv),
            );
            state.infer.constrain(
                crate::types::Pos::Var(recv_tv),
                crate::types::Neg::Var(receiver_role_tv),
            );
            recv_info = Some((recv_name, recv_def, recv_tv));
        }

        state.ctx.push_local();
        if let Some((recv_name, recv_def, _)) = &recv_info {
            state.ctx.bind_local(recv_name.clone(), *recv_def);
        }
        for arg_pat in &arg_pats {
            for (name, def) in &arg_pat.local_bindings {
                state.ctx.bind_local(name.clone(), *def);
            }
        }
        let body = state.with_owner(method_def, |state| lower_binding_body(state, &body_node));
        state.ctx.pop_local();

        if let Some(sig) = sig {
            let mut expected_pos_vars = role_scope.clone();
            let mut expected_neg_vars = role_scope.clone();
            let _expected_pos = lower_pure_sig_pos_id(state, sig, &mut expected_pos_vars);
            let expected_neg = lower_pure_sig_neg_id(state, sig, &mut expected_neg_vars);
            let constrained_body = wrap_header_lambdas(state, body.clone(), arg_pats.clone());
            state
                .infer
                .constrain(crate::types::Pos::Var(constrained_body.tv), expected_neg);
            if let Some(receiver_arg_name) = role_arg_names.first() {
                if has_receiver {
                    let receiver_sig = SigType::Var(SigVar {
                        name: receiver_arg_name.clone(),
                        span: pattern.text_range(),
                    });
                    let role_sig_vars = role_arg_names
                        .iter()
                        .map(|name| {
                            (
                                name.clone(),
                                SigType::Var(SigVar {
                                    name: name.clone(),
                                    span: pattern.text_range(),
                                }),
                            )
                        })
                        .collect::<HashMap<_, _>>();
                    let receiver_sig = substitute_role_sig_type(&receiver_sig, &role_sig_vars);
                    let sig = substitute_role_sig_type(sig, &role_sig_vars);
                    state.runtime_export_schemes.insert(
                        method_def,
                        runtime_export_role_method_scheme(state, role_path, &receiver_sig, &sig),
                    );
                }
            }
        }

        let mut all_arg_pats = arg_pats;
        if let Some((recv_name, recv_def, recv_tv)) = recv_info {
            all_arg_pats.insert(
                0,
                ArgPatInfo {
                    def: recv_def,
                    tv: recv_tv,
                    arg_eff_tv: state.fresh_exact_pure_eff_tv(),
                    read_eff_tv: None,
                    pat: Some(TypedPat {
                        tv: recv_tv,
                        kind: crate::ast::expr::PatKind::UnresolvedName(recv_name.clone()),
                    }),
                    local_bindings: vec![(recv_name, recv_def)],
                    ann: None,
                    unit_arg: false,
                },
            );
        }
        let principal_body = wrap_header_lambdas(state, body.clone(), all_arg_pats);
        let principal_body_tv = principal_body.tv;
        state.principal_bodies.insert(method_def, principal_body);
        state.infer.constrain(
            crate::types::Pos::Var(principal_body_tv),
            crate::types::Neg::Var(method_tv),
        );
        state.infer.constrain(
            crate::types::Pos::Var(method_tv),
            crate::types::Neg::Var(principal_body_tv),
        );
    });
}

fn collect_fun_input_sig_vars(sig: &SigType) -> HashSet<String> {
    let mut out = HashSet::new();
    collect_fun_input_sig_vars_inner(sig, &mut out);
    out
}
