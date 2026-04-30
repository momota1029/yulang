use super::*;

use crate::types::{Neg, Pos};

pub(crate) fn lower_impl_decl(state: &mut LowerState, node: &SyntaxNode) {
    let impl_def = state.fresh_def();
    let Some(head) = child_node(node, SyntaxKind::TypeExpr) else {
        return;
    };
    let Some(sig) = parse_sig_type_expr(&head) else {
        return;
    };
    let Some((role, args)) = sig_type_head(&sig) else {
        return;
    };
    let role = canonical_role_path(state, &role);
    let assoc_eqs = collect_impl_assoc_type_equations(node);
    let role_infos = state.infer.role_arg_infos_of(&role);
    let mut impl_scope_names = binding_sig_var_names(node);
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
    let mut pos_vars = type_scope.clone();
    let mut neg_vars = type_scope.clone();
    let mut neg_sig = lower_pure_sig_neg_id(state, &expected_sig, &mut neg_vars);
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
        neg_sig = state.infer.alloc_neg(Neg::Fun {
            arg: recv_pos,
            arg_eff: state.infer.arena.empty_pos_row,
            ret_eff: state.infer.arena.empty_neg_row,
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
        state.principal_bodies.insert(method_def, principal_body);

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
