use crate::profile::ProfileClock as Instant;
use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use crate::ids::{NegId, PosId};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

/// act 本体ブロック内の操作宣言（`our op: sig`）を登録する。
pub(crate) fn lower_act_body(
    state: &mut LowerState,
    node: &SyntaxNode,
    effect_path: Path,
    act_scope: &HashMap<String, crate::ids::TypeVar>,
    act_arg_tvs: &[crate::ids::TypeVar],
    selected_names: Option<&Vec<Name>>,
) {
    let start = Instant::now();
    let mut ops = Vec::new();
    let mut acts = Vec::new();
    let mut structs = Vec::new();
    let mut impls = Vec::new();
    let mut bindings = Vec::new();
    let collect_start = Instant::now();
    collect_lowerable_act_body_items(
        node,
        selected_names,
        &mut ops,
        &mut acts,
        &mut structs,
        &mut impls,
        &mut bindings,
    );
    state.lower_detail.lower_act_body_collect_items += collect_start.elapsed();

    let ops_start = Instant::now();
    for child in &ops {
        lower_act_operation_decl(state, child, effect_path.clone(), act_scope, act_arg_tvs);
    }
    state.lower_detail.lower_act_body_ops += ops_start.elapsed();

    for child in &acts {
        super::super::lower_act_decl(state, child);
    }

    for child in &structs {
        super::super::lower_struct_decl(state, child);
    }

    for child in &impls {
        super::super::lower_impl_decl(state, child);
    }

    state.with_act_effect_path(effect_path, |state| {
        let prereg_start = Instant::now();
        for child in &bindings {
            super::super::preregister_binding_as_module_value(state, child);
        }
        state.lower_detail.lower_act_body_preregister += prereg_start.elapsed();

        let bindings_start = Instant::now();
        for child in &bindings {
            super::super::lower_binding(state, child);
        }
        state.lower_detail.lower_act_body_bindings += bindings_start.elapsed();
    });
    state.lower_detail.lower_act_body += start.elapsed();
}

fn collect_lowerable_act_body_items(
    node: &SyntaxNode,
    selected_names: Option<&Vec<Name>>,
    ops: &mut Vec<SyntaxNode>,
    acts: &mut Vec<SyntaxNode>,
    structs: &mut Vec<SyntaxNode>,
    impls: &mut Vec<SyntaxNode>,
    bindings: &mut Vec<SyntaxNode>,
) {
    for child in node.children() {
        match child.kind() {
            SyntaxKind::IndentBlock | SyntaxKind::BraceGroup => {
                collect_lowerable_act_body_items(
                    &child,
                    selected_names,
                    ops,
                    acts,
                    structs,
                    impls,
                    bindings,
                );
            }
            SyntaxKind::ActDecl => {
                let Some(name) = super::super::ident_or_sigil_name(&child) else {
                    continue;
                };
                let info = ActBodyItemInfo {
                    name,
                    is_operation: false,
                };
                if info.is_selected(selected_names) {
                    acts.push(child);
                }
            }
            SyntaxKind::StructDecl => {
                let Some(name) = super::super::ident_or_sigil_name(&child) else {
                    continue;
                };
                let info = ActBodyItemInfo {
                    name,
                    is_operation: false,
                };
                if info.is_selected(selected_names) {
                    structs.push(child);
                }
            }
            SyntaxKind::ImplDecl => {
                let Some(name) = impl_decl_role_name(&child) else {
                    continue;
                };
                let info = ActBodyItemInfo {
                    name,
                    is_operation: false,
                };
                if info.is_selected(selected_names) {
                    impls.push(child);
                }
            }
            SyntaxKind::Binding | SyntaxKind::OpDef => {
                let Some(info) = act_body_item_info(&child) else {
                    continue;
                };
                if !info.is_selected(selected_names) {
                    continue;
                }
                if info.is_operation {
                    ops.push(child);
                } else if child.kind() == SyntaxKind::Binding {
                    bindings.push(child);
                }
            }
            _ => {}
        }
    }
}

fn impl_decl_role_name(node: &SyntaxNode) -> Option<Name> {
    let head = super::super::child_node(node, SyntaxKind::TypeExpr)?;
    let sig = crate::lower::signature::parse_sig_type_expr(&head)?;
    let (role, _) = crate::lower::signature::sig_type_head(&sig)?;
    role.segments.last().cloned()
}

fn act_body_item_info(node: &SyntaxNode) -> Option<ActBodyItemInfo> {
    match node.kind() {
        SyntaxKind::Binding => {
            let header = super::super::child_node(node, SyntaxKind::BindingHeader)?;
            if let Some(method) = super::super::global_extension_method_header(&header) {
                return Some(ActBodyItemInfo {
                    name: method.name,
                    is_operation: false,
                });
            }
            Some(ActBodyItemInfo {
                name: super::super::header_value_name(&header)?,
                is_operation: super::super::child_node(node, SyntaxKind::BindingBody).is_none()
                    && (super::super::has_token(&header, SyntaxKind::My)
                        || super::super::has_token(&header, SyntaxKind::Our)
                        || super::super::has_token(&header, SyntaxKind::Pub))
                    && super::super::descendant_node(&header, SyntaxKind::TypeAnn).is_some(),
            })
        }
        SyntaxKind::OpDef => {
            let header = super::super::child_node(node, SyntaxKind::OpDefHeader)?;
            Some(ActBodyItemInfo {
                name: super::super::header_value_name(&header)?,
                is_operation: true,
            })
        }
        _ => None,
    }
}

struct ActBodyItemInfo {
    name: Name,
    is_operation: bool,
}

impl ActBodyItemInfo {
    fn is_selected(&self, selected_names: Option<&Vec<Name>>) -> bool {
        let Some(selected_names) = selected_names else {
            return true;
        };
        selected_names.iter().any(|selected| selected == &self.name)
    }
}

fn lower_act_operation_decl(
    state: &mut LowerState,
    node: &SyntaxNode,
    effect_path: Path,
    act_scope: &HashMap<String, crate::ids::TypeVar>,
    act_arg_tvs: &[crate::ids::TypeVar],
) -> Option<()> {
    let header_kind = match node.kind() {
        SyntaxKind::Binding => SyntaxKind::BindingHeader,
        SyntaxKind::OpDef => SyntaxKind::OpDefHeader,
        _ => return None,
    };
    let header = super::super::child_node(node, header_kind)?;
    let name = super::super::header_value_name(&header)?;
    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.effect_op_args.insert(
        def,
        act_arg_tvs.iter().copied().map(|tv| (tv, tv)).collect(),
    );
    state
        .effect_op_effect_paths
        .insert(def, effect_path.clone());
    let mid = state.ctx.current_module;
    state.insert_value_with_visibility(
        mid,
        name,
        def,
        super::super::header_module_visibility(&header),
    );
    if let Some((pos_sig, neg_sig)) =
        lower_op_signatures(state, &header, effect_path, act_scope, act_arg_tvs)
    {
        state.effect_op_pos_sigs.insert(def, pos_sig);
        state.effect_op_neg_sigs.insert(def, neg_sig);
        state.infer.constrain(pos_sig, Neg::Var(tv));
        state.infer.constrain(Pos::Var(tv), neg_sig);
        state.infer.store_frozen_scheme(
            def,
            crate::scheme::freeze_pos_scheme(&state.infer, state.effect_op_pos_sigs[&def]),
        );
    }
    Some(())
}

fn lower_op_signatures(
    state: &mut LowerState,
    header: &SyntaxNode,
    effect_path: Path,
    act_scope: &HashMap<String, crate::ids::TypeVar>,
    act_arg_tvs: &[crate::ids::TypeVar],
) -> Option<(PosId, NegId)> {
    let type_expr = super::super::descendant_node(header, SyntaxKind::TypeExpr)?;
    let sig = crate::lower::signature::parse_sig_type_expr(&type_expr)?;
    let mut pos_vars = act_scope.clone();
    let mut neg_vars = act_scope.clone();
    Some((
        crate::lower::signature::lower_sig_pos_id(
            state,
            &sig,
            &mut pos_vars,
            effect_path,
            act_arg_tvs,
        ),
        crate::lower::signature::lower_sig_neg_id(state, &sig, &mut neg_vars, act_arg_tvs),
    ))
}
