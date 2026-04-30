use yulang_parser::lex::SyntaxKind;

use crate::ids::DefId;
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Visibility as ModuleVisibility};

/// Binding ヘッダを走査して DefId/TypeVar を確保し、テーブルに登録する。
///
/// `my x = e` / `my f x = e` どちらも「束縛名」は Pattern の先頭 Ident。
/// タプルパターン `my (x, y) = e` は PatParenGroup 内のすべての名前を登録する。
pub(crate) fn preregister_binding(state: &mut LowerState, node: &SyntaxNode) -> Option<DefId> {
    let header = super::super::child_node(node, SyntaxKind::BindingHeader)
        .or_else(|| super::super::child_node(node, SyntaxKind::OpDefHeader))?;
    let is_pub = !state.force_local_bindings()
        && (super::super::has_token(&header, SyntaxKind::Our)
            || super::super::has_token(&header, SyntaxKind::Pub));
    let is_module_private = is_module_private_binding(state, is_pub);
    if node.kind() != SyntaxKind::OpDef {
        if let Some(info) = super::super::global_extension_method_header(&header) {
            return preregister_dotted_method(state, &header, &info);
        }
    }
    let pat_node = super::super::child_node(&header, SyntaxKind::Pattern);
    let direct_ident = if node.kind() == SyntaxKind::OpDef {
        super::super::header_value_name(&header)
    } else {
        super::super::direct_binding_name(pat_node.as_ref()?)
    };

    if let Some(name) = direct_ident {
        let def = state.fresh_def();
        let tv = state.fresh_tv();
        let operator_fixity = if node.kind() == SyntaxKind::OpDef {
            Some(super::super::header_operator_fixity(&header)?)
        } else {
            None
        };
        state.register_def_tv(def, tv);
        state.mark_let_bound_def(def);
        if let Some(owner) = state.current_owner {
            state.register_def_owner(def, owner);
        }
        state.register_def_name(def, name.clone());
        if let Some(fixity) = operator_fixity {
            state.ctx.mark_operator_def(def, fixity);
        }
        if is_pub {
            state.insert_value(state.ctx.current_module, name, def);
        } else if is_module_private {
            state.insert_value_with_visibility(
                state.ctx.current_module,
                name,
                def,
                ModuleVisibility::My,
            );
        } else {
            state.ctx.bind_local(name, def);
        }
        if let Some(fixity) = operator_fixity {
            state.ctx.modules.insert_operator_value_with_visibility(
                state.ctx.current_module,
                super::super::header_value_name(&header)?,
                fixity,
                def,
                if is_pub {
                    ModuleVisibility::Pub
                } else if is_module_private {
                    ModuleVisibility::My
                } else {
                    ModuleVisibility::Pub
                },
            );
        }
        return Some(def);
    }

    preregister_pat_names(state, pat_node.as_ref()?, is_pub, is_module_private);
    None
}

pub(crate) fn preregister_binding_as_module_value(
    state: &mut LowerState,
    node: &SyntaxNode,
) -> Option<DefId> {
    let header = super::super::child_node(node, SyntaxKind::BindingHeader)
        .or_else(|| super::super::child_node(node, SyntaxKind::OpDefHeader))?;
    if node.kind() != SyntaxKind::OpDef {
        if let Some(info) = super::super::global_extension_method_header(&header) {
            return preregister_dotted_method(state, &header, &info);
        }
    }
    let pat_node = super::super::child_node(&header, SyntaxKind::Pattern);
    let direct_ident = if node.kind() == SyntaxKind::OpDef {
        super::super::header_value_name(&header)
    } else {
        super::super::direct_binding_name(pat_node.as_ref()?)
    };

    if let Some(name) = direct_ident {
        let def = state.fresh_def();
        let tv = state.fresh_tv();
        let operator_fixity = if node.kind() == SyntaxKind::OpDef {
            Some(super::super::header_operator_fixity(&header)?)
        } else {
            None
        };
        state.register_def_tv(def, tv);
        state.mark_let_bound_def(def);
        state.register_def_name(def, name.clone());
        if let Some(fixity) = operator_fixity {
            state.ctx.mark_operator_def(def, fixity);
            state.ctx.modules.insert_operator_value_with_visibility(
                state.ctx.current_module,
                name.clone(),
                fixity,
                def,
                ModuleVisibility::Pub,
            );
        }
        state.insert_value(state.ctx.current_module, name, def);
        return Some(def);
    }

    preregister_pat_names_as_module_values(state, pat_node.as_ref()?);
    None
}

fn preregister_dotted_method(
    state: &mut LowerState,
    header: &SyntaxNode,
    info: &super::super::GlobalExtensionMethodHeader,
) -> Option<DefId> {
    let def = state.fresh_def();
    let tv = state.fresh_tv();
    let effect_path = state.current_act_effect_path.clone();
    let hidden_name = if let Some(effect_path) = &effect_path {
        super::super::effect_method_hidden_name(effect_path, &info.name, def)
    } else {
        super::super::extension_method_hidden_name(&info.name, def)
    };
    let visibility = super::super::header_module_visibility(header);
    state.register_def_tv(def, tv);
    state.mark_let_bound_def(def);
    state.register_def_name(def, hidden_name.clone());
    state.insert_value_with_visibility(state.ctx.current_module, hidden_name, def, visibility);
    if let Some(effect_path) = effect_path {
        state
            .infer
            .register_effect_method(crate::solve::EffectMethodInfo {
                name: info.name.clone(),
                effect: effect_path,
                def,
                module: state.ctx.current_module,
                visibility,
                receiver_expects_computation: false,
            });
    } else {
        state
            .infer
            .register_extension_method(crate::solve::ExtensionMethodInfo {
                name: info.name.clone(),
                def,
                module: state.ctx.current_module,
                visibility,
                receiver_expects_computation: false,
            });
    }
    Some(def)
}

fn preregister_pat_names(
    state: &mut LowerState,
    node: &SyntaxNode,
    is_pub: bool,
    is_module_private: bool,
) {
    match node.kind() {
        SyntaxKind::Pattern | SyntaxKind::PatOr | SyntaxKind::PatAs | SyntaxKind::PatParenGroup => {
            for child in node.children() {
                preregister_pat_names(state, &child, is_pub, is_module_private);
            }
            let direct = node
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find_map(|t| match t.kind() {
                    SyntaxKind::Ident => Some(Name(t.text().to_string())),
                    SyntaxKind::SigilIdent => super::super::sigil_pattern_binding_name(t.text()),
                    _ => None,
                });
            if let Some(name) = direct {
                let def = state.fresh_def();
                let tv = state.fresh_tv();
                state.register_def_tv(def, tv);
                state.mark_let_bound_def(def);
                if let Some(owner) = state.current_owner {
                    state.register_def_owner(def, owner);
                }
                state.register_def_name(def, name.clone());
                if is_pub {
                    state.insert_value(state.ctx.current_module, name, def);
                } else if is_module_private {
                    state.insert_value_with_visibility(
                        state.ctx.current_module,
                        name,
                        def,
                        ModuleVisibility::My,
                    );
                } else {
                    state.ctx.bind_local(name, def);
                }
            }
        }
        _ => {}
    }
}

fn is_module_private_binding(state: &LowerState, is_pub: bool) -> bool {
    !is_pub && state.current_owner.is_none() && state.ctx.local_depth() == 1
}

fn preregister_pat_names_as_module_values(state: &mut LowerState, node: &SyntaxNode) {
    match node.kind() {
        SyntaxKind::Pattern | SyntaxKind::PatOr | SyntaxKind::PatAs | SyntaxKind::PatParenGroup => {
            for child in node.children() {
                preregister_pat_names_as_module_values(state, &child);
            }
            let direct = node
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find_map(|t| match t.kind() {
                    SyntaxKind::Ident => Some(Name(t.text().to_string())),
                    SyntaxKind::SigilIdent => super::super::sigil_pattern_binding_name(t.text()),
                    _ => None,
                });
            if let Some(name) = direct {
                let def = state.fresh_def();
                let tv = state.fresh_tv();
                state.register_def_tv(def, tv);
                state.mark_let_bound_def(def);
                state.register_def_name(def, name.clone());
                state.insert_value(state.ctx.current_module, name, def);
            }
        }
        _ => {}
    }
}
