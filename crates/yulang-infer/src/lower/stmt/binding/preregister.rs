use rowan::TextRange;
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
        if let Some(pat) = pat_node.as_ref() {
            register_binding_call_shape_hint(state, def, pat);
        }
        state.register_def_span(
            def,
            binding_name_span(&header).unwrap_or(header.text_range()),
        );
        let operator_name = name.clone();
        if let Some(fixity) = operator_fixity {
            state.ctx.mark_operator_def(def, fixity);
            if super::super::header_operator_is_lazy(&header) {
                state.ctx.mark_lazy_operator_def(def);
            }
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
                operator_name,
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
        if let Some(pat) = pat_node.as_ref() {
            register_binding_call_shape_hint(state, def, pat);
        }
        state.register_def_span(
            def,
            binding_name_span(&header).unwrap_or(header.text_range()),
        );
        if let Some(fixity) = operator_fixity {
            state.ctx.mark_operator_def(def, fixity);
            if super::super::header_operator_is_lazy(&header) {
                state.ctx.mark_lazy_operator_def(def);
            }
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

fn register_binding_call_shape_hint(state: &mut LowerState, def: DefId, pat_node: &SyntaxNode) {
    // ヘッダ引数を持つ束縛（`my f x = ...` や `my add (x)(y): int = ...`）は関数値ねぇ。
    // 末尾の型注釈は返り値型であって束縛そのものの値の型ではないから、callable として扱う。
    // ここを non-callable と誤登録すると、callee shadowing が prelude 側の同名関数を
    // 選んでしまい、ユーザ定義の束縛が export から外れる。
    if !super::collect_header_args(pat_node).is_empty() {
        state.register_callable_value_def(def);
        return;
    }
    if let Some(sig) = binding_pattern_sig(pat_node) {
        super::register_sig_call_shape_hint(state, def, &sig);
    }
}

fn binding_pattern_sig(node: &SyntaxNode) -> Option<crate::lower::signature::SigType> {
    let ann = crate::lower::ann::pat_type_ann_node(node)?;
    let type_expr = ann
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)?;
    crate::lower::signature::parse_sig_type_expr(&type_expr)
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
        SyntaxKind::PatField => {
            for child in node.children() {
                if child.kind() != SyntaxKind::Expr {
                    preregister_pat_names(state, &child, is_pub, is_module_private);
                }
            }
            let has_nested_pat = node.children().any(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Pattern | SyntaxKind::PatOr | SyntaxKind::PatAs
                )
            });
            if !has_nested_pat
                && let Some((name, span)) = node
                    .children_with_tokens()
                    .filter_map(|it| it.into_token())
                    .find(|t| t.kind() == SyntaxKind::Ident)
                    .map(|t| (Name(t.text().to_string()), t.text_range()))
            {
                preregister_pat_name(state, name, span, is_pub, is_module_private);
            }
        }
        SyntaxKind::Pattern
        | SyntaxKind::PatOr
        | SyntaxKind::PatAs
        | SyntaxKind::PatParenGroup
        | SyntaxKind::PatList
        | SyntaxKind::PatRecord
        | SyntaxKind::PatSpread
        | SyntaxKind::ApplyML
        | SyntaxKind::ApplyC => {
            for child in node.children() {
                if child.kind() != SyntaxKind::Expr {
                    preregister_pat_names(state, &child, is_pub, is_module_private);
                }
            }
            let direct = node
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find_map(|t| match t.kind() {
                    SyntaxKind::Ident => Some((Name(t.text().to_string()), t.text_range())),
                    SyntaxKind::SigilIdent => super::super::sigil_pattern_binding_name(t.text())
                        .map(|name| (name, t.text_range())),
                    _ => None,
                });
            if let Some((name, span)) = direct {
                preregister_pat_name(state, name, span, is_pub, is_module_private);
            }
        }
        _ => {}
    }
}

fn preregister_pat_name(
    state: &mut LowerState,
    name: Name,
    span: TextRange,
    is_pub: bool,
    is_module_private: bool,
) {
    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.mark_let_bound_def(def);
    if let Some(owner) = state.current_owner {
        state.register_def_owner(def, owner);
    }
    state.register_def_name(def, name.clone());
    state.register_def_span(def, span);
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

fn is_module_private_binding(state: &LowerState, is_pub: bool) -> bool {
    !is_pub && state.current_owner.is_none() && state.ctx.local_depth() == 1
}

fn binding_name_span(header: &SyntaxNode) -> Option<TextRange> {
    if header.kind() == SyntaxKind::OpDefHeader {
        return token_span(header, SyntaxKind::OpName);
    }
    let pattern = super::super::child_node(header, SyntaxKind::Pattern)?;
    token_span(&pattern, SyntaxKind::Ident).or_else(|| token_span(&pattern, SyntaxKind::OpName))
}

fn token_span(node: &SyntaxNode, kind: SyntaxKind) -> Option<TextRange> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|token| token.kind() == kind)
        .map(|token| token.text_range())
}

fn preregister_pat_names_as_module_values(state: &mut LowerState, node: &SyntaxNode) {
    match node.kind() {
        SyntaxKind::PatField => {
            for child in node.children() {
                if child.kind() != SyntaxKind::Expr {
                    preregister_pat_names_as_module_values(state, &child);
                }
            }
            let has_nested_pat = node.children().any(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::Pattern | SyntaxKind::PatOr | SyntaxKind::PatAs
                )
            });
            if !has_nested_pat
                && let Some((name, span)) = node
                    .children_with_tokens()
                    .filter_map(|it| it.into_token())
                    .find(|t| t.kind() == SyntaxKind::Ident)
                    .map(|t| (Name(t.text().to_string()), t.text_range()))
            {
                preregister_pat_name_as_module_value(state, name, span);
            }
        }
        SyntaxKind::Pattern
        | SyntaxKind::PatOr
        | SyntaxKind::PatAs
        | SyntaxKind::PatParenGroup
        | SyntaxKind::PatList
        | SyntaxKind::PatRecord
        | SyntaxKind::PatSpread
        | SyntaxKind::ApplyML
        | SyntaxKind::ApplyC => {
            for child in node.children() {
                if child.kind() != SyntaxKind::Expr {
                    preregister_pat_names_as_module_values(state, &child);
                }
            }
            let direct = node
                .children_with_tokens()
                .filter_map(|it| it.into_token())
                .find_map(|t| match t.kind() {
                    SyntaxKind::Ident => Some((Name(t.text().to_string()), t.text_range())),
                    SyntaxKind::SigilIdent => super::super::sigil_pattern_binding_name(t.text())
                        .map(|name| (name, t.text_range())),
                    _ => None,
                });
            if let Some((name, span)) = direct {
                preregister_pat_name_as_module_value(state, name, span);
            }
        }
        _ => {}
    }
}

fn preregister_pat_name_as_module_value(state: &mut LowerState, name: Name, span: TextRange) {
    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);
    state.mark_let_bound_def(def);
    state.register_def_name(def, name.clone());
    state.register_def_span(def, span);
    state.insert_value(state.ctx.current_module, name, def);
}
