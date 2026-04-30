use yulang_parser::lex::SyntaxKind;

use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Path, Visibility};

/// `act Console: ...` を lowering する。
///
/// act 名を型名前空間に登録し、同名の companion module を作る。
/// companion module 配下の値が method / operation 解決の対象になる。
pub(crate) fn lower_act_decl(state: &mut LowerState, node: &SyntaxNode) {
    let Some(name) = super::super::ident_or_sigil_name(node) else {
        return;
    };
    let visibility = act_visibility(node);
    let mut effect_segments = state.ctx.current_module_path().segments;
    effect_segments.push(name.clone());
    let effect_path = Path {
        segments: effect_segments,
    };
    state
        .act_templates
        .insert(effect_path.clone(), node.clone());
    let act_scope = super::super::collect_act_type_scope(state, node);
    let act_arg_tvs = crate::lower::signature::ordered_act_type_vars(node, &act_scope);
    let act_args = act_arg_tvs
        .iter()
        .copied()
        .map(|tv| (tv, tv))
        .collect::<Vec<_>>();

    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);

    let mid = state.ctx.current_module;
    state.insert_type_with_visibility(mid, name.clone(), def, visibility);
    state
        .effect_arities
        .insert(effect_path.clone(), act_arg_tvs.len());
    state
        .effect_args
        .insert(effect_path.clone(), act_args.clone());

    let act_copy = super::prepare_act_copy(state, node, &act_scope, &act_args);

    let alias_owner = state.ctx.modules.node(mid).parent.unwrap_or(mid);

    super::super::with_companion_module(state, name.clone(), |state| {
        state.insert_type_alias_with_visibility(alias_owner, name.clone(), def, visibility);
        state.insert_module_alias_with_visibility(
            alias_owner,
            name.clone(),
            state.ctx.current_module,
            visibility,
        );
        if let Some(copy) = act_copy {
            super::lower_act_copy_body(state, copy, &effect_path, &act_args);
        }

        let body_node = super::super::child_node(node, SyntaxKind::IndentBlock)
            .or_else(|| super::super::child_node(node, SyntaxKind::BraceGroup));
        if let Some(body) = body_node {
            super::lower_act_body(state, &body, effect_path, &act_scope, &act_arg_tvs, None);
        }
    });
}

fn act_visibility(node: &SyntaxNode) -> Visibility {
    if super::super::has_token(node, SyntaxKind::Pub) {
        Visibility::Pub
    } else if super::super::has_token(node, SyntaxKind::Our) {
        Visibility::Our
    } else if super::super::has_token(node, SyntaxKind::My) {
        Visibility::My
    } else {
        Visibility::Pub
    }
}
