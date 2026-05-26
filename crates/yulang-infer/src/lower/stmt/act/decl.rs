use yulang_parser::lex::SyntaxKind;

use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Path, Visibility};

/// `act Console: ...` を lowering する。
///
/// act 名を型名前空間に登録し、同名の companion module を作る。
/// companion module 配下の値が method / operation 解決の対象になる。
pub(crate) fn lower_act_decl(state: &mut LowerState, node: &SyntaxNode) {
    let Some(mut header) = act_decl_header(state, node) else {
        return;
    };
    let already_preregistered = state.act_templates.contains_key(&header.effect_path);
    if !already_preregistered {
        preregister_act_decl(state, node);
        let Some(updated_header) = act_decl_header(state, node) else {
            return;
        };
        header = updated_header;
    }

    let act_copy = super::prepare_act_copy(state, node, &header.act_scope, &header.act_args);
    let saved_module = state.ctx.enter_or_create_module(header.name);
    if let Some(copy) = act_copy {
        super::lower_act_copy_body(state, copy, &header.effect_path, &header.act_args);
    }
    if let Some(body) = act_decl_body(node) {
        super::lower_act_body(
            state,
            &body,
            header.effect_path,
            &header.act_scope,
            &header.act_arg_tvs,
            None,
            true,
        );
    }
    state.ctx.leave_module(saved_module);
}

pub(crate) fn preregister_act_decl(state: &mut LowerState, node: &SyntaxNode) {
    let Some(header) = act_decl_header(state, node) else {
        return;
    };
    if state.act_templates.contains_key(&header.effect_path) {
        return;
    }
    state
        .act_templates
        .insert(header.effect_path.clone(), node.clone());
    let def = state.fresh_def();
    let tv = state.fresh_tv();
    state.register_def_tv(def, tv);

    let mid = state.ctx.current_module;
    state.insert_type_with_visibility(mid, header.name.clone(), def, header.visibility);
    state
        .effect_arities
        .insert(header.effect_path.clone(), header.act_arg_tvs.len());
    state
        .effect_args
        .insert(header.effect_path.clone(), header.act_args.clone());

    let alias_owner = state.ctx.modules.node(mid).parent.unwrap_or(mid);

    let saved_module = state.ctx.enter_or_create_module(header.name.clone());
    state.mark_companion_module(state.ctx.current_module);
    {
        let state = &mut *state;
        state.insert_type_alias_with_visibility(
            state.ctx.current_module,
            header.name.clone(),
            def,
            Visibility::My,
        );
        state.insert_type_alias_with_visibility(
            alias_owner,
            header.name.clone(),
            def,
            header.visibility,
        );
        state.insert_module_alias_with_visibility(
            alias_owner,
            header.name.clone(),
            state.ctx.current_module,
            header.visibility,
        );
        if let Some(body) = act_decl_body(node) {
            super::preregister_act_body(
                state,
                &body,
                header.effect_path,
                &header.act_scope,
                &header.act_arg_tvs,
                None,
            );
        }
    }
    state.ctx.leave_module(saved_module);
}

struct ActDeclHeader {
    name: crate::symbols::Name,
    visibility: Visibility,
    effect_path: Path,
    act_scope: std::collections::HashMap<String, crate::ids::TypeVar>,
    act_arg_tvs: Vec<crate::ids::TypeVar>,
    act_args: Vec<(crate::ids::TypeVar, crate::ids::TypeVar)>,
}

fn act_decl_header(state: &mut LowerState, node: &SyntaxNode) -> Option<ActDeclHeader> {
    let Some(name) = super::super::ident_or_sigil_name(node) else {
        return None;
    };
    let visibility = act_visibility(node);
    let mut effect_segments = state.ctx.current_module_path().segments;
    effect_segments.push(name.clone());
    let effect_path = Path {
        segments: effect_segments,
    };
    let (act_scope, act_arg_tvs, act_args) =
        if let Some(existing_args) = state.effect_args.get(&effect_path).cloned() {
            let act_arg_tvs = existing_args
                .iter()
                .map(|(pos, _)| *pos)
                .collect::<Vec<_>>();
            let act_scope = crate::lower::signature::act_type_param_names(node)
                .into_iter()
                .zip(act_arg_tvs.iter().copied())
                .collect::<std::collections::HashMap<_, _>>();
            (act_scope, act_arg_tvs, existing_args)
        } else {
            let act_scope = super::super::collect_act_type_scope(state, node);
            let act_arg_tvs = crate::lower::signature::ordered_act_type_vars(node, &act_scope);
            let act_args = act_arg_tvs
                .iter()
                .copied()
                .map(|tv| (tv, tv))
                .collect::<Vec<_>>();
            (act_scope, act_arg_tvs, act_args)
        };
    Some(ActDeclHeader {
        name,
        visibility,
        effect_path,
        act_scope,
        act_arg_tvs,
        act_args,
    })
}

fn act_decl_body(node: &SyntaxNode) -> Option<SyntaxNode> {
    super::super::child_node(node, SyntaxKind::IndentBlock)
        .or_else(|| super::super::child_node(node, SyntaxKind::BraceGroup))
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
