use rowan::TextRange;
use yulang_parser::lex::SyntaxKind;

use crate::lower::role::{ErrorThrowVariant, ErrorUpSource};
use crate::lower::signature::{SigType, SigVar, act_type_param_names, fresh_type_scope};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path, Visibility};

/// `error E: ...` を enum + same-name act operation として lowering する。
///
/// 最初の sugar は同名 constructor / operation を安定して生成することに絞る。
/// `from` と generated `raise` は、衝突規則と handler 展開が固まってから足す。
pub(crate) fn lower_error_decl(state: &mut LowerState, node: &SyntaxNode) {
    let Some(name) = super::super::ident_name(node) else {
        return;
    };
    let visibility = error_visibility(node);
    let mut effect_segments = state.ctx.current_module_path().segments;
    effect_segments.push(name.clone());
    let effect_path = Path {
        segments: effect_segments,
    };

    super::lower_enum_decl(state, node);

    let act_scope = fresh_type_scope(state, &act_type_param_names(node));
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
    state.effect_args.insert(effect_path.clone(), act_args);

    let alias_owner = state.ctx.modules.node(mid).parent.unwrap_or(mid);
    let saved_module = state.ctx.enter_or_create_module(name.clone());
    state.mark_companion_module(state.ctx.current_module);
    state.insert_type_alias_with_visibility(alias_owner, name.clone(), def, visibility);
    state.insert_module_alias_with_visibility(
        alias_owner,
        name,
        state.ctx.current_module,
        visibility,
    );

    let mut throw_variants = Vec::new();
    let mut up_sources = Vec::new();
    for variant in super::super::child_nodes(node, SyntaxKind::EnumVariant) {
        let Some(variant_name) = super::super::ident_name(&variant) else {
            continue;
        };
        let payload_sig = super::enum_variant_payload_sig(&variant);
        let sig = error_operation_sig(&variant);
        let Some(operation_def) = super::super::register_act_operation_sig(
            state,
            variant_name.clone(),
            visibility,
            effect_path.clone(),
            &act_scope,
            &act_arg_tvs,
            sig,
        ) else {
            continue;
        };
        let Some(constructor_def) = state.same_path_value_def_for_effect_op(operation_def) else {
            continue;
        };
        throw_variants.push(ErrorThrowVariant {
            payload_sig: payload_sig.clone(),
            constructor_def,
            operation_def,
        });
        if enum_variant_has_from_marker(&variant)
            && let Some(source_sig) = payload_sig
        {
            up_sources.push(ErrorUpSource {
                source_sig,
                target_operation_def: operation_def,
                target_constructor_def: constructor_def,
                payload_constructor_defs: Vec::new(),
            });
        }
    }
    state
        .error_throw_variants
        .insert(effect_path.clone(), throw_variants.clone());
    let error_sig = error_type_sig(&effect_path, &act_type_param_names(node), node.text_range());
    let expanded_up_sources = crate::lower::role::expand_error_up_sources(state, &up_sources);
    state
        .error_up_sources
        .insert(effect_path.clone(), expanded_up_sources.clone());
    crate::lower::role::lower_synthetic_error_wrap(
        state,
        &error_sig,
        &throw_variants,
        &expanded_up_sources,
        visibility,
    );
    crate::lower::role::lower_synthetic_error_up(
        state,
        &error_sig,
        &expanded_up_sources,
        visibility,
    );
    state.ctx.leave_module(saved_module);
    crate::lower::role::lower_synthetic_error_throw(state, &error_sig, throw_variants);
}

fn error_operation_sig(variant: &SyntaxNode) -> SigType {
    let span = variant.text_range();
    let ret = never_sig(span);
    let Some(payload) = super::enum_variant_payload_sig(variant) else {
        return ret;
    };
    SigType::Fun {
        arg: Box::new(payload),
        ret_eff: None,
        ret: Box::new(ret),
        span,
    }
}

fn never_sig(span: TextRange) -> SigType {
    SigType::Prim {
        path: Path {
            segments: vec![Name("never".to_string())],
        },
        span,
    }
}

fn error_type_sig(effect_path: &Path, type_param_names: &[String], span: TextRange) -> SigType {
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
            path: effect_path.clone(),
            span,
        }
    } else {
        SigType::Apply {
            path: effect_path.clone(),
            args,
            span,
        }
    }
}

fn error_visibility(node: &SyntaxNode) -> Visibility {
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

fn enum_variant_has_from_marker(variant_node: &SyntaxNode) -> bool {
    let mut seen_name = false;
    for token in variant_node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
    {
        if token.kind() != SyntaxKind::Ident {
            continue;
        }
        if !seen_name {
            seen_name = true;
            continue;
        }
        return token.text() == "from";
    }
    false
}
