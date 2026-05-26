use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use crate::ast::expr::{ExprKind, PatKind, TypedExpr, TypedPat};
use crate::ids::{DefId, TypeVar};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

/// `enum opt 'a = nil | just 'a with: ...` を lowering する。
///
/// - 型名前空間に enum 名を登録
/// - companion module に variant constructor を登録
/// - `with:` の binding は nominal type method として companion module に登録
pub(crate) fn lower_enum_decl(state: &mut LowerState, node: &SyntaxNode) {
    let Some(name) = super::super::ident_name(node) else {
        return;
    };
    let mut enum_segments = state.ctx.current_module_path().segments;
    enum_segments.push(name.clone());
    let enum_path = Path {
        segments: enum_segments,
    };
    let type_param_names = crate::lower::signature::act_type_param_names(node);
    let type_scope = crate::lower::signature::fresh_type_scope(state, &type_param_names);
    let type_arg_tvs = crate::lower::signature::ordered_type_vars(&type_param_names, &type_scope);

    let type_def = state.fresh_def();
    let type_tv = state.fresh_tv();
    state.register_def_tv(type_def, type_tv);
    let mid = state.ctx.current_module;
    state.insert_type(mid, name.clone(), type_def);

    let saved = state.ctx.enter_module(name);
    state.mark_companion_module(state.ctx.current_module);
    for variant in super::super::child_nodes(node, SyntaxKind::EnumVariant) {
        lower_enum_variant(
            state,
            &variant,
            &enum_path,
            &type_param_names,
            &type_scope,
            &type_arg_tvs,
        );
    }
    super::super::lower_type_with_bindings(state, node, &enum_path, &type_param_names);
    state.ctx.leave_module(saved);
}

fn lower_enum_variant(
    state: &mut LowerState,
    variant_node: &SyntaxNode,
    enum_path: &Path,
    type_param_names: &[String],
    type_scope: &HashMap<String, TypeVar>,
    type_arg_tvs: &[TypeVar],
) {
    let Some(variant_name) = super::super::ident_name(variant_node) else {
        return;
    };

    let ctor_def = state.fresh_def();
    let ctor_tv = state.fresh_tv();
    state.register_def_tv(ctor_def, ctor_tv);
    state.insert_value(state.ctx.current_module, variant_name.clone(), ctor_def);
    state
        .enum_variant_tags
        .insert(ctor_def, variant_name.clone());
    state.enum_variant_patterns.insert(
        ctor_def,
        crate::lower::EnumVariantPatternShape {
            enum_path: enum_path.clone(),
            payload: crate::lower::EnumVariantPatternPayload::Source {
                type_param_names: type_param_names.to_vec(),
                payload_sig: enum_variant_payload_sig(variant_node),
            },
        },
    );

    let enum_pos = state.pos_con(
        enum_path.clone(),
        super::super::invariant_args(type_arg_tvs),
    );
    let enum_neg = state.neg_con(
        enum_path.clone(),
        super::super::invariant_args(type_arg_tvs),
    );
    let payload_sigs = enum_variant_payload_sigs(variant_node);
    let frozen_ctor_scheme = if !payload_sigs.is_empty() {
        let mut neg_scope = type_scope.clone();
        let fun_pos = enum_constructor_pos_for_payloads(
            state,
            &payload_sigs,
            &mut neg_scope,
            enum_pos.clone(),
        );
        crate::scheme::freeze_pos_scheme(&state.infer, state.infer.alloc_pos(fun_pos))
    } else {
        crate::scheme::freeze_pos_scheme(&state.infer, state.infer.alloc_pos(enum_pos.clone()))
    };

    let body = if !payload_sigs.is_empty() {
        let mut pos_scope = type_scope.clone();
        let mut neg_scope = type_scope.clone();
        let payloads = payload_sigs
            .iter()
            .map(|sig| {
                (
                    crate::lower::signature::lower_pure_sig_type(state, sig, &mut pos_scope),
                    crate::lower::signature::lower_pure_sig_neg_type(state, sig, &mut neg_scope),
                )
            })
            .collect::<Vec<_>>();
        let mut neg_scope_for_ctor = type_scope.clone();
        let ctor_pos = enum_constructor_pos_for_payloads(
            state,
            &payload_sigs,
            &mut neg_scope_for_ctor,
            enum_pos.clone(),
        );
        state.infer.constrain(ctor_pos, Neg::Var(ctor_tv));
        synthetic_enum_payload_constructor_body(
            state,
            ctor_def,
            &variant_name,
            payloads,
            enum_pos,
            enum_neg,
        )
    } else {
        state.infer.constrain(enum_pos.clone(), Neg::Var(ctor_tv));
        state.infer.constrain(Pos::Var(ctor_tv), enum_neg.clone());
        synthetic_enum_nullary_constructor_body(state, &variant_name, enum_pos, enum_neg)
    };

    state.insert_principal_body(ctor_def, body.clone());
    state.infer.constrain(Pos::Var(body.tv), Neg::Var(ctor_tv));
    state.infer.constrain(Pos::Var(ctor_tv), Neg::Var(body.tv));
    state
        .infer
        .store_frozen_scheme(ctor_def, frozen_ctor_scheme);

    if enum_variant_has_from_marker(variant_node) {
        if let Some(source_sig) = enum_variant_payload_sig(variant_node) {
            let target_sig =
                enum_target_sig(enum_path, type_param_names, variant_node.text_range());
            crate::lower::role::lower_synthetic_variant_cast(
                state,
                &source_sig,
                &target_sig,
                &variant_name,
            );
        }
    }
}

pub(crate) fn enum_variant_payload_sig(
    variant_node: &SyntaxNode,
) -> Option<crate::lower::signature::SigType> {
    let payloads = enum_variant_payload_sigs(variant_node);
    match payloads.len() {
        0 => None,
        1 => payloads.into_iter().next(),
        _ => Some(crate::lower::signature::SigType::Tuple {
            items: payloads,
            span: variant_node.text_range(),
        }),
    }
}

fn enum_variant_payload_sigs(variant_node: &SyntaxNode) -> Vec<crate::lower::signature::SigType> {
    let type_items = super::super::child_nodes(variant_node, SyntaxKind::TypeExpr)
        .into_iter()
        .filter_map(|type_expr| crate::lower::signature::parse_sig_type_expr(&type_expr))
        .collect::<Vec<_>>();
    if !type_items.is_empty() {
        return type_items;
    }

    let Some(tuple_items) = super::super::child_nodes(variant_node, SyntaxKind::StructField)
        .into_iter()
        .filter_map(|field| super::super::child_node(&field, SyntaxKind::TypeExpr))
        .map(|type_expr| crate::lower::signature::parse_sig_type_expr(&type_expr))
        .collect::<Option<Vec<_>>>()
    else {
        return Vec::new();
    };

    if tuple_items.is_empty() {
        Vec::new()
    } else {
        vec![crate::lower::signature::SigType::Tuple {
            items: tuple_items,
            span: variant_node.text_range(),
        }]
    }
}

fn enum_constructor_pos_for_payloads(
    state: &mut LowerState,
    payload_sigs: &[crate::lower::signature::SigType],
    scope: &mut HashMap<String, TypeVar>,
    ret: Pos,
) -> Pos {
    payload_sigs.iter().rev().fold(ret, |ret, sig| {
        let payload_neg = crate::lower::signature::lower_pure_sig_neg_type(state, sig, scope);
        state.pos_fun(
            payload_neg,
            state.neg_row(vec![], Neg::Top),
            state.pos_row(vec![], Pos::Bot),
            ret,
        )
    })
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

fn enum_target_sig(
    enum_path: &Path,
    type_param_names: &[String],
    span: rowan::TextRange,
) -> crate::lower::signature::SigType {
    let args = type_param_names
        .iter()
        .map(|name| {
            crate::lower::signature::SigType::Var(crate::lower::signature::SigVar {
                name: name.clone(),
                span,
            })
        })
        .collect::<Vec<_>>();
    if args.is_empty() {
        crate::lower::signature::SigType::Prim {
            path: enum_path.clone(),
            span,
        }
    } else {
        crate::lower::signature::SigType::Apply {
            path: enum_path.clone(),
            args,
            span,
        }
    }
}

fn synthetic_enum_nullary_constructor_body(
    state: &mut LowerState,
    tag: &Name,
    enum_pos: Pos,
    enum_neg: Neg,
) -> TypedExpr {
    let variant_tv = state.fresh_tv();
    let ret_tv = state.fresh_tv();
    let variant = TypedExpr {
        tv: variant_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::PolyVariant(
            tag.clone(),
            Vec::new(),
            crate::ast::expr::PolyVariantOrigin::Constructor,
        ),
    };
    state.infer.constrain(
        state.pos_variant(vec![(tag.clone(), Vec::new())]),
        Neg::Var(variant_tv),
    );
    state.infer.constrain(
        Pos::Var(variant_tv),
        Neg::PolyVariant(vec![(tag.clone(), Vec::new())]),
    );
    state.infer.constrain(enum_pos, Neg::Var(ret_tv));
    state.infer.constrain(Pos::Var(ret_tv), enum_neg);
    let body_eff = state.fresh_exact_pure_eff_tv();
    state.representation_coerce(variant_tv, ret_tv, body_eff, variant)
}

fn synthetic_enum_payload_constructor_body(
    state: &mut LowerState,
    ctor_def: DefId,
    tag: &Name,
    payload_types: Vec<(Pos, Neg)>,
    enum_pos: Pos,
    enum_neg: Neg,
) -> TypedExpr {
    let variant_tv = state.fresh_tv();
    let ret_tv = state.fresh_tv();
    let mut payload_tvs = Vec::with_capacity(payload_types.len());
    let mut payload_exprs = Vec::with_capacity(payload_types.len());
    let mut arg_pats = Vec::with_capacity(payload_types.len());

    for (index, (payload_pos, payload_neg)) in payload_types.into_iter().enumerate() {
        let arg_def = state.fresh_def();
        let arg_tv = state.fresh_tv();
        let payload_tv = state.fresh_tv();
        let arg_name = if index == 0 {
            Name("value".to_string())
        } else {
            Name(format!("value{index}"))
        };
        state.register_def_tv(arg_def, arg_tv);
        state.register_def_name(arg_def, arg_name.clone());
        state.register_def_owner(arg_def, ctor_def);
        state.infer.constrain(payload_pos, Neg::Var(payload_tv));
        state.infer.constrain(Pos::Var(payload_tv), payload_neg);
        state
            .infer
            .constrain(Pos::Var(arg_tv), Neg::Var(payload_tv));
        state
            .infer
            .constrain(Pos::Var(payload_tv), Neg::Var(arg_tv));

        let payload_coerce_eff = state.fresh_exact_pure_eff_tv();
        let arg_expr_eff = state.fresh_exact_pure_eff_tv();
        payload_exprs.push(state.representation_coerce(
            arg_tv,
            payload_tv,
            payload_coerce_eff,
            TypedExpr {
                tv: arg_tv,
                eff: arg_expr_eff,
                kind: ExprKind::Var(arg_def),
            },
        ));
        payload_tvs.push(payload_tv);

        let arg_eff_tv = state.fresh_exact_pure_eff_tv();
        arg_pats.push(super::super::ArgPatInfo {
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
            ann_non_generic_tvs: Vec::new(),
            unit_arg: false,
        });
    }

    let variant = TypedExpr {
        tv: variant_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::PolyVariant(
            tag.clone(),
            payload_exprs,
            crate::ast::expr::PolyVariantOrigin::Constructor,
        ),
    };
    state.infer.constrain(
        state.pos_variant(vec![(
            tag.clone(),
            payload_tvs.iter().copied().map(Pos::Var).collect(),
        )]),
        Neg::Var(variant_tv),
    );
    state.infer.constrain(
        Pos::Var(variant_tv),
        Neg::PolyVariant(vec![(
            tag.clone(),
            payload_tvs
                .iter()
                .copied()
                .map(|payload_tv| state.infer.alloc_neg(Neg::Var(payload_tv)))
                .collect(),
        )]),
    );
    state.infer.constrain(enum_pos, Neg::Var(ret_tv));
    state.infer.constrain(Pos::Var(ret_tv), enum_neg);

    let body_eff = state.fresh_exact_pure_eff_tv();
    let body = state.representation_coerce(variant_tv, ret_tv, body_eff, variant);
    super::super::wrap_header_lambdas(state, body, arg_pats)
}
