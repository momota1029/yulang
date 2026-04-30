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
            type_param_names: type_param_names.to_vec(),
            payload_sig: enum_variant_payload_sig(variant_node),
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
    let frozen_ctor_scheme = if let Some(sig) = enum_variant_payload_sig(variant_node) {
        let mut neg_scope = type_scope.clone();
        let payload_neg =
            crate::lower::signature::lower_pure_sig_neg_type(state, &sig, &mut neg_scope);
        let fun_pos = state.pos_fun(
            payload_neg,
            state.neg_row(vec![], Neg::Top),
            state.pos_row(vec![], Pos::Bot),
            enum_pos.clone(),
        );
        crate::scheme::freeze_pos_scheme(&state.infer, state.infer.alloc_pos(fun_pos))
    } else {
        crate::scheme::freeze_pos_scheme(&state.infer, state.infer.alloc_pos(enum_pos.clone()))
    };

    let body = if let Some(sig) = enum_variant_payload_sig(variant_node) {
        let mut pos_scope = type_scope.clone();
        let mut neg_scope = type_scope.clone();
        let payload_pos = crate::lower::signature::lower_pure_sig_type(state, &sig, &mut pos_scope);
        let payload_neg =
            crate::lower::signature::lower_pure_sig_neg_type(state, &sig, &mut neg_scope);
        state.infer.constrain(
            state.pos_fun(
                payload_neg.clone(),
                state.neg_row(vec![], Neg::Top),
                state.pos_row(vec![], Pos::Bot),
                enum_pos.clone(),
            ),
            Neg::Var(ctor_tv),
        );
        synthetic_enum_unary_constructor_body(
            state,
            ctor_def,
            &variant_name,
            payload_pos,
            payload_neg,
            enum_pos,
            enum_neg,
        )
    } else {
        state.infer.constrain(enum_pos.clone(), Neg::Var(ctor_tv));
        state.infer.constrain(Pos::Var(ctor_tv), enum_neg.clone());
        synthetic_enum_nullary_constructor_body(state, &variant_name, enum_pos, enum_neg)
    };

    state.principal_bodies.insert(ctor_def, body.clone());
    state.infer.constrain(Pos::Var(body.tv), Neg::Var(ctor_tv));
    state.infer.constrain(Pos::Var(ctor_tv), Neg::Var(body.tv));
    state
        .infer
        .store_frozen_scheme(ctor_def, frozen_ctor_scheme);
}

fn enum_variant_payload_sig(variant_node: &SyntaxNode) -> Option<crate::lower::signature::SigType> {
    if let Some(type_expr) = super::super::child_node(variant_node, SyntaxKind::TypeExpr) {
        return crate::lower::signature::parse_sig_type_expr(&type_expr);
    }

    let tuple_items = super::super::child_nodes(variant_node, SyntaxKind::StructField)
        .into_iter()
        .filter_map(|field| super::super::child_node(&field, SyntaxKind::TypeExpr))
        .map(|type_expr| crate::lower::signature::parse_sig_type_expr(&type_expr))
        .collect::<Option<Vec<_>>>()?;

    if tuple_items.is_empty() {
        None
    } else {
        Some(crate::lower::signature::SigType::Tuple {
            items: tuple_items,
            span: variant_node.text_range(),
        })
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
        kind: ExprKind::PolyVariant(tag.clone(), Vec::new()),
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
    TypedExpr {
        tv: ret_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::Coerce {
            actual_tv: variant_tv,
            expected_tv: ret_tv,
            expr: Box::new(variant),
        },
    }
}

fn synthetic_enum_unary_constructor_body(
    state: &mut LowerState,
    ctor_def: DefId,
    tag: &Name,
    payload_pos: Pos,
    payload_neg: Neg,
    enum_pos: Pos,
    enum_neg: Neg,
) -> TypedExpr {
    let arg_def = state.fresh_def();
    let arg_tv = state.fresh_tv();
    let payload_tv = state.fresh_tv();
    let variant_tv = state.fresh_tv();
    let ret_tv = state.fresh_tv();
    let arg_name = Name("value".to_string());
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

    let variant = TypedExpr {
        tv: variant_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::PolyVariant(
            tag.clone(),
            vec![TypedExpr {
                tv: payload_tv,
                eff: state.fresh_exact_pure_eff_tv(),
                kind: ExprKind::Coerce {
                    actual_tv: arg_tv,
                    expected_tv: payload_tv,
                    expr: Box::new(TypedExpr {
                        tv: arg_tv,
                        eff: state.fresh_exact_pure_eff_tv(),
                        kind: ExprKind::Var(arg_def),
                    }),
                },
            }],
        ),
    };
    state.infer.constrain(
        state.pos_variant(vec![(tag.clone(), vec![Pos::Var(payload_tv)])]),
        Neg::Var(variant_tv),
    );
    state.infer.constrain(
        Pos::Var(variant_tv),
        Neg::PolyVariant(vec![(
            tag.clone(),
            vec![state.infer.alloc_neg(Neg::Var(payload_tv))],
        )]),
    );
    state.infer.constrain(enum_pos, Neg::Var(ret_tv));
    state.infer.constrain(Pos::Var(ret_tv), enum_neg);

    let body = TypedExpr {
        tv: ret_tv,
        eff: state.fresh_exact_pure_eff_tv(),
        kind: ExprKind::Coerce {
            actual_tv: variant_tv,
            expected_tv: ret_tv,
            expr: Box::new(variant),
        },
    };
    let arg_eff_tv = state.fresh_exact_pure_eff_tv();
    super::super::wrap_header_lambdas(
        state,
        body,
        vec![super::super::ArgPatInfo {
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
    )
}
