use yulang_parser::lex::SyntaxKind;

use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::Path;
use crate::types::{Neg, Pos};

/// `struct point { x: int, y: int }` を lowering する。
///
/// - 型名前空間に struct 名を登録
/// - コンストラクタ（`point { x, y }`）を値名前空間に登録
/// - フィールドアクセサ（`point::x`, `point::y`）を companion module に登録
pub(crate) fn lower_struct_decl(state: &mut LowerState, node: &SyntaxNode) {
    let Some(name) = super::super::ident_name(node) else {
        return;
    };
    let mut struct_segments = state.ctx.current_module_path().segments;
    struct_segments.push(name.clone());
    let struct_path = Path {
        segments: struct_segments,
    };
    let type_scope = super::super::collect_act_type_scope(state, node);
    let type_param_names = crate::lower::signature::act_type_param_names(node);
    let type_arg_tvs = crate::lower::signature::ordered_type_vars(&type_param_names, &type_scope);

    let type_def = state.fresh_def();
    let type_tv = state.fresh_tv();
    state.register_def_tv(type_def, type_tv);
    let mid = state.ctx.current_module;
    state.insert_type(mid, name.clone(), type_def);

    let ctor_def = state.fresh_def();
    let ctor_tv = state.fresh_tv();
    state.register_def_tv(ctor_def, ctor_tv);
    state.insert_value(mid, name.clone(), ctor_def);

    let saved = state.ctx.enter_module(name);
    state.mark_companion_module(state.ctx.current_module);

    let mut fields = Vec::new();
    let mut field_defs = Vec::new();
    for field in super::super::child_nodes(node, SyntaxKind::StructField) {
        let Some(field_name) = super::super::ident_name(&field) else {
            continue;
        };
        let Some((field_pos, field_neg)) =
            super::super::lower_struct_field_type(state, &field, &type_scope)
        else {
            continue;
        };
        fields.push((field_name.clone(), field_pos.clone(), field_neg.clone()));

        let field_def = state.fresh_def();
        let field_tv = state.fresh_tv();
        state.register_def_tv(field_def, field_tv);
        let companion_mid = state.ctx.current_module;
        state.insert_value(companion_mid, field_name.clone(), field_def);
        state
            .infer
            .register_type_field(struct_path.clone(), field_name.clone(), field_def);
        field_defs.push((field_name.clone(), field_def, field_tv));
        state.infer.constrain(
            state.pos_fun(
                state.neg_con(
                    struct_path.clone(),
                    super::super::invariant_args(&type_arg_tvs),
                ),
                state.neg_row(vec![], Neg::Top),
                state.pos_row(vec![], Pos::Bot),
                field_pos,
            ),
            Neg::Var(field_tv),
        );
    }
    state.infer.register_type_field_set(
        struct_path.clone(),
        ctor_def,
        field_defs
            .iter()
            .map(|(name, def, _)| (name.clone(), *def))
            .collect(),
    );

    let ctor_record = fields
        .iter()
        .map(|(name, _, neg)| crate::types::RecordField::required(name.clone(), neg.clone()))
        .collect::<Vec<_>>();
    state.infer.constrain(
        state.pos_fun(
            state.neg_record(ctor_record),
            state.neg_row(vec![], Neg::Top),
            state.pos_row(vec![], Pos::Bot),
            state.pos_con(
                struct_path.clone(),
                super::super::invariant_args(&type_arg_tvs),
            ),
        ),
        Neg::Var(ctor_tv),
    );
    let ctor_body = super::super::synthetic_struct_constructor_body(state, ctor_def);
    state.principal_bodies.insert(ctor_def, ctor_body.clone());
    state
        .infer
        .constrain(Pos::Var(ctor_body.tv), Neg::Var(ctor_tv));
    state
        .infer
        .constrain(Pos::Var(ctor_tv), Neg::Var(ctor_body.tv));
    state.infer.store_frozen_scheme(
        ctor_def,
        crate::scheme::freeze_type_var(&state.infer, ctor_tv),
    );
    state.infer.mark_frozen_ref_committed(ctor_def);

    for (field_name, field_def, field_tv) in field_defs {
        let body = super::super::synthetic_struct_field_body(
            state,
            &struct_path,
            &type_arg_tvs,
            &fields,
            field_def,
            &field_name,
        );
        state.principal_bodies.insert(field_def, body.clone());
        state.infer.constrain(Pos::Var(body.tv), Neg::Var(field_tv));
        state.infer.constrain(Pos::Var(field_tv), Neg::Var(body.tv));
        state.infer.store_frozen_scheme(
            field_def,
            crate::scheme::freeze_type_var(&state.infer, field_tv),
        );
        state.infer.mark_frozen_ref_committed(field_def);
    }

    super::super::lower_struct_with_bindings(
        state,
        node,
        &struct_path,
        &type_param_names,
        &type_arg_tvs,
    );
    state.ctx.leave_module(saved);
}
