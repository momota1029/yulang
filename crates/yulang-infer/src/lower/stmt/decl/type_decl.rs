use std::collections::HashMap;

use yulang_parser::lex::SyntaxKind;

use crate::ids::{DefId, TypeVar};
use crate::lower::{LowerState, SyntaxNode};
use crate::symbols::{Name, Path};
use crate::types::{Neg, Pos};

/// `type ref 'e 'a with: ...` を lowering する。
///
/// `struct self:` は外側の nominal type 自体のフィールド定義として扱い、
/// companion module には `ref::field` と `ref::method` を登録する。
pub(crate) fn lower_type_decl(state: &mut LowerState, node: &SyntaxNode) {
    let Some(name) = super::super::ident_name(node) else {
        return;
    };
    let type_path = companion_type_path(state, &name);
    let type_param_names = crate::lower::signature::act_type_param_names(node);
    let type_scope = crate::lower::signature::fresh_type_scope(state, &type_param_names);
    let type_arg_tvs = crate::lower::signature::ordered_type_vars(&type_param_names, &type_scope);
    let self_struct = type_decl_self_struct(node);
    let self_enum = type_decl_self_enum(node);

    if self_struct.is_none() && self_enum.is_none() {
        if state
            .ctx
            .modules
            .node(state.ctx.current_module)
            .types
            .contains_key(&name)
        {
            let saved = state.ctx.enter_module(name);
            state.mark_companion_module(state.ctx.current_module);
            lower_type_with_bindings(state, node, &type_path, &type_param_names);
            state.ctx.leave_module(saved);
            return;
        }
    }

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
    if let Some(self_struct) = self_struct {
        lower_self_struct_fields(
            state,
            &self_struct,
            &type_path,
            &type_scope,
            &type_arg_tvs,
            &type_param_names,
            ctor_def,
            ctor_tv,
        );
    }
    lower_type_with_bindings(state, node, &type_path, &type_param_names);
    state.ctx.leave_module(saved);
}

fn companion_type_path(state: &LowerState, name: &Name) -> Path {
    let mut type_segments = state.ctx.current_module_path().segments;
    type_segments.push(name.clone());
    Path {
        segments: type_segments,
    }
}

fn type_decl_self_struct(node: &SyntaxNode) -> Option<SyntaxNode> {
    node.children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
        .into_iter()
        .flat_map(|block| block.children())
        .find(|child| {
            child.kind() == SyntaxKind::StructDecl
                && super::super::ident_name(child) == Some(Name("self".to_string()))
        })
}

fn type_decl_self_enum(node: &SyntaxNode) -> Option<SyntaxNode> {
    node.children()
        .find(|child| {
            matches!(
                child.kind(),
                SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
            )
        })
        .into_iter()
        .flat_map(|block| block.children())
        .find(|child| {
            child.kind() == SyntaxKind::EnumDecl
                && super::super::ident_name(child) == Some(Name("self".to_string()))
        })
}

fn lower_self_struct_fields(
    state: &mut LowerState,
    struct_node: &SyntaxNode,
    type_path: &Path,
    type_scope: &HashMap<String, TypeVar>,
    type_arg_tvs: &[TypeVar],
    type_param_names: &[String],
    ctor_def: DefId,
    ctor_tv: TypeVar,
) {
    let mut fields = Vec::new();
    let mut field_defs = Vec::new();
    for field in super::super::child_nodes(struct_node, SyntaxKind::StructField) {
        let Some(field_name) = super::super::ident_name(&field) else {
            continue;
        };
        let Some((field_pos, field_neg)) =
            super::super::lower_struct_field_type(state, &field, type_scope)
        else {
            continue;
        };
        fields.push((field_name.clone(), field_pos.clone(), field_neg.clone()));

        let accessor_scope = crate::lower::signature::fresh_type_scope(state, type_param_names);
        let accessor_arg_tvs =
            crate::lower::signature::ordered_type_vars(type_param_names, &accessor_scope);
        let Some((accessor_field_pos, _)) =
            super::super::lower_struct_field_type(state, &field, &accessor_scope)
        else {
            continue;
        };

        let field_def = state.fresh_def();
        let field_tv = state.fresh_tv();
        state.register_def_tv(field_def, field_tv);
        let companion_mid = state.ctx.current_module;
        state.insert_value(companion_mid, field_name.clone(), field_def);
        state
            .infer
            .register_type_field(type_path.clone(), field_name.clone(), field_def);
        field_defs.push((field_name.clone(), field_def, field_tv));
        state.infer.constrain(
            state.pos_fun(
                state.neg_con(
                    type_path.clone(),
                    super::super::invariant_args(&accessor_arg_tvs),
                ),
                state.neg_row(vec![], Neg::Top),
                state.pos_row(vec![], Pos::Bot),
                accessor_field_pos,
            ),
            Neg::Var(field_tv),
        );
        state.infer.store_frozen_scheme(
            field_def,
            crate::scheme::freeze_type_var(&state.infer, field_tv),
        );
        state.infer.mark_frozen_ref_committed(field_def);
    }
    state.infer.register_type_field_set(
        type_path.clone(),
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
                type_path.clone(),
                super::super::invariant_args(type_arg_tvs),
            ),
        ),
        Neg::Var(ctor_tv),
    );
    state.infer.store_frozen_scheme(
        ctor_def,
        crate::scheme::freeze_type_var(&state.infer, ctor_tv),
    );
    state.infer.mark_frozen_ref_committed(ctor_def);

    let ctor_body = super::super::synthetic_struct_constructor_body(state, ctor_def);
    state.principal_bodies.insert(ctor_def, ctor_body.clone());
    state
        .infer
        .constrain(Pos::Var(ctor_body.tv), Neg::Var(ctor_tv));
    state
        .infer
        .constrain(Pos::Var(ctor_tv), Neg::Var(ctor_body.tv));

    for (field_name, field_def, field_tv) in field_defs {
        let body = super::super::synthetic_struct_field_body(
            state,
            type_path,
            type_arg_tvs,
            &fields,
            field_def,
            &field_name,
        );
        state.principal_bodies.insert(field_def, body.clone());
        state.infer.constrain(Pos::Var(body.tv), Neg::Var(field_tv));
        state.infer.constrain(Pos::Var(field_tv), Neg::Var(body.tv));
    }
}

pub(crate) fn lower_type_with_bindings(
    state: &mut LowerState,
    node: &SyntaxNode,
    type_path: &Path,
    type_param_names: &[String],
) {
    let Some(with_block) = super::super::child_node(node, SyntaxKind::IndentBlock)
        .or_else(|| super::super::child_node(node, SyntaxKind::BraceGroup))
    else {
        return;
    };

    for item in with_block.children() {
        match item.kind() {
            SyntaxKind::Binding => {
                let method_scope =
                    crate::lower::signature::fresh_type_scope(state, type_param_names);
                let method_arg_tvs =
                    crate::lower::signature::ordered_type_vars(type_param_names, &method_scope);
                super::super::lower_struct_with_binding(state, &item, type_path, &method_arg_tvs);
            }
            SyntaxKind::ImplDecl => {
                super::lower_attached_impl_decl(state, &item, type_path, type_param_names);
            }
            SyntaxKind::CastDecl => {
                super::lower_cast_decl(state, &item);
            }
            _ => {}
        }
    }
}
