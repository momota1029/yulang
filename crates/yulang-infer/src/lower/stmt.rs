//! 文・宣言の lowering。
//!
//! このモジュールがやること（stmt レベル）:
//! - ブロック内の全 Binding を先行登録（相互再帰対応）
//! - Binding / UseDecl / ModDecl / ActDecl / StructDecl を lowering
//! - モジュールテーブル登録・DefId/TypeVar 発行・SCC 登録
use yulang_parser::lex::SyntaxKind;

use super::ann::{LoweredEffAnn, configure_arg_effect_from_ann};
use super::{LowerState, SyntaxNode};
use crate::ast::expr::TypedBlock;
use crate::symbols::Path;

/// Root ノードを lowering して TypedBlock を返す。
pub fn lower_root(state: &mut LowerState, root: &SyntaxNode) -> TypedBlock {
    assert_eq!(root.kind(), SyntaxKind::Root);
    let block = lower_block(state, root);
    state.record_top_level_block(
        Path {
            segments: Vec::new(),
        },
        block.clone(),
    );
    finish_lowering(state);
    block
}

/// Root ノードを指定 module path の中へ lowering する。
/// 複数ファイル lowering では各 file をこの関数で流し、最後に `finish_lowering` を呼ぶ。
pub fn lower_root_in_module(
    state: &mut LowerState,
    root: &SyntaxNode,
    module_path: Path,
) -> TypedBlock {
    assert_eq!(root.kind(), SyntaxKind::Root);
    let saved = state.ctx.enter_module_path(&module_path);
    let block = lower_block(state, root);
    state.ctx.leave_module_path(saved);
    state.record_top_level_block(module_path, block.clone());
    block
}

pub fn finish_lowering(state: &mut LowerState) {
    state.refresh_selection_environment();
}

mod act;
mod binding;
mod control;
mod decl;
mod patterns;
mod structs;
mod support;
mod synthetic_act;
mod var;

pub(crate) use act::ActCopy;
use act::lower_act_decl;
pub(crate) use act::{
    lower_act_body, lower_act_copy_body, transform_copied_frozen_scheme,
    transform_copied_principal_body,
};
pub(super) use binding::preregister_binding_as_module_value;
pub(crate) use binding::{
    ArgPatInfo, HeaderArg, binding_sig_var_names, collect_header_args,
    connect_pattern_sig_annotation, lower_binding_body, lower_binding_with_type_scope,
    make_arg_pat_info, preregister_binding, wrap_header_lambdas,
};
use binding::{
    connect_binding_type_annotation, direct_binding_name, extract_binding_lhs, lower_binding,
    preconstrain_recursive_binding_header_shape,
};
pub(super) use control::collect_block_items;
pub use control::lower_block;
pub(crate) use control::{lower_block_expr_from_items, lower_scoped_with_block_expr_with_tail};
pub(crate) use decl::GlobalExtensionMethodHeader;
use decl::{
    current_module_effect_method_def, current_module_extension_method_def,
    effect_method_hidden_name, extension_method_hidden_name, global_extension_method_header,
    lower_attached_impl_decl, lower_enum_decl, lower_impl_decl, lower_mod_decl, lower_role_decl,
    lower_type_decl, lower_type_with_bindings, lower_use_decl, lower_where_clause,
};
pub use patterns::lower_pat;
pub(crate) use patterns::{bind_pattern_locals, connect_pat_shape_and_locals};
use patterns::{connect_let_pattern, pattern_binding_name};
use structs::{
    export_runtime_struct_method_type, export_runtime_struct_receiver_type, invariant_args,
    lower_struct_decl, lower_struct_field_type, lower_struct_with_binding,
    lower_struct_with_bindings, synthetic_struct_constructor_body, synthetic_struct_field_body,
};
pub(crate) use support::with_companion_module;
pub(super) use support::{
    child_node, child_nodes, descendant_node, has_token, header_value_name, ident_name,
    ident_or_sigil_name,
};
pub(crate) use support::{
    clone_replace_effect_path_pos_between_arenas, direct_param_source_eff_tv, lambda_expr_eff_tv,
    replace_effect_path_neg, replace_effect_path_pos,
};
use support::{collect_act_type_scope, header_module_visibility, header_operator_fixity};
use support::{lookup_small_subst, neg_prim_type, prim_type};
pub(crate) use synthetic_act::{
    SyntheticActSource, SyntheticActSpec, materialize_synthetic_act, nullary_synthetic_act_spec,
    register_synthetic_act_identity, unary_synthetic_act_spec,
};
use var::{binding_var_sigils, lower_var_binding_suffix, sigil_pattern_binding_name};
