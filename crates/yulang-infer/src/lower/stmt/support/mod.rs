mod companion;
mod effect_path_replace;
mod header;
mod lambda_effect;
mod prim;
mod subst;
mod syntax;
mod type_scope;

pub(crate) use companion::with_companion_module;
pub(crate) use effect_path_replace::{
    clone_replace_effect_path_pos_between_arenas, replace_effect_path_neg, replace_effect_path_pos,
};
pub(crate) use header::{header_module_visibility, header_operator_fixity, header_value_name};
pub(crate) use lambda_effect::{direct_param_source_eff_tv, lambda_expr_eff_tv};
pub(crate) use prim::{neg_prim_type, prim_type};
pub(crate) use subst::lookup_small_subst;
pub(crate) use syntax::{
    child_node, child_nodes, descendant_node, has_token, ident_name, ident_or_sigil_name,
};
pub(crate) use type_scope::collect_act_type_scope;
