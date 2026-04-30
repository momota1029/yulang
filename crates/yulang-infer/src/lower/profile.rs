use std::time::Duration;

use crate::scc::CommitReadyProfile;

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FinalizeCompactProfile {
    pub total: Duration,
    pub iterations: usize,
    pub scc_compute: Duration,
    pub scc_compress: Duration,
    pub scc_share: Duration,
    pub commit_ready: CommitReadyProfile,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FinalizeCompactResults {
    pub finalized_defs: Vec<crate::ids::DefId>,
    pub profile: FinalizeCompactProfile,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LowerDetailProfile {
    pub lower_binding: Duration,
    pub extract_binding_lhs: Duration,
    pub lower_binding_scope: Duration,
    pub lower_binding_body: Duration,
    pub wrap_header_lambdas: Duration,
    pub lower_var_binding_suffix: Duration,
    pub lower_act_copy_body: Duration,
    pub lower_act_body: Duration,
    pub lower_act_body_collect_items: Duration,
    pub lower_act_body_ops: Duration,
    pub lower_act_body_preregister: Duration,
    pub lower_act_body_bindings: Duration,
    pub try_copy_lowered_act_body: Duration,
    pub try_lower_act_copy_from_template: Duration,
    pub copy_effect_ops_from_source_module: Duration,
    pub connect_pat_shape_and_locals: Duration,
    pub lower_expr: Duration,
    pub lower_expr_chain: Duration,
    pub resolve_path_expr: Duration,
    pub apply_suffix: Duration,
    pub lower_expr_atom: Duration,
    pub lower_expr_atom_tuple: Duration,
    pub lower_expr_atom_record: Duration,
    pub lower_expr_atom_block: Duration,
    pub lower_expr_atom_lambda: Duration,
    pub lower_expr_atom_catch: Duration,
    pub lower_expr_atom_case: Duration,
    pub lower_expr_atom_if: Duration,
    pub lower_expr_atom_literal: Duration,
    pub lower_catch: Duration,
    pub lower_catch_arm: Duration,
    pub bind_catch_pat_locals: Duration,
    pub connect_catch_pat_locals: Duration,
    pub instantiate_effect_op_use: Duration,
    pub extract_catch_effect_path: Duration,
    pub lower_catch_effect_payload_pat: Duration,
    pub connect_pat_name: Duration,
    pub connect_pat_tuple: Duration,
    pub connect_pat_record: Duration,
    pub connect_pat_poly_variant: Duration,
    pub connect_pat_alias: Duration,
    pub connect_pat_or: Duration,
}
