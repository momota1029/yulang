use super::*;

mod cast;
mod error;
mod regular;

pub(crate) use cast::{lower_cast_decl, lower_synthetic_variant_cast};
pub(crate) use error::{
    ErrorThrowVariant, ErrorUpSource, lower_synthetic_error_throw, lower_synthetic_error_up,
    lower_synthetic_error_wrap,
};

pub(crate) fn lower_impl_decl(state: &mut LowerState, node: &SyntaxNode) {
    regular::lower_impl_decl(state, node);
}

pub(crate) fn lower_attached_impl_decl(
    state: &mut LowerState,
    node: &SyntaxNode,
    receiver_path: &Path,
    receiver_type_param_names: &[String],
) {
    regular::lower_attached_impl_decl(state, node, receiver_path, receiver_type_param_names);
}
