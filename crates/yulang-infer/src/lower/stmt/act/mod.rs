mod body;
mod copy;
mod copy_lower;
mod copy_scheme;
mod copy_transform;
mod decl;

pub(crate) use body::lower_act_body;
pub(crate) use copy::{ActCopy, prepare_act_copy};
pub(crate) use copy_lower::lower_act_copy_body;
pub(crate) use copy_scheme::transform_copied_frozen_scheme;
pub(crate) use copy_transform::transform_copied_principal_body;
pub(crate) use decl::lower_act_decl;
