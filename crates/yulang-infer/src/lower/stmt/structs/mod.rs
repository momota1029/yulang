mod decl;
mod export;
mod method;
mod synthetic;
mod r#type;

pub(crate) use decl::lower_struct_decl;
pub(crate) use export::{export_runtime_struct_method_type, export_runtime_struct_receiver_type};
pub(crate) use method::{lower_struct_with_binding, lower_struct_with_bindings};
pub(crate) use synthetic::{synthetic_struct_constructor_body, synthetic_struct_field_body};
pub(crate) use r#type::{invariant_args, lower_struct_field_type};
