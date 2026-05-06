mod annotation;
mod arg;
mod body;
mod decl;
mod lambda;
mod lhs;
mod preregister;
mod recursive;
mod sig;

pub(crate) use annotation::{
    apply_binding_type_annotation_cast, connect_binding_type_annotation,
    connect_pattern_sig_annotation,
};
pub(crate) use arg::{ArgPatInfo, HeaderArg, collect_header_args, make_arg_pat_info};
pub(crate) use body::lower_binding_body;
pub(crate) use decl::{lower_binding, lower_binding_with_type_scope};
pub(crate) use lambda::wrap_header_lambdas;
pub(crate) use lhs::{direct_binding_name, extract_binding_lhs};
pub(crate) use preregister::{preregister_binding, preregister_binding_as_module_value};
pub(crate) use recursive::preconstrain_recursive_binding_header_shape;
pub(crate) use sig::binding_sig_var_names;
