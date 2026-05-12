use yulang_typed_ir as typed_ir;

use crate::ids::TypeVar;
use crate::lower::LowerState;
use crate::symbols::Path;

pub(crate) fn export_runtime_struct_receiver_type(
    state: &LowerState,
    struct_path: &Path,
    type_arg_tvs: &[TypeVar],
) -> typed_ir::Type {
    typed_ir::Type::Named {
        path: crate::lower::role::export_runtime_path(
            &state.ctx.canonical_current_type_path(struct_path),
        ),
        args: type_arg_tvs
            .iter()
            .map(|tv| {
                typed_ir::TypeArg::Type(typed_ir::Type::Var(typed_ir::TypeVar(format!(
                    "t{}",
                    tv.0
                ))))
            })
            .collect(),
    }
}

pub(crate) fn export_runtime_struct_method_type(
    state: &LowerState,
    sig: &crate::lower::signature::SigType,
) -> typed_ir::Type {
    match sig {
        crate::lower::signature::SigType::Fun {
            arg, ret_eff, ret, ..
        } => typed_ir::Type::Fun {
            param: Box::new(export_runtime_struct_method_type(state, arg)),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(crate::lower::role::export_runtime_sig_row(
                state,
                ret_eff.as_ref(),
            )),
            ret: Box::new(export_runtime_struct_method_type(state, ret)),
        },
        other => crate::lower::role::export_runtime_sig_type(state, other),
    }
}
