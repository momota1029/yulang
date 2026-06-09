use yulang_typed_ir as typed_ir;

use crate::ir::{Binding, ExprKind};

pub fn binding_is_parametric_runtime_intrinsic(binding: &Binding) -> bool {
    matches!(binding.body.kind, ExprKind::PrimitiveOp(_)) || binding_is_var_ref_constructor(binding)
}

pub(crate) fn binding_is_var_ref_constructor(binding: &Binding) -> bool {
    let typed_ir::Type::Fun { ret, .. } = &binding.scheme.body else {
        return false;
    };
    let typed_ir::Type::Named { path, .. } = ret.as_ref() else {
        return false;
    };
    path_has_suffix(path, &["std", "control", "var", "ref"])
}

fn path_has_suffix(path: &typed_ir::Path, suffix: &[&str]) -> bool {
    path.segments.len() >= suffix.len()
        && path
            .segments
            .iter()
            .rev()
            .zip(suffix.iter().rev())
            .all(|(segment, expected)| segment.0 == *expected)
}
