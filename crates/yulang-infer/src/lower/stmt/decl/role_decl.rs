use crate::lower::{LowerState, SyntaxNode};

pub(crate) fn lower_impl_decl(state: &mut LowerState, node: &SyntaxNode) {
    crate::lower::role::lower_impl_decl(state, node);
}

/// `role Add 'a: ...` を lowering する。
///
/// role 名を型名前空間と companion module に登録し、method を値として登録する。
/// まずは impl 解決なしの role method fallback として使う。
pub(crate) fn lower_role_decl(state: &mut LowerState, node: &SyntaxNode) {
    crate::lower::role::lower_role_decl(state, node);
}
