//! CST recovery emission.

use crate::{cursor::SyntaxIn, lexical::item::Item, syntax_kind::SyntaxKind};

pub(crate) mod emit;

/// Emits a direct `Invalid` wrapper around its complete nested construction.
/// The closure keeps the original item and builder ownership, so continuation
/// and balanced node construction remain parser-owned rather than diagnostic
/// state.
pub(crate) fn emit_structured_recovery_error_from_item<R>(
    mut i: SyntaxIn,
    primary: Item,
    body: impl FnOnce(SyntaxIn, Item) -> (R, usize),
) -> R {
    i.state.start_node(SyntaxKind::Invalid.into());
    let (result, _) = body(i.rb(), primary);
    i.state.finish_node();
    result
}
