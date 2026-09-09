//! Contextual `as` owns one full Type and preserves its exact successor exit.

use crate::{
    ambient_claim::AmbientClaimContext,
    cursor::SyntaxIn,
    handoff::NormalizedExit,
    lexical::{current_item::LineEntry, item::Item, stops::Stops, yumark::FenceBoundary},
    recovery_record::{ExpressionRole, GrammarRole},
    syntax_kind::SyntaxKind,
    type_expr::{
        TypeOuterBoundary,
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient,
        type_nud_item_normalized_with_ambient,
    },
};
use reborrow_generic::Reborrow as _;

#[allow(clippy::too_many_arguments)]
pub(crate) fn type_annotation_tail_normalized(
    mut i: SyntaxIn,
    mut keyword: Item,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    keyword.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::TypeAnnotationTail.into());
    keyword.emit_remaining(&mut *i.state, SyntaxKind::AsKw);
    let (item, item_origin, line_entry) =
        type_nud_item_normalized_with_ambient(i.rb(), item_origin, line_entry, fence, ambient);
    let (exit, _) = required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
        i.rb(),
        item,
        GrammarRole::Expression(ExpressionRole::TypeAnnotation),
        baseline,
        stops,
        TypeOuterBoundary::NONE,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    i.state.finish_node();
    exit
}
