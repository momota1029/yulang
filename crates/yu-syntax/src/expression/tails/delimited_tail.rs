//! Call, index and projection wrappers around the shared delimiter owner.

use crate::ambient_claim::AmbientClaimContext;
use crate::cst_output::emit::emit_token_item;
use crate::cursor::SyntaxIn;
use crate::expression::continue_normalized_tail;
use crate::expression::delimited::{DelimitedOwner, delimited_items_normalized};
use crate::handoff::{MlMode, NormalizedExit};
use crate::lexical::current_item::LineEntry;
use crate::lexical::item::Item;
use crate::lexical::position::{advanced_origin, suffix_marker};
use crate::lexical::stops::Stops;
use crate::lexical::yumark::FenceBoundary;
use crate::operator_table::BindingPower;
use crate::statement::StatementLineHandoff;
use crate::syntax_kind::SyntaxKind;
use reborrow_generic::Reborrow as _;

#[allow(clippy::too_many_arguments)]
pub(crate) fn call_tail_normalized(
    mut i: SyntaxIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::CallTail.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        DelimitedOwner::Call,
        stops,
        baseline,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn index_tail_normalized(
    mut i: SyntaxIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::IndexTail.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        DelimitedOwner::Index,
        stops,
        baseline,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn projection_tail_normalized(
    mut i: SyntaxIn,
    dot: Item,
    open: Item,
    node: SyntaxKind,
    record_spread: bool,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: Stops,
    ml_mode: MlMode,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(node.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = delimited_items_normalized(
        i.rb(),
        if record_spread {
            DelimitedOwner::ProjectionRecord
        } else {
            DelimitedOwner::ProjectionTuple
        },
        stops,
        baseline,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_normalized_tail(
        i,
        threshold,
        baseline,
        stops,
        ml_mode,
        line_handoff,
        exit,
        item_origin,
        fence,
        ambient,
        sequence,
    )
}
