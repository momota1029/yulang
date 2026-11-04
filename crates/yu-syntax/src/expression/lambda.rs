//! Complete lambda headers and their ordinary mandatory body.

use crate::{
    ambient_claim::AmbientClaimContext,
    cursor::SyntaxIn,
    handoff::{MlMode, NormalizedExit},
    lexical::{
        current_item::{LineEntry, current_item},
        expression_item::expression_item,
        item::Item,
        lexer::scan_pattern_nud_payload,
        observation::token_kind,
        operator_scan::OperatorSite,
        position::{advanced_origin, suffix_marker},
        stops::{LAMBDA_RECOVERY_BOUNDARY, Stops},
        yumark::FenceBoundary,
    },
    pattern::{PATTERN_STOP_ARROW, PATTERN_STOP_ITEM, pattern_from_entry_item_normalized},
    statement::StatementLineHandoff,
    syntax_kind::SyntaxKind,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn lambda_nud_normalized(
    mut i: SyntaxIn,
    mut slash: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    slash.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::LambdaExpression.into());
    slash.emit_remaining(&mut *i.state, SyntaxKind::Backslash);
    let pattern_stops = PATTERN_STOP_ARROW | PATTERN_STOP_ITEM;
    let (mut item, origin, next_line_entry) =
        lambda_header_item(i.rb(), item_origin, line_entry, fence, pattern_stops);
    item_origin = origin;
    line_entry = next_line_entry;
    loop {
        match token_kind(&item) {
            Some(crate::lexical::item::TokenKind::Identifier) => {
                item.emit_remaining(&mut *i.state, SyntaxKind::Identifier);
                (item, item_origin, line_entry) =
                    lambda_header_item(i.rb(), item_origin, line_entry, fence, pattern_stops);
            }
            Some(crate::lexical::item::TokenKind::LParen) => {
                item.emit_all_remaining_leading(&mut *i.state);
                let entry = suffix_marker(i.rb());
                let exit = pattern_from_entry_item_normalized(
                    i.rb(),
                    item,
                    baseline,
                    pattern_stops,
                    line_handoff,
                    item_origin,
                    line_entry,
                    fence,
                    ambient,
                );
                item_origin = advanced_origin(item_origin, entry, i.rb());
                (item, line_entry) = match exit {
                    NormalizedExit::Complete(Err(crate::handoff::Either::Left(item)), line) => {
                        (item, line)
                    }
                    _ => unreachable!(
                        "complete source-only lambda header retains its next parameter or arrow"
                    ),
                };
            }
            Some(crate::lexical::item::TokenKind::Arrow) => {
                item.emit_remaining(&mut *i.state, SyntaxKind::Arrow);
                break;
            }
            _ => unreachable!("complete source-only header contains only admitted parameters"),
        }
    }
    let stops = stops | LAMBDA_RECOVERY_BOUNDARY;
    let (body, item_origin, line_entry) = expression_item(
        i.rb(),
        OperatorSite::Nud,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
    );
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = super::required_operand::required_inline_expr_item_normalized(
        i.rb(),
        body,
        None,
        baseline,
        stops,
        MlMode::All,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    i.state.finish_node();
    exit
}

fn lambda_header_item(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pattern_stops: crate::pattern::PatternStops,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let current = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_pattern_nud_payload(lex, leading, origin, fence, pattern_stops)
                },
            )
        })
        .expect("complete source-only header admission guarantees its Items");
    (
        current.item,
        advanced_origin(item_origin, entry, i.rb()),
        current.next_line_entry,
    )
}
