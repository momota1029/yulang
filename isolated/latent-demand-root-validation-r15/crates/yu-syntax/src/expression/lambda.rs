//! Complete unary lambda headers and their ordinary mandatory body.

use crate::{
    ambient_claim::AmbientClaimContext,
    cursor::SyntaxIn,
    handoff::{MlMode, NormalizedExit},
    lexical::{
        current_item::{AcceptedPayload, CurrentPayload, LineEntry, current_item},
        expression_item::expression_item,
        item::Item,
        lexer::{scan_arm_arrow, scan_identifier},
        operator_scan::OperatorSite,
        position::{advanced_origin, suffix_marker},
        stops::{LAMBDA_RECOVERY_BOUNDARY, Stops},
        yumark::FenceBoundary,
    },
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
    for kind in [SyntaxKind::Identifier, SyntaxKind::Arrow] {
        let entry = suffix_marker(i.rb());
        let current = i
            .token(|lex| {
                current_item(lex, item_origin, line_entry, fence, |lex, _, _, _, _| {
                    let token = match kind {
                        SyntaxKind::Identifier => scan_identifier(lex),
                        SyntaxKind::Arrow => scan_arm_arrow(lex),
                        _ => unreachable!("only the admitted header is consumed"),
                    }?;
                    Some(AcceptedPayload {
                        payload: CurrentPayload::Token(token),
                        next_line_entry: LineEntry::InLine,
                    })
                })
            })
            .expect("complete source-only header admission guarantees its Items");
        item_origin = advanced_origin(item_origin, entry, i.rb());
        line_entry = current.next_line_entry;
        current.item.emit_remaining(&mut *i.state, kind);
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
