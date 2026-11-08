//! Postfix guard ownership at statement and delimited-expression boundaries.

use crate::{
    ambient_claim::AmbientClaimContext,
    cursor::{SyntaxIn, SyntaxOutputCheckpoint},
    expression::{postfix_if_candidate, required_expr_item_normalized},
    handoff::{Either, MlMode, NormalizedExit},
    lexical::{
        expression_item::expression_item,
        operator_scan::OperatorSite,
        position::{advanced_origin, suffix_marker},
        stops::{STOP_COLON, STOP_ELSE, STOP_ELSIF, STOP_LBRACE, STOP_LINE_BREAK, Stops},
        yumark::FenceBoundary,
    },
    statement::StatementLineHandoff,
    syntax_kind::SyntaxKind,
};

#[allow(clippy::too_many_arguments)]
pub(crate) fn finish_postfix_if(
    mut i: SyntaxIn,
    checkpoint: SyntaxOutputCheckpoint,
    mut exit: NormalizedExit,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    loop {
        let (mut keyword, line) = match exit {
            NormalizedExit::Complete(Err(Either::Left(item)), line)
                if postfix_if_candidate(i.rb(), &item) =>
            {
                (item, line)
            }
            other => return other,
        };
        i.state
            .start_node_at(&checkpoint, SyntaxKind::PostfixIfExpression.into());
        keyword.emit_all_remaining_leading(&mut *i.state);
        keyword.emit_remaining(&mut *i.state, SyntaxKind::IfKw);
        let condition_stops =
            stops | STOP_COLON | STOP_LBRACE | STOP_ELSE | STOP_ELSIF | STOP_LINE_BREAK;
        let entry = suffix_marker(i.rb());
        let (mut item, item_origin, line) = expression_item(
            i.rb(),
            OperatorSite::Nud,
            origin,
            line,
            fence,
            baseline,
            condition_stops,
        );
        if !item.payload_view().is_boundary()
            && !item.payload_view().is_eof()
            && !crate::lexical::observation::is_line_stop(&item, condition_stops)
        {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        i.state.start_node(SyntaxKind::Condition.into());
        i.state.start_node(SyntaxKind::OperatorChain.into());
        exit = required_expr_item_normalized(
            i.rb(),
            item,
            None,
            baseline,
            condition_stops,
            MlMode::All,
            line_handoff,
            item_origin,
            line,
            fence,
            ambient,
            sequence,
        );
        i.state.finish_node();
        i.state.finish_node();
        i.state.finish_node();
        origin = advanced_origin(origin, entry, i.rb());
    }
}
