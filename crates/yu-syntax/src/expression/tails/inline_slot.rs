//! Shared Colon/With inline-slot boundary and recovery publication.

use crate::cursor::recovery::RecoveryDraft;
use crate::cursor::recovery::emit::emit_recovery_missing;
use crate::cursor::{LexIn, SyntaxIn};
use crate::lexical::item::{Item, LeadingTrivia};
use crate::lexical::observation::{
    implicit_delimited_newline, is_active_stop_lex, is_close, is_line_stop, is_separator,
};
use crate::lexical::stops::Stops;
use crate::recovery_record::{
    ExpectationSources, ExpectedSyntax, GrammarRole, RecoveryKind, RecoverySiteKey,
    SyntaxExpectation, UnexpectedSyntax,
};
use std::sync::Arc;

pub(super) fn is_inline_slot_boundary(
    i: SyntaxIn,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> bool {
    inline_boundary(item, baseline, stops)
        || i.map(
            |lex: LexIn| Some(is_active_stop_lex(lex, item, stops)),
            |stop| stop,
        )
        .unwrap_or(false)
}

pub(super) fn inline_boundary(item: &Item, baseline: usize, stops: Stops) -> bool {
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_separator(item)
        || is_close(item)
        || is_line_stop(item, stops)
        || implicit_delimited_newline(baseline, item.leading_view())
}

pub(super) fn emit_inline_leading(i: &mut SyntaxIn, item: &mut Item) {
    if !item.leading_view().is_grammar_empty() {
        item.emit_all_remaining_leading(&mut *i.state);
    }
}

pub(super) fn emit_inline_slot_missing(
    i: SyntaxIn,
    item: &mut Item,
    origin: usize,
    role: GrammarRole,
    expected: ExpectedSyntax,
    stops: Stops,
) {
    let at = if item.payload_view().is_boundary() {
        item.payload_view()
            .pending_boundary()
            .expect("boundary coordinate")
            .coordinate()
    } else {
        if item.payload_view().is_eof() && !is_line_stop(item, stops) {
            item.emit_eof_leading(&mut *i.state);
        }
        item.extent(origin).recovery_range().start
    };
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        inline_slot_draft(role, expected, RecoveryKind::Missing, range, Arc::from([]))
    });
}

pub(super) fn inline_slot_draft(
    role: GrammarRole,
    expected: ExpectedSyntax,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}
