//! Direct Rowan emission for already-accepted parser items.

#[cfg(test)]
use crate::handoff::End;
use rowan::GreenNodeBuilder;
use std::ops::Range;

use crate::syntax_kind::SyntaxKind;

use crate::{
    cursor::{LexIn, SyntaxIn},
    lexical::item::{Item, ItemExtent, LeadingTrivia, TokenKind},
};

/// Sealed capability for one total malformed run.
///
/// Its private `SyntaxIn` cannot escape. The body can only perform total
/// lexical work, emit already-owned run bytes, or terminally seal a run
/// through eligible retry leading; node ownership remains with the helper.
pub(crate) struct ErrorRunOutput<'a, 'source, 'operators, 'cache> {
    input: SyntaxIn<'a, 'source, 'operators, 'cache>,
    error_run_extent: Option<Range<usize>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum PathSegmentRetryLeadingSeal {
    Ineligible,
    Sealed,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CallArgumentRetryLeadingSeal {
    Ineligible,
    Sealed,
}

impl ErrorRunOutput<'_, '_, '_, '_> {
    pub(crate) fn lexical<O>(&mut self, operation: impl FnOnce(LexIn) -> O) -> O {
        self.input
            .token(|lex| Some(operation(lex)))
            .expect("an Error-run lexical operation is total")
    }

    pub(crate) fn emit_item_as(&mut self, item: Item, successor_origin: usize) -> ItemExtent {
        let extent = item.extent(successor_origin);
        self.include_extent(extent.recovery_range());
        item.emit_remaining_error(&mut *self.input.state);
        extent
    }

    pub(crate) fn emit_literal_segment(&mut self, text: &str, range: Range<usize>) {
        assert!(!text.is_empty(), "an Error literal segment is nonempty");
        assert_eq!(
            range.end.checked_sub(range.start),
            Some(text.len()),
            "literal segment text and extent must agree"
        );
        self.include_extent(range);
        self.input.state.token(SyntaxKind::Error.into(), text);
    }

    /// Emits a contiguous same-line EOF-leading suffix into the raw Error run.
    /// The suffix extends the raw Error run even though EOF itself is not a token.
    pub(crate) fn emit_same_line_eof_leading(
        &mut self,
        item: &mut Item,
        successor_origin: usize,
    ) -> Range<usize> {
        assert!(item.payload_view().is_eof(), "only EOF has EOF leading");
        assert!(
            !item.leading_view().contains_line_break(),
            "an Error never consumes newline EOF leading"
        );
        let extent = item.extent(successor_origin).remaining();
        assert!(!extent.is_empty(), "EOF Error leading is nonempty");
        self.include_extent(extent);
        item.emit_error_eof_leading(&mut *self.input.state);
        self.error_run_extent
            .clone()
            .expect("EOF leading extends a nonempty Error")
    }

    /// Emits an eligible block-comment prefix from the borrowed PathSegment
    /// retry Item into the raw Error run.
    pub(crate) fn emit_path_segment_retry_leading_prefix(
        &mut self,
        retry: &mut Item,
        successor_origin: usize,
    ) -> PathSegmentRetryLeadingSeal {
        let error_run_extent = self
            .error_run_extent
            .as_ref()
            .expect("PathSegment retry-leading sealing requires a nonempty Error body");
        let Some(prefix) = retry.path_segment_retry_leading_prefix(successor_origin) else {
            return PathSegmentRetryLeadingSeal::Ineligible;
        };
        let prefix_range = prefix.range();
        if prefix_range.start != error_run_extent.end {
            return PathSegmentRetryLeadingSeal::Ineligible;
        }
        let sealed_extent = error_run_extent.start..prefix_range.end;
        retry.emit_path_segment_retry_leading_prefix(&mut *self.input.state, prefix);
        self.error_run_extent = Some(sealed_extent.clone());
        PathSegmentRetryLeadingSeal::Sealed
    }

    /// Emits one eligible complete same-line leading prefix from the borrowed
    /// CallArgument retry Item into the raw Error run. Payload and boundary
    /// eligibility remain the Call owner's fact.
    pub(crate) fn emit_call_argument_retry_leading_prefix(
        &mut self,
        retry: &mut Item,
        successor_origin: usize,
    ) -> CallArgumentRetryLeadingSeal {
        let error_run_extent = self
            .error_run_extent
            .as_ref()
            .expect("CallArgument retry-leading sealing requires a nonempty Error body");
        let Some(prefix) = retry.call_argument_retry_leading_prefix(successor_origin) else {
            return CallArgumentRetryLeadingSeal::Ineligible;
        };
        let prefix_range = prefix.range();
        if prefix_range.start != error_run_extent.end {
            return CallArgumentRetryLeadingSeal::Ineligible;
        }
        let sealed_extent = error_run_extent.start..prefix_range.end;
        retry.emit_call_argument_retry_leading_prefix(&mut *self.input.state, prefix);
        self.error_run_extent = Some(sealed_extent.clone());
        CallArgumentRetryLeadingSeal::Sealed
    }

    fn include_extent(&mut self, next: Range<usize>) {
        assert!(next.start < next.end, "an Error-run segment is nonempty");
        if let Some(extent) = &mut self.error_run_extent {
            assert_eq!(
                extent.end, next.start,
                "Error-run segments remain in physical source order"
            );
            extent.end = next.end;
        } else {
            self.error_run_extent = Some(next);
        }
    }
}

pub(crate) fn emit_recovery_missing(mut i: SyntaxIn, leading: LeadingTrivia, at: usize) {
    emit_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::Missing.into());
    i.state.finish_node();
    let _ = at;
}

/// Publish required list slots immediately before their already-owned newline.
pub(crate) fn emit_required_slots_before_newlines(
    i: &mut SyntaxIn,
    item: &mut Item,
    end_part: usize,
    origin: usize,
    needs_expression: &mut bool,
    recovery_requires_expression: &mut bool,
) {
    {
        let output = &mut *i.state;
        item.emit_leading_prefix_with_coordinate(output, end_part, origin, |kind, at, output| {
            if kind == crate::lexical::item::TriviaKind::Newline {
                if *needs_expression {
                    output.start_node(SyntaxKind::Missing.into());
                    output.finish_node();
                    let _ = at;
                }
                *needs_expression = true;
                *recovery_requires_expression = false;
            }
        });
    }
}

pub(crate) fn emit_recovery_error_item(
    i: SyntaxIn,
    item: Item,
    successor_origin: usize,
) -> ItemExtent {
    emit_recovery_error_run(i, |run| run.emit_item_as(item, successor_origin))
}

pub(crate) fn emit_recovery_error_run<R>(
    i: SyntaxIn,
    body: impl FnOnce(&mut ErrorRunOutput<'_, '_, '_, '_>) -> R,
) -> R {
    // The physical token run is the only durable recovery fact.
    let mut run = ErrorRunOutput {
        input: i,
        error_run_extent: None,
    };
    let result = body(&mut run);
    let ErrorRunOutput {
        input,
        error_run_extent,
    } = run;
    let _ = input;
    error_run_extent.expect("an Error run emits a nonempty physical extent");
    result
}

pub(crate) fn emit_identifier_core(i: &mut SyntaxIn, item: Item) {
    debug_assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    i.state.start_node(SyntaxKind::IdentifierExpression.into());
    item.emit_remaining(&mut *i.state, SyntaxKind::Identifier);
    i.state.finish_node();
}

pub(crate) fn emit_integer_core(i: &mut SyntaxIn, item: Item) {
    debug_assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Integer));
    i.state.start_node(SyntaxKind::IntegerLiteral.into());
    item.emit_remaining(&mut *i.state, SyntaxKind::Integer);
    i.state.finish_node();
}

pub(crate) fn emit_operator_use(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    debug_assert!(item.payload_view().operator_use().is_some());
    i.state.start_node(kind.into());
    item.emit_remaining(&mut *i.state, SyntaxKind::Operator);
    i.state.finish_node();
}

/// An accepted contextual `with` outranks an otherwise selected dynamic word
/// operator, but remains a single already-owned Item.
pub(crate) fn emit_with_keyword(i: &mut SyntaxIn, item: Item) {
    let payload = item.payload_view();
    debug_assert!(
        payload.token_kind() == Some(TokenKind::Identifier) || payload.operator_use().is_some()
    );
    debug_assert_eq!(payload.spelling(), Some("with"));
    item.emit_remaining(&mut *i.state, SyntaxKind::WithKw);
}

pub(crate) fn emit_token_item(i: &mut SyntaxIn, item: Item) {
    let payload = item.payload_view();
    let kind = if payload.operator_use().is_some() {
        SyntaxKind::Operator
    } else {
        token_syntax_kind(
            payload
                .token_kind()
                .expect("only a lexical item can be emitted"),
        )
    };
    item.emit_remaining(&mut *i.state, kind);
}

/// Emits one committed interior literal Item while keeping accepted Yumark
/// quote prefixes outside the literal token kind.
pub(crate) fn emit_literal_item(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    debug_assert!(item.leading_view().is_grammar_empty());
    debug_assert!(item.payload_view().token_kind().is_some());
    item.emit_remaining(&mut *i.state, kind);
}

/// Gate 3's isolated cell fixture emits one already-accepted segmented item
/// without changing the ordinary canonical emitters before lexical closure.
#[cfg(test)]
pub(crate) fn emit_fragmented_item(i: &mut SyntaxIn, item: Item) {
    let payload = item.payload_view();
    let kind = if payload.operator_use().is_some() {
        Some(SyntaxKind::Operator)
    } else {
        payload.token_kind().map(token_syntax_kind)
    };
    let is_eof = payload.is_eof();
    match kind {
        Some(kind) => item.emit_remaining(&mut *i.state, kind),
        None if is_eof => {
            let mut item = item;
            item.emit_eof_leading(&mut *i.state);
        }
        None => unreachable!("a boundary has a dedicated terminal adapter"),
    }
}

/// The enclosing owner emits accepted EOF trivia after receiving `End`.
#[cfg(test)]
pub(crate) fn emit_end(output: &mut GreenNodeBuilder, end: &mut End) {
    end.item.emit_eof_leading(output);
}

fn emit_trivia(i: &mut SyntaxIn, trivia: &LeadingTrivia) {
    emit_trivia_builder(&mut *i.state, trivia);
}

fn emit_trivia_builder(output: &mut GreenNodeBuilder, trivia: &LeadingTrivia) {
    trivia.emit(output);
}

pub(crate) fn token_syntax_kind(kind: TokenKind) -> SyntaxKind {
    match kind {
        TokenKind::Identifier => SyntaxKind::Identifier,
        TokenKind::SigilIdentifier => SyntaxKind::SigilIdentifier,
        TokenKind::Integer => SyntaxKind::Integer,
        TokenKind::Operator => unreachable!("operators have a selected dynamic role"),
        TokenKind::LParen => SyntaxKind::LParen,
        TokenKind::RParen => SyntaxKind::RParen,
        TokenKind::LBracket => SyntaxKind::LBracket,
        TokenKind::RBracket => SyntaxKind::RBracket,
        TokenKind::LBrace => SyntaxKind::LBrace,
        TokenKind::RBrace => SyntaxKind::RBrace,
        TokenKind::Comma => SyntaxKind::Comma,
        TokenKind::Semicolon => SyntaxKind::Semicolon,
        TokenKind::Dot => SyntaxKind::Dot,
        TokenKind::DotDot => SyntaxKind::DotDot,
        TokenKind::Arrow => SyntaxKind::Arrow,
        TokenKind::Colon => SyntaxKind::Colon,
        TokenKind::Equals => SyntaxKind::Equals,
        TokenKind::Forall => SyntaxKind::ForKw,
        TokenKind::EffectRowApostrophe => SyntaxKind::Apostrophe,
        TokenKind::PolymorphicVariantColon => SyntaxKind::Colon,
        TokenKind::PatternSymbolColon => SyntaxKind::Colon,
        TokenKind::PathSeparator => SyntaxKind::ColonColon,
        TokenKind::Pipe => SyntaxKind::Pipe,
        TokenKind::Unknown => SyntaxKind::Unknown,
    }
}
