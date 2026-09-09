//! Direct Rowan emission for already-accepted parser items.

#[cfg(test)]
use crate::handoff::End;
use rowan::GreenNodeBuilder;
use std::{ops::Range, sync::Arc};

use crate::{
    recovery_record::{RecoveryKind, UnexpectedCategory, UnexpectedSyntax},
    syntax_kind::SyntaxKind,
};

use crate::{
    cursor::recovery::RecoveryDraft,
    cursor::{LexIn, SyntaxIn},
    lexical::item::{Item, ItemExtent, LeadingTrivia, TokenKind},
};

/// Sealed capability for one total malformed run.
///
/// Its private `SyntaxIn` cannot escape. The body can only perform total
/// lexical work, emit already-owned run bytes, append explicit unexpected
/// evidence, or terminally seal one record through eligible retry leading;
/// node and diagnostic operations remain owned by the helper.
pub(crate) struct ErrorRunOutput<'a, 'source, 'operators, 'cache> {
    input: SyntaxIn<'a, 'source, 'operators, 'cache>,
    error_node_extent: Option<Range<usize>>,
    record_extent: Option<Range<usize>>,
    unexpected: Vec<UnexpectedSyntax>,
    sealed: Option<ErrorRunSeal>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ErrorRunSeal {
    RecordThroughRetryLeading(UnexpectedCategory),
    PathSegmentRetryLeadingPrefix(UnexpectedCategory),
    CallArgumentRetryLeadingPrefix(UnexpectedCategory),
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
        self.assert_unsealed();
        self.input
            .token(|lex| Some(operation(lex)))
            .expect("an Error-run lexical operation is total")
    }

    pub(crate) fn emit_item_as(
        &mut self,
        item: Item,
        successor_origin: usize,
        kind: SyntaxKind,
    ) -> ItemExtent {
        self.assert_unsealed();
        let extent = item.extent(successor_origin);
        self.include_extent(extent.recovery_range());
        item.emit_remaining(&mut *self.input.state, kind);
        extent
    }

    pub(crate) fn emit_literal_segment(
        &mut self,
        text: &str,
        range: Range<usize>,
        kind: SyntaxKind,
    ) {
        self.assert_unsealed();
        assert!(!text.is_empty(), "an Error literal segment is nonempty");
        assert_eq!(
            range.end.checked_sub(range.start),
            Some(text.len()),
            "literal segment text and extent must agree"
        );
        self.include_extent(range);
        self.input.state.token(kind.into(), text);
    }

    pub(crate) fn append_unexpected(&mut self, unexpected: UnexpectedSyntax) {
        self.assert_unsealed();
        self.unexpected.push(unexpected);
    }

    /// Emits a contiguous same-line EOF-leading suffix while the Error node is
    /// still open. The suffix is physical Error content, so it extends the
    /// Error and record extents even though EOF itself is not a token.
    pub(crate) fn emit_same_line_eof_leading(
        &mut self,
        item: &mut Item,
        successor_origin: usize,
    ) -> Range<usize> {
        self.assert_unsealed();
        assert!(item.payload_view().is_eof(), "only EOF has EOF leading");
        assert!(
            !item.leading_view().contains_line_break(),
            "an Error never consumes newline EOF leading"
        );
        let extent = item.extent(successor_origin).remaining();
        assert!(!extent.is_empty(), "EOF Error leading is nonempty");
        self.include_extent(extent);
        item.emit_eof_leading(&mut *self.input.state);
        self.error_node_extent
            .clone()
            .expect("EOF leading extends a nonempty Error")
    }

    /// Extends only the committed diagnostic record through one unchanged
    /// retry Item's contiguous same-line leading. Success makes this
    /// capability terminal; ineligible Items leave it open and unchanged.
    pub(crate) fn seal_record_through_retry_leading(
        &mut self,
        retry: &Item,
        successor_origin: usize,
        category: UnexpectedCategory,
    ) -> bool {
        self.assert_unsealed();
        assert!(
            self.unexpected.is_empty(),
            "retry-leading sealing replaces ordinary unexpected evidence"
        );
        let error_node_extent = self
            .error_node_extent
            .as_ref()
            .expect("retry-leading sealing requires a nonempty Error body");
        let Some(suffix) = retry.retry_leading_diagnostic_suffix(successor_origin) else {
            return false;
        };
        if suffix.start != error_node_extent.end {
            return false;
        }
        let record_extent = error_node_extent.start..suffix.end;
        debug_assert!(record_extent.start < record_extent.end);
        self.record_extent = Some(record_extent);
        self.sealed = Some(ErrorRunSeal::RecordThroughRetryLeading(category));
        true
    }

    /// Emits only an eligible block-comment prefix from the same borrowed
    /// PathSegment retry Item, then seals the equal Error/record extent.
    pub(crate) fn seal_path_segment_retry_leading_prefix(
        &mut self,
        retry: &mut Item,
        successor_origin: usize,
        category: UnexpectedCategory,
    ) -> PathSegmentRetryLeadingSeal {
        self.assert_unsealed();
        assert!(
            self.unexpected.is_empty(),
            "PathSegment retry-leading sealing replaces ordinary unexpected evidence"
        );
        let error_node_extent = self
            .error_node_extent
            .as_ref()
            .expect("PathSegment retry-leading sealing requires a nonempty Error body");
        let Some(prefix) = retry.path_segment_retry_leading_prefix(successor_origin) else {
            return PathSegmentRetryLeadingSeal::Ineligible;
        };
        let prefix_range = prefix.range();
        if prefix_range.start != error_node_extent.end {
            return PathSegmentRetryLeadingSeal::Ineligible;
        }
        let sealed_extent = error_node_extent.start..prefix_range.end;
        retry.emit_path_segment_retry_leading_prefix(&mut *self.input.state, prefix);
        self.error_node_extent = Some(sealed_extent.clone());
        self.record_extent = Some(sealed_extent);
        self.sealed = Some(ErrorRunSeal::PathSegmentRetryLeadingPrefix(category));
        PathSegmentRetryLeadingSeal::Sealed
    }

    /// Emits one eligible complete same-line leading prefix from the same
    /// borrowed CallArgument retry Item, then seals the equal Error/record
    /// extent. Payload and boundary eligibility remain the Call owner's fact.
    pub(crate) fn seal_call_argument_retry_leading_prefix(
        &mut self,
        retry: &mut Item,
        successor_origin: usize,
        category: UnexpectedCategory,
    ) -> CallArgumentRetryLeadingSeal {
        self.assert_unsealed();
        assert!(
            self.unexpected.is_empty(),
            "CallArgument retry-leading sealing replaces ordinary unexpected evidence"
        );
        let error_node_extent = self
            .error_node_extent
            .as_ref()
            .expect("CallArgument retry-leading sealing requires a nonempty Error body");
        let Some(prefix) = retry.call_argument_retry_leading_prefix(successor_origin) else {
            return CallArgumentRetryLeadingSeal::Ineligible;
        };
        let prefix_range = prefix.range();
        if prefix_range.start != error_node_extent.end {
            return CallArgumentRetryLeadingSeal::Ineligible;
        }
        let sealed_extent = error_node_extent.start..prefix_range.end;
        retry.emit_call_argument_retry_leading_prefix(&mut *self.input.state, prefix);
        self.error_node_extent = Some(sealed_extent.clone());
        self.record_extent = Some(sealed_extent);
        self.sealed = Some(ErrorRunSeal::CallArgumentRetryLeadingPrefix(category));
        CallArgumentRetryLeadingSeal::Sealed
    }

    fn include_extent(&mut self, next: Range<usize>) {
        self.assert_unsealed();
        assert!(next.start < next.end, "an Error-run segment is nonempty");
        if let Some(extent) = &mut self.error_node_extent {
            assert_eq!(
                extent.end, next.start,
                "Error-run segments remain in physical source order"
            );
            extent.end = next.end;
        } else {
            self.error_node_extent = Some(next);
        }
        self.record_extent = self.error_node_extent.clone();
    }

    fn assert_unsealed(&self) {
        assert!(
            self.sealed.is_none(),
            "a sealed retry-leading Error run is terminal"
        );
    }
}

pub(crate) fn emit_recovery_missing(
    mut i: SyntaxIn,
    leading: LeadingTrivia,
    at: usize,
    make_draft: impl FnOnce(Range<usize>) -> RecoveryDraft,
) {
    emit_trivia(&mut i, &leading);
    i.state.start_node(SyntaxKind::Missing.into());
    i.state.finish_node();
    let range = at..at;
    let draft = make_draft(range.clone());
    draft.assert_emission(RecoveryKind::Missing, &range, &[]);
    i.recover.commit_recovery(draft);
}

/// Publish required list slots immediately before their already-owned newline.
pub(crate) fn emit_required_slots_before_newlines(
    i: &mut SyntaxIn,
    item: &mut Item,
    end_part: usize,
    origin: usize,
    needs_expression: &mut bool,
    recovery_requires_expression: &mut bool,
    make_draft: impl Fn(usize) -> RecoveryDraft,
) {
    {
        let recover = &mut *i.recover;
        let output = &mut *i.state;
        item.emit_leading_prefix_with_coordinate(output, end_part, origin, |kind, at, output| {
            if kind == crate::lexical::item::TriviaKind::Newline {
                if *needs_expression {
                    output.start_node(SyntaxKind::Missing.into());
                    output.finish_node();
                    recover.commit_recovery(make_draft(at));
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
    emitted_kind: SyntaxKind,
    unexpected: UnexpectedSyntax,
    make_draft: impl FnOnce(Range<usize>, Arc<[UnexpectedSyntax]>) -> RecoveryDraft,
) -> ItemExtent {
    emit_recovery_error_run(
        i,
        |run| {
            let extent = run.emit_item_as(item, successor_origin, emitted_kind);
            let UnexpectedSyntax::Token { range, .. } = &unexpected else {
                panic!("a one-Item Error requires Token unexpected evidence")
            };
            assert_eq!(range, &extent.recovery_range());
            run.append_unexpected(unexpected);
            extent
        },
        make_draft,
    )
}

pub(crate) fn emit_recovery_error_run<R>(
    i: SyntaxIn,
    body: impl FnOnce(&mut ErrorRunOutput<'_, '_, '_, '_>) -> R,
    make_draft: impl FnOnce(Range<usize>, Arc<[UnexpectedSyntax]>) -> RecoveryDraft,
) -> R {
    // This is atomic for normal parser returns: the one node and one record are
    // paired before the helper returns. `body` and `make_draft` are total
    // post-commit contracts; unwinding invalidates this GreenNodeBuilder.
    i.state.start_node(SyntaxKind::Error.into());
    let mut run = ErrorRunOutput {
        input: i,
        error_node_extent: None,
        record_extent: None,
        unexpected: Vec::new(),
        sealed: None,
    };
    let result = body(&mut run);
    let ErrorRunOutput {
        input,
        error_node_extent,
        record_extent,
        unexpected,
        sealed,
    } = run;
    input.state.finish_node();
    let error_node_extent =
        error_node_extent.expect("an Error run emits a nonempty physical extent");
    let range = record_extent.expect("an Error run records its emitted physical extent");
    let unexpected: Arc<[UnexpectedSyntax]> = match sealed {
        Some(ErrorRunSeal::RecordThroughRetryLeading(category)) => {
            assert!(unexpected.is_empty());
            assert_eq!(range.start, error_node_extent.start);
            assert!(range.end > error_node_extent.end);
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category,
            }])
        }
        Some(ErrorRunSeal::PathSegmentRetryLeadingPrefix(category)) => {
            assert!(unexpected.is_empty());
            assert_eq!(range, error_node_extent);
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category,
            }])
        }
        Some(ErrorRunSeal::CallArgumentRetryLeadingPrefix(category)) => {
            assert!(unexpected.is_empty());
            assert_eq!(range, error_node_extent);
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category,
            }])
        }
        None => {
            assert_eq!(range, error_node_extent);
            unexpected.into()
        }
    };
    let draft = make_draft(range.clone(), unexpected.clone());
    draft.assert_emission(RecoveryKind::Error, &range, &unexpected);
    input.recover.commit_recovery(draft);
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
