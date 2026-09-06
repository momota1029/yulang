//! Direct Rowan emission for already-accepted rewrite items.

use std::{ops::Range, sync::Arc};

use crate::{
    session::{RecoveryKind, UnexpectedSyntax},
    syntax_kind::SyntaxKind,
};

use super::{
    LexIn, RewriteIn,
    driver::End,
    item::{Item, ItemExtent, LeadingTrivia, TokenKind},
    output::{RecoveryDraft, RewriteOutput},
};

/// Sealed capability for one total malformed run.
///
/// Its private `RewriteIn` cannot escape. The body can only perform total
/// lexical work, emit already-owned run bytes, and append explicit unexpected
/// evidence; node and diagnostic operations remain owned by the helper.
pub(super) struct ErrorRunOutput<'a, 'source, 'recover, 'operators, 'output, 'frozen> {
    input: RewriteIn<'a, 'source, 'recover, 'operators, 'output, 'frozen>,
    extent: Option<Range<usize>>,
    unexpected: Vec<UnexpectedSyntax>,
}

impl ErrorRunOutput<'_, '_, '_, '_, '_, '_> {
    pub(super) fn lexical<O>(&mut self, operation: impl FnOnce(LexIn) -> O) -> O {
        self.input
            .token(|lex| Some(operation(lex)))
            .expect("an Error-run lexical operation is total")
    }

    pub(super) fn emit_item_as(
        &mut self,
        item: Item,
        successor_origin: usize,
        kind: SyntaxKind,
    ) -> ItemExtent {
        let extent = item.extent(successor_origin);
        self.include_extent(extent.recovery_range());
        item.emit_remaining(&mut *self.input.state, kind);
        extent
    }

    pub(super) fn emit_literal_segment(
        &mut self,
        text: &str,
        range: Range<usize>,
        kind: SyntaxKind,
    ) {
        assert!(!text.is_empty(), "an Error literal segment is nonempty");
        assert_eq!(
            range.end.checked_sub(range.start),
            Some(text.len()),
            "literal segment text and extent must agree"
        );
        self.include_extent(range);
        self.input.state.token(kind.into(), text);
    }

    pub(super) fn append_unexpected(&mut self, unexpected: UnexpectedSyntax) {
        self.unexpected.push(unexpected);
    }

    fn include_extent(&mut self, next: Range<usize>) {
        assert!(next.start < next.end, "an Error-run segment is nonempty");
        if let Some(extent) = &mut self.extent {
            assert_eq!(
                extent.end, next.start,
                "Error-run segments remain in physical source order"
            );
            extent.end = next.end;
        } else {
            self.extent = Some(next);
        }
    }
}

pub(super) fn emit_recovery_missing(
    mut i: RewriteIn,
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
    i.state.commit_recovery(draft);
}

pub(super) fn emit_recovery_error_item(
    i: RewriteIn,
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

pub(super) fn emit_recovery_error_run<R>(
    i: RewriteIn,
    body: impl FnOnce(&mut ErrorRunOutput<'_, '_, '_, '_, '_, '_>) -> R,
    make_draft: impl FnOnce(Range<usize>, Arc<[UnexpectedSyntax]>) -> RecoveryDraft,
) -> R {
    // This is atomic for normal parser returns: the one node and one record are
    // paired before the helper returns. `body` and `make_draft` are total
    // post-commit contracts; unwinding invalidates this RewriteOutput.
    i.state.start_node(SyntaxKind::Error.into());
    let mut run = ErrorRunOutput {
        input: i,
        extent: None,
        unexpected: Vec::new(),
    };
    let result = body(&mut run);
    let ErrorRunOutput {
        input,
        extent,
        unexpected,
    } = run;
    input.state.finish_node();
    let range = extent.expect("an Error run emits a nonempty physical extent");
    let unexpected: Arc<[UnexpectedSyntax]> = unexpected.into();
    let draft = make_draft(range.clone(), unexpected.clone());
    draft.assert_emission(RecoveryKind::Error, &range, &unexpected);
    input.state.commit_recovery(draft);
    result
}

pub(super) fn emit_identifier_core(i: &mut RewriteIn, item: Item) {
    debug_assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    i.state.start_node(SyntaxKind::IdentifierExpression.into());
    item.emit_remaining(&mut *i.state, SyntaxKind::Identifier);
    i.state.finish_node();
}

pub(super) fn emit_integer_core(i: &mut RewriteIn, item: Item) {
    debug_assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Integer));
    i.state.start_node(SyntaxKind::IntegerLiteral.into());
    item.emit_remaining(&mut *i.state, SyntaxKind::Integer);
    i.state.finish_node();
}

pub(super) fn emit_operator_use(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    debug_assert!(item.payload_view().operator_use().is_some());
    i.state.start_node(kind.into());
    item.emit_remaining(&mut *i.state, SyntaxKind::Operator);
    i.state.finish_node();
}

/// An accepted contextual `with` outranks an otherwise selected dynamic word
/// operator, but remains a single already-owned Item.
pub(super) fn emit_with_keyword(i: &mut RewriteIn, item: Item) {
    let payload = item.payload_view();
    debug_assert!(
        payload.token_kind() == Some(TokenKind::Identifier) || payload.operator_use().is_some()
    );
    debug_assert_eq!(payload.spelling(), Some("with"));
    item.emit_remaining(&mut *i.state, SyntaxKind::WithKw);
}

pub(super) fn emit_token_item(i: &mut RewriteIn, item: Item) {
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
pub(super) fn emit_literal_item(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    debug_assert!(item.leading_view().is_grammar_empty());
    debug_assert!(item.payload_view().token_kind().is_some());
    item.emit_remaining(&mut *i.state, kind);
}

/// Gate 3's isolated cell fixture emits one already-accepted segmented item
/// without changing the ordinary canonical emitters before lexical closure.
#[cfg(test)]
pub(super) fn emit_fragmented_item(i: &mut RewriteIn, item: Item) {
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

/// An accepted owner emits the pending item's trivia before its zero-width
/// missing slot.
pub(super) fn emit_missing(i: &mut RewriteIn, leading: LeadingTrivia) {
    emit_trivia(i, &leading);
    i.state.start_node(SyntaxKind::Missing.into());
    i.state.finish_node();
}

pub(super) fn emit_leading_trivia(i: &mut RewriteIn, trivia: &LeadingTrivia) {
    emit_trivia(i, trivia);
}

pub(super) fn emit_error_item(i: &mut RewriteIn, item: Item) {
    i.state.start_node(SyntaxKind::Error.into());
    emit_token_item(i, item);
    i.state.finish_node();
}

/// The enclosing owner emits accepted EOF trivia after receiving `End`.
pub(super) fn emit_end(output: &mut RewriteOutput, end: &mut End) {
    end.item.emit_eof_leading(output);
}

fn emit_trivia(i: &mut RewriteIn, trivia: &LeadingTrivia) {
    emit_trivia_builder(&mut *i.state, trivia);
}

fn emit_trivia_builder(output: &mut RewriteOutput, trivia: &LeadingTrivia) {
    trivia.emit(output);
}

fn token_syntax_kind(kind: TokenKind) -> SyntaxKind {
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
