//! Canonical-Statement admission and direct construction for doc declarations.
//!
//! WP-G12 CST contract: leading documents retain their existing sibling position.
//! An attached line document is a `DocCommentDeclaration` directly inside its
//! owning `BindingStatement`: after `BindingHeader` for an after-`=` document,
//! after `BindingBody` for a trailing document. Both forms preserve source order;
//! the physical newline stays with the next grammar owner. The owner constructs
//! the node, rather than putting it in the expression or interpreting trivia later.
//! An operator-table declaration of `--` disables both attached positions.
//! Fresh delimited/statement sequences discard the enclosing doc permission;
//! mandatory-operand scanning never receives a doc boundary.

use crate::{
    cursor::SyntaxIn,
    handoff::{NormalizedExit, complete},
    lexical::{current_item::LineEntry, item::Item, yumark::FenceBoundary},
    syntax_kind::SyntaxKind,
    yumark::{
        adapter::{parse_block_document_direct, parse_line_document_direct},
        judge::{
            BlockCloseContext, BlockCloseDecision, DocumentMarkerKind, StatementPosition,
            judge_block_close, judge_document_marker_parts,
        },
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DocCommentKind {
    Line,
    Block,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct DocCommentAdmission {
    kind: DocCommentKind,
    trailing_marker_bytes: usize,
    base_col: usize,
}

pub(crate) fn doc_comment_selected_lexical(
    source: &str,
    item: &Item,
    item_origin: usize,
    position: StatementPosition,
) -> Option<DocCommentAdmission> {
    let spelling = item.payload_view().spelling()?;
    let matched = judge_document_marker_parts(spelling, source, item_origin, position)?;
    Some(DocCommentAdmission {
        kind: match matched.marker.kind {
            DocumentMarkerKind::Line => DocCommentKind::Line,
            DocumentMarkerKind::BlockOpen => DocCommentKind::Block,
        },
        trailing_marker_bytes: matched.trailing_bytes,
        base_col: match position {
            StatementPosition::CanonicalLineStart { base_col } => base_col,
            StatementPosition::CanonicalSameLine | StatementPosition::NonStatement => 0,
        },
    })
}

pub(crate) fn doc_comment_declaration_normalized(
    mut i: SyntaxIn,
    mut item: Item,
    admission: DocCommentAdmission,
    item_origin: usize,
    line_entry: LineEntry,
    _fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let base_col = admission.base_col;
    item.emit_all_remaining_leading(&mut *i.state);
    let payload = item.extent(item_origin).payload();
    debug_assert_eq!(item.extent(item_origin).remaining().start, payload.start);

    i.state.start_node(SyntaxKind::DocCommentDeclaration.into());
    let marker_kind = match admission.kind {
        DocCommentKind::Line => SyntaxKind::DocLinePrefix,
        DocCommentKind::Block => SyntaxKind::DocBlockOpen,
    };
    let marker = match admission.kind {
        DocCommentKind::Line => "--",
        DocCommentKind::Block => "---",
    };
    i.state.token(marker_kind.into(), marker);
    i.advance_bytes(admission.trailing_marker_bytes);

    match admission.kind {
        DocCommentKind::Line => {
            let source = i.remainder();
            let operators = i.operators();
            let state = parse_line_document_direct(source, operators, &mut *i.state)
                .expect("a production line document has no deferred fence body");
            i.advance_bytes(state.consumed);
        }
        DocCommentKind::Block => {
            let source = i.remainder();
            let lf = source
                .find('\n')
                .expect("strict block admission proved an opening physical newline");
            let content_end = lf - usize::from(lf > 0 && source.as_bytes()[lf - 1] == b'\r');
            if content_end > 0 {
                i.state
                    .token(SyntaxKind::Whitespace.into(), &source[..content_end]);
            }
            i.state
                .token(SyntaxKind::Newline.into(), &source[content_end..lf + 1]);
            i.advance_bytes(lf + 1);

            let source = i.remainder();
            let operators = i.operators();
            let state = parse_block_document_direct(source, base_col, operators, &mut *i.state)
                .expect("selected yulang fence convergence is outside Gate 6");
            i.advance_bytes(state.consumed);

            let close_indent = i
                .remainder()
                .bytes()
                .take_while(|byte| matches!(byte, b' ' | b'\t'))
                .count();
            if close_indent > 0 {
                i.state.token(
                    SyntaxKind::Whitespace.into(),
                    &i.remainder()[..close_indent],
                );
                i.advance_bytes(close_indent);
            }

            let close_origin = item_origin
                .checked_add(admission.trailing_marker_bytes)
                .and_then(|origin| origin.checked_add(lf + 1))
                .and_then(|origin| origin.checked_add(state.consumed))
                .and_then(|origin| origin.checked_add(close_indent))
                .expect("a doc-comment coordinate fits usize");
            match judge_block_close(
                i.remainder(),
                close_origin,
                BlockCloseContext {
                    after_opening_line: true,
                    at_physical_line_start: true,
                    indent_col: base_col,
                    base_col,
                },
            ) {
                BlockCloseDecision::Close(_) => {
                    i.state.token(SyntaxKind::DocBlockClose.into(), "---");
                    i.advance_bytes(3);
                }
                BlockCloseDecision::MissingDocCommentClosingDelimiter { .. }
                | BlockCloseDecision::Text => {
                    i.state.start_node(SyntaxKind::Missing.into());
                    i.state.finish_node();
                }
            }
        }
    }
    i.state.finish_node();
    complete(Ok(()), line_entry)
}

/// Owns the after-`=` line document before the body starts. Only horizontal
/// whitespace is crossed; the physical newline remains for the body owner.
pub(super) fn line_doc_after_equals(
    mut i: SyntaxIn,
    origin: usize,
    doc: crate::sequence::DeclarationDocContext,
) -> Option<usize> {
    let source = i.remainder();
    let gap = source
        .bytes()
        .take_while(|b| matches!(b, b' ' | b'\t'))
        .count();
    let source = &source[gap..];
    if origin + gap > doc.start_line_end || !source.starts_with("--") || source.starts_with("---") {
        return None;
    }
    if gap != 0 {
        i.state
            .token(SyntaxKind::Whitespace.into(), &i.remainder()[..gap]);
        i.advance_bytes(gap);
    }
    i.state.start_node(SyntaxKind::DocCommentDeclaration.into());
    i.state.token(SyntaxKind::DocLinePrefix.into(), "--");
    i.advance_bytes(2);
    let state = parse_line_document_direct(i.remainder(), i.operators(), &mut *i.state)
        .expect("a line document has no deferred fence body");
    i.advance_bytes(state.consumed);
    i.state.finish_node();
    Some(origin + gap + 2 + state.consumed)
}

/// A completed expression returns its unconsumed marker to the declaration.
/// The node is emitted only after the expression/body node has closed.
pub(super) fn trailing_line_doc(
    mut i: SyntaxIn,
    exit: NormalizedExit,
    origin: usize,
    doc: Option<crate::sequence::DeclarationDocContext>,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    match exit {
        NormalizedExit::Complete(Err(crate::handoff::Either::Left(item)), line)
            if doc.is_some_and(|doc| item.extent(origin).payload().start <= doc.start_line_end) =>
        {
            if let Some(admission) = doc_comment_selected_lexical(
                i.remainder(),
                &item,
                origin,
                StatementPosition::CanonicalSameLine,
            ) {
                doc_comment_declaration_normalized(i.rb(), item, admission, origin, line, fence)
            } else {
                complete(crate::handoff::handoff(item), line)
            }
        }
        exit => exit,
    }
}

/// Member leading lines keep the sibling representation of canonical leading
/// docs. Same-line body introducers do not create a leading-doc position.
pub(super) fn member_leading_doc(
    source: &str,
    item: &Item,
    origin: usize,
) -> Option<DocCommentAdmission> {
    let base_col = item.leading_view().indentation_after_newline()?;
    let admission = doc_comment_selected_lexical(
        source,
        item,
        origin,
        StatementPosition::CanonicalLineStart { base_col },
    )?;
    (admission.kind == DocCommentKind::Line).then_some(admission)
}

pub(super) fn member_trailing_doc_selected(
    source: &str,
    item: &Item,
    origin: usize,
    doc: Option<crate::sequence::DeclarationDocContext>,
) -> Option<DocCommentAdmission> {
    if item.payload_view().is_boundary()
        || !doc.is_some_and(|doc| item.extent(origin).payload().start <= doc.start_line_end)
    {
        return None;
    }
    doc_comment_selected_lexical(source, item, origin, StatementPosition::CanonicalSameLine)
}

/// Keeps a separator inside the member only when it precedes an attached doc.
/// Without a doc, the exact existing separator/tree ownership is retained.
pub(super) fn member_trailing_doc(
    mut i: SyntaxIn,
    item: Item,
    origin: usize,
    line: LineEntry,
    doc: Option<crate::sequence::DeclarationDocContext>,
    fence: Option<&FenceBoundary>,
) -> (Option<Item>, usize, LineEntry) {
    if let Some(admission) = member_trailing_doc_selected(i.remainder(), &item, origin, doc) {
        let entry = i.remainder().len();
        doc_comment_declaration_normalized(i.rb(), item, admission, origin, line, fence);
        return (
            None,
            origin + entry - i.remainder().len(),
            LineEntry::InLine,
        );
    }
    if item.payload_view().token_kind() == Some(crate::lexical::item::TokenKind::Comma)
        && let Some(doc) = doc
    {
        let source = i.remainder().trim_start_matches([' ', '\t']);
        let gap = i.remainder().len() - source.len();
        if origin + gap <= doc.start_line_end
            && source.starts_with("--")
            && !source.starts_with("---")
        {
            crate::cursor::recovery::emit::emit_token_item(&mut i, item);
            let origin =
                line_doc_after_equals(i.rb(), origin, doc).expect("lookahead admitted line doc");
            return (None, origin, LineEntry::InLine);
        }
    }
    (Some(item), origin, line)
}

pub(crate) fn member_line_doc_at(
    source: &str,
    item: &Item,
    origin: usize,
    position: StatementPosition,
) -> Option<DocCommentAdmission> {
    let admission = doc_comment_selected_lexical(source, item, origin, position)?;
    (admission.kind == DocCommentKind::Line).then_some(admission)
}
