//! Canonical-Statement admission and direct construction for doc declarations.

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
