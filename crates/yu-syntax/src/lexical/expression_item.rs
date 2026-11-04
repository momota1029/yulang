//! Total expression and pattern-opener lexical scans shared with sealed Error runs.
use crate::{
    cursor::{LexIn, SyntaxIn},
    lexical::{
        current_item::{AcceptedPayload, CurrentPayload, LineEntry, current_item},
        item::Item,
        lexer::{scan_expression_payload_with_symbols, scan_operator_shaped_unknown},
        operator_scan::OperatorSite,
        stops::Stops,
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
    literal::{
        quote_run, scan_expression_rule_literal_opener_token, scan_pattern_literal_opener_token,
        scan_string_opener_token,
    },
};

pub(crate) fn expression_item(
    i: SyntaxIn,
    site: OperatorSite,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    expression_item_with_doc_boundary(
        i,
        site,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn expression_item_with_doc_boundary(
    mut i: SyntaxIn,
    site: OperatorSite,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    doc_boundary: bool,
    declaration_doc: Option<crate::sequence::DeclarationDocContext>,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_expression_item_lexical_with_doc_boundary(
            lex,
            site,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            doc_boundary,
            declaration_doc,
        ))
    })
    .expect("expression payload scanning is total")
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn scan_expression_item_lexical(
    i: LexIn,
    site: OperatorSite,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    scan_expression_item_lexical_with_doc_boundary(
        i,
        site,
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        false,
        None,
    )
}

#[allow(clippy::too_many_arguments)]
fn scan_expression_item_lexical_with_doc_boundary(
    i: LexIn,
    site: OperatorSite,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    doc_boundary: bool,
    declaration_doc: Option<crate::sequence::DeclarationDocContext>,
) -> (Item, usize, LineEntry) {
    let (current, consumed) = i.with_str(|lex| {
        let marker_boundary = matches!(site, OperatorSite::Led)
            && (doc_boundary || declaration_doc.is_some())
            && matches!(
                observe_fenced_trivia(lex.remainder(), item_origin, line_entry, fence),
                TriviaObservation::Visible(visible) if
                    (declaration_doc.is_some_and(|doc|
                        item_origin + lex.remainder().len() - visible.source.len() <= doc.start_line_end)
                        && visible.source.starts_with("--")
                        && !visible.source.starts_with("---"))
                    || (doc_boundary && visible.indentation == Some(baseline)
                        && crate::yumark::judge::judge_document_marker(
                            visible.source, 0,
                            crate::yumark::judge::StatementPosition::CanonicalLineStart { base_col: baseline },
                        ).is_some())
            );
        current_item(
            lex,
            item_origin,
            line_entry,
            fence,
            |mut lex, leading, origin, fence, _| {
                if marker_boundary {
                    return lex
                        .token(scan_operator_shaped_unknown)
                        .map(|token| AcceptedPayload {
                            payload: CurrentPayload::Token(token),
                            next_line_entry: LineEntry::InLine,
                        });
                }
                scan_expression_payload_with_literals(
                    lex, site, leading, origin, fence, baseline, stops,
                )
            },
        )
        .expect("expression payload scanning is total")
    });
    (
        current.item,
        item_origin
            .checked_add(consumed.len())
            .expect("a direct expression coordinate must fit usize"),
        current.next_line_entry,
    )
}

pub(crate) fn scan_expression_payload_with_literals(
    mut i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> Option<AcceptedPayload> {
    if let Some(literal) = i.token(|lex| scan_expression_literal_payload(lex, site)) {
        return Some(literal);
    }
    scan_expression_payload_with_symbols(
        i,
        site,
        has_leading_trivia,
        payload_origin,
        fence,
        baseline,
        stops,
    )
}

pub(crate) fn scan_expression_literal_payload(
    mut i: LexIn,
    site: OperatorSite,
) -> Option<AcceptedPayload> {
    if matches!(site, OperatorSite::Nud)
        && let Some(token) = i.token(scan_expression_rule_literal_opener_token)
    {
        return Some(literal_payload(token));
    }
    i.token(scan_string_opener_token)
        .map(|(token, _)| literal_payload(token))
}

pub(crate) fn scan_pattern_literal_payload(mut i: LexIn) -> Option<AcceptedPayload> {
    // Pattern reserves one quote for RuleLiteral and three or more for String;
    // keep the rejected two-quote run maximal as one ordinary recovery Item.
    if quote_run(i.remainder()) == 2 {
        return i.token(scan_operator_shaped_unknown).map(literal_payload);
    }
    i.token(scan_pattern_literal_opener_token)
        .map(literal_payload)
}

pub(crate) fn scan_pattern_quote_literal_payload(i: LexIn) -> Option<AcceptedPayload> {
    (quote_run(i.remainder()) != 0).then_some(())?;
    scan_pattern_literal_payload(i)
}

fn literal_payload(token: crate::lexical::item::Token) -> AcceptedPayload {
    AcceptedPayload {
        payload: CurrentPayload::Token(token),
        next_line_entry: LineEntry::InLine,
    }
}
