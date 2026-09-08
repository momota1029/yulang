//! Total expression and pattern-opener lexical scans shared with sealed Error runs.
use crate::parser::{
    LexIn, ParserIn, Stops,
    input::{
        current_item::{AcceptedPayload, CurrentPayload, LineEntry, current_item},
        item::Item,
        lexer::{scan_expression_payload, scan_operator_shaped_unknown},
        operator::OperatorSite,
        yumark::FenceBoundary,
    },
    literal::{
        quote_run, scan_expression_rule_literal_opener_token, scan_pattern_literal_opener_token,
        scan_string_opener_token,
    },
};

pub(in crate::parser) fn expression_item(
    mut i: ParserIn,
    site: OperatorSite,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_expression_item_lexical(
            lex,
            site,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
        ))
    })
    .expect("expression payload scanning is total")
}

#[allow(clippy::too_many_arguments)]
pub(in crate::parser) fn scan_expression_item_lexical(
    i: LexIn,
    site: OperatorSite,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> (Item, usize, LineEntry) {
    let (current, consumed) = i.with_str(|lex| {
        current_item(
            lex,
            item_origin,
            line_entry,
            fence,
            |lex, leading, origin, fence, _| {
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

pub(in crate::parser) fn scan_expression_payload_with_literals(
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
    scan_expression_payload(
        i,
        site,
        has_leading_trivia,
        payload_origin,
        fence,
        baseline,
        stops,
    )
}

pub(in crate::parser) fn scan_expression_literal_payload(
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

pub(in crate::parser) fn scan_pattern_literal_payload(mut i: LexIn) -> Option<AcceptedPayload> {
    // Pattern reserves one quote for RuleLiteral and three or more for String;
    // keep the rejected two-quote run maximal as one ordinary recovery Item.
    if quote_run(i.remainder()) == 2 {
        return i.token(scan_operator_shaped_unknown).map(literal_payload);
    }
    i.token(scan_pattern_literal_opener_token)
        .map(literal_payload)
}

fn literal_payload(token: crate::parser::input::item::Token) -> AcceptedPayload {
    AcceptedPayload {
        payload: CurrentPayload::Token(token),
        next_line_entry: LineEntry::InLine,
    }
}
