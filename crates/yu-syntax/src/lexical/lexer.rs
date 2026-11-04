//! Lexical item construction and ordinary trivia ownership for the parser.

#[cfg(test)]
use crate::lexical::item::{LeadingTrivia, Payload};
use chasa_recover::parser::{choice, token};
use reborrow_generic::Reborrow as _;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::lexical::operator_scan::OperatorSite;

use crate::{
    cursor::{LexIn, LexRecover, SyntaxIn},
    lexical::{
        current_item::{AcceptedPayload, CurrentPayload, LineEntry, current_item},
        item::{ForeignSplit, Item, PendingBoundary, PendingFragments, Token, TokenKind, Trivia},
        operator_scan::{scan_dangling_operator_fenced, scan_operator_fenced},
        stops::{STOP_ARROW, STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR, Stops},
        yumark::{FenceBoundary, FenceLineDecision, judge_fence_line},
    },
};

/// Complete one canonical Statement head. Visibility words are reserved here,
/// before dynamic operators, but nowhere in expression-only positions.
#[cfg(test)]
pub(crate) fn statement_item_after_trivia(
    mut i: SyntaxIn,
    leading: LeadingTrivia,
    baseline: usize,
    stops: Stops,
) -> Item {
    let has_leading_trivia = !leading.view().is_grammar_empty();
    let payload = i
        .token(|lex| scan_statement_payload(lex, has_leading_trivia, 0, None, baseline, stops))
        .map(accepted_payload)
        .unwrap_or(Payload::Eof);
    Item::plain(leading, payload)
}

/// Scan one complete canonical Statement item without access to the Rowan
/// sink. Callers may therefore use the exact typed boundary vocabulary inside
/// a rollback-capable lexical transaction.
#[cfg(test)]
pub(crate) fn scan_statement_item(mut i: LexIn, baseline: usize, stops: Stops) -> Option<Item> {
    let leading = scan_trivia(i.rb());
    let payload = scan_statement_payload(
        i,
        !leading.view().is_grammar_empty(),
        0,
        None,
        baseline,
        stops,
    )
    .map(accepted_payload)
    .unwrap_or(Payload::Eof);
    Some(Item::plain(leading, payload))
}

/// Raw payload vocabulary for one normalized canonical-Statement Item.
/// Current-Item owns leading trivia, fence boundaries, EOF, and Item assembly.
pub(crate) fn scan_statement_payload(
    mut i: LexIn,
    has_leading_trivia: bool,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> Option<AcceptedPayload> {
    if let Some(keyword) = i.token(scan_statement_keyword) {
        Some(AcceptedPayload {
            payload: CurrentPayload::Token(keyword),
            next_line_entry: LineEntry::InLine,
        })
    } else {
        scan_expression_payload(
            i,
            OperatorSite::Nud,
            has_leading_trivia,
            item_origin,
            fence,
            baseline,
            stops,
        )
    }
}

/// Raw payload vocabulary for one normalized expression Item. Leading trivia,
/// fence boundaries, EOF, and final Item construction remain owned by
/// `current_item`.
pub(crate) fn scan_expression_payload(
    mut i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> Option<AcceptedPayload> {
    let record_spread = stops & STOP_RECORD_SPREAD != 0;
    let marker_after_operator = stops & STOP_RECORD_SPREAD_AFTER_OPERATOR != 0;
    let payload =
        if let Some(slash) = i.token(|lex| scan_lambda_backslash(lex, payload_origin, fence)) {
            CurrentPayload::Token(slash)
        } else if record_spread
            && matches!(site, OperatorSite::Nud)
            && let Some(marker) = i.token(scan_record_spread_marker)
        {
            CurrentPayload::Token(marker)
        } else if stops & STOP_ARROW != 0
            && let Some(arrow) = i.token(scan_arm_arrow)
        {
            CurrentPayload::Token(arrow)
        } else if matches!(site, OperatorSite::Nud)
            && let Some(keyword) = i.token(scan_nud_keyword)
        {
            CurrentPayload::Token(keyword)
        } else if matches!(site, OperatorSite::Nud)
            && let Some(identifier) = i.token(scan_expression_sigil_identifier)
        {
            CurrentPayload::Token(identifier)
        } else if let Some(operator) = i.token(|lex| {
            scan_operator_fenced(
                lex,
                site,
                has_leading_trivia,
                baseline,
                stops,
                payload_origin,
                fence,
            )
        }) {
            CurrentPayload::Operator(operator)
        } else if matches!(site, OperatorSite::Led)
            && let Some(equals) = i.token(scan_assignment_equals)
        {
            CurrentPayload::Token(equals)
        } else if matches!(site, OperatorSite::Led)
            && has_leading_trivia
            && let Some(identifier) = i.token(scan_expression_sigil_identifier)
        {
            CurrentPayload::Token(identifier)
        } else if matches!(site, OperatorSite::Led)
            && let Some(operator) = i.token(|lex| {
                scan_dangling_operator_fenced(
                    lex,
                    OperatorSite::Led,
                    baseline,
                    stops,
                    payload_origin,
                    fence,
                )
            })
        {
            CurrentPayload::Operator(operator)
        } else if marker_after_operator || (record_spread && matches!(site, OperatorSite::Led)) {
            if let Some(marker) = i.token(scan_record_spread_marker) {
                CurrentPayload::Token(marker)
            } else {
                CurrentPayload::Token(scan_token(i)?)
            }
        } else {
            CurrentPayload::Token(scan_token(i)?)
        };
    Some(AcceptedPayload {
        payload,
        next_line_entry: LineEntry::InLine,
    })
}

/// Optional NUD payload vocabulary. The enclosing `current_item` transaction
/// owns rollback when no expression can start at this Item.
pub(crate) fn scan_nud_payload(
    mut i: LexIn,
    has_leading_trivia: bool,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> Option<AcceptedPayload> {
    let payload =
        if let Some(slash) = i.token(|lex| scan_lambda_backslash(lex, payload_origin, fence)) {
            CurrentPayload::Token(slash)
        } else if stops & STOP_ARROW != 0
            && let Some(arrow) = i.token(scan_arm_arrow)
        {
            CurrentPayload::Token(arrow)
        } else if let Some(keyword) = i.token(scan_nud_keyword) {
            CurrentPayload::Token(keyword)
        } else if let Some(token) = i.token(scan_lparen) {
            CurrentPayload::Token(token)
        } else if let Some(token) = i.token(scan_lbrace) {
            CurrentPayload::Token(token)
        } else if let Some(token) = i.token(scan_expression_sigil_identifier) {
            CurrentPayload::Token(token)
        } else if let Some(operator) = i.token(|lex| {
            scan_operator_fenced(
                lex,
                OperatorSite::Nud,
                has_leading_trivia,
                baseline,
                stops,
                payload_origin,
                fence,
            )
        }) {
            CurrentPayload::Operator(operator)
        } else if let Some(operator) = i.token(|lex| {
            scan_dangling_operator_fenced(
                lex,
                OperatorSite::Nud,
                baseline,
                stops,
                payload_origin,
                fence,
            )
        }) {
            CurrentPayload::Operator(operator)
        } else if let Some(token) = i.token(scan_expression_symbol_colon) {
            CurrentPayload::Token(token)
        } else if let Some(token) = i.token(scan_identifier) {
            CurrentPayload::Token(token)
        } else {
            CurrentPayload::Token(i.token(scan_number)?)
        };
    Some(AcceptedPayload {
        payload,
        next_line_entry: LineEntry::InLine,
    })
}

/// Path tails admit their sigil-aware segment vocabulary before falling back
/// to the ordinary normalized LED vocabulary.
pub(crate) fn scan_path_segment_payload(
    mut i: LexIn,
    has_leading_trivia: bool,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> Option<AcceptedPayload> {
    if let Some(segment) = i.token(scan_path_segment) {
        return Some(AcceptedPayload {
            payload: CurrentPayload::Token(segment),
            next_line_entry: LineEntry::InLine,
        });
    }
    scan_expression_payload(
        i,
        OperatorSite::Led,
        has_leading_trivia,
        payload_origin,
        fence,
        baseline,
        stops,
    )
}

fn scan_token(mut i: LexIn) -> Option<Token> {
    i.check(choice((
        token(scan_identifier),
        token(scan_number),
        token(scan_expression_colon),
        token(scan_punctuation),
        token(scan_unknown),
    )))
}

#[cfg(test)]
fn accepted_payload(accepted: AcceptedPayload) -> Payload {
    match accepted.payload {
        CurrentPayload::Token(token) => Payload::Token(token),
        CurrentPayload::Operator(operator) => Payload::Operator(operator),
    }
}

/// A dynamic table may recognize a word prefix before the ordinary scanner's
/// optional `?` / `!` suffix. A contextual word accepts only the full word.
pub(crate) fn contextual_word_suffix_follower(i: LexIn) -> Option<bool> {
    Some(!matches!(i.remainder().chars().next(), Some('?' | '!')))
}

pub(crate) fn introduced_body_indentation_normalized(
    i: SyntaxIn,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<usize> {
    i.map(
        |lex: LexIn| {
            Some(
                crate::lexical::trivia::newline_indentation_after_fenced_trivia(
                    lex.remainder(),
                    item_origin,
                    LineEntry::InLine,
                    fence,
                ),
            )
        },
        |indentation| indentation,
    )
    .flatten()
}

pub(crate) fn scan_case_label_payload(mut i: LexIn) -> Option<AcceptedPayload> {
    Some(token_payload(i.token(scan_apostrophe_sigil_identifier)?))
}

/// Raw NUD vocabulary for one normalized TypeExpression Item.
pub(crate) fn scan_type_nud_payload(
    mut i: LexIn,
    _has_leading_trivia: bool,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<AcceptedPayload> {
    if let Some(forall) = i.token(scan_type_forall) {
        return Some(token_payload(forall));
    }
    scan_type_payload_at(i, true, payload_origin, fence)
}

/// Raw successor vocabulary for one normalized TypeExpression Item.
pub(crate) fn scan_type_payload(
    i: LexIn,
    has_leading_trivia: bool,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<AcceptedPayload> {
    scan_type_payload_at(i, has_leading_trivia, payload_origin, fence)
}

fn scan_type_payload_at(
    mut i: LexIn,
    allow_tag: bool,
    _payload_origin: usize,
    _fence: Option<&FenceBoundary>,
) -> Option<AcceptedPayload> {
    if let Some(colon) = i.token(|lex| scan_type_polymorphic_variant_colon(lex, allow_tag)) {
        return Some(token_payload(colon));
    }
    let token = i.check(choice((
        token(scan_type_effect_row_apostrophe),
        token(scan_path_segment),
        token(scan_integer),
        choice((
            token(scan_exact_equals),
            token(scan_malformed_equals),
            token(scan_type_arrow),
            token(scan_type_colon),
            token(scan_punctuation),
            token(scan_unknown),
        )),
    )))?;
    Some(token_payload(token))
}

/// Type's mandatory-primary recovery must hand an exact `=` to its caller,
/// while a longer operator-shaped spelling is one malformed primary.
fn scan_malformed_equals(i: LexIn) -> Option<Token> {
    i.remainder().starts_with('=').then_some(())?;
    scan_operator_shaped_unknown(i)
}

/// Raw primary vocabulary for one normalized Pattern Item.
pub(crate) fn scan_pattern_nud_payload(
    mut i: LexIn,
    has_leading_trivia: bool,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
    stops: crate::pattern::PatternStops,
) -> Option<AcceptedPayload> {
    if pattern_range_start(i.rb(), payload_origin, fence, stops) {
        let mut marker = i.token(scan_pattern_range_marker)?;
        marker.kind = TokenKind::PatternRangeStart;
        return Some(token_payload(marker));
    }
    if let Some(literal) = i.token(crate::lexical::expression_item::scan_pattern_literal_payload) {
        return Some(literal);
    }
    if let Some(symbol) = i.token(scan_pattern_symbol_colon) {
        return Some(token_payload(symbol));
    }
    scan_pattern_payload(i, has_leading_trivia, payload_origin, fence, stops)
}

fn pattern_range_start(
    mut i: LexIn,
    origin: usize,
    fence: Option<&FenceBoundary>,
    stops: crate::pattern::PatternStops,
) -> bool {
    if !i.remainder().starts_with("..") {
        return false;
    }
    let mut source = i.remainder();
    let mut recover = LexRecover::new(i.recovery().operators());
    let mut probe = chasa_recover::In::new(&mut source, &mut recover, ());
    let Some(marker) = probe.token(scan_pattern_range_marker) else {
        return false;
    };
    pattern_range_upper_starts(
        probe.remainder(),
        probe.recovery().operators(),
        origin + marker.text.len(),
        fence,
        stops,
    )
}

fn pattern_range_upper_starts(
    source: &str,
    operators: &crate::operator_table::OperatorTable,
    origin: usize,
    fence: Option<&FenceBoundary>,
    stops: crate::pattern::PatternStops,
) -> bool {
    let mut source = source;
    let mut recover = LexRecover::new(operators);
    let mut probe = chasa_recover::In::new(&mut source, &mut recover, ());
    let Some(next) = current_item(
        probe.rb(),
        origin,
        LineEntry::InLine,
        fence,
        |lex, leading, origin, fence, _| scan_pattern_payload(lex, leading, origin, fence, stops),
    ) else {
        return false;
    };
    !next.item.leading_view().has_ordinary_newline()
        && next.item.payload_view().token_kind() == Some(TokenKind::Integer)
}

/// An expression tail can hand the first dot of a following arm to its owner.
pub(crate) fn pattern_range_after_expression_item(
    i: &SyntaxIn,
    item: &Item,
    origin: usize,
    fence: Option<&FenceBoundary>,
    stops: crate::pattern::PatternStops,
) -> Option<usize> {
    let (suffix, additional) = match item.payload_view().spelling()? {
        "." => {
            let suffix = i.remainder().strip_prefix('.')?;
            if suffix
                .chars()
                .next()
                .is_some_and(is_operator_shaped_character)
            {
                return None;
            }
            (suffix, 1)
        }
        ".." => (i.remainder(), 0),
        _ => return None,
    };
    pattern_range_upper_starts(suffix, i.operators(), origin + additional, fence, stops)
        .then_some(additional)
}

/// Raw successor vocabulary for one normalized Pattern Item.
pub(crate) fn scan_pattern_payload(
    mut i: LexIn,
    has_leading_trivia: bool,
    _payload_origin: usize,
    _fence: Option<&FenceBoundary>,
    stops: crate::pattern::PatternStops,
) -> Option<AcceptedPayload> {
    if has_leading_trivia
        && stops & crate::pattern::PATTERN_ARM_APPLICATION_STOPS
            == crate::pattern::PATTERN_ARM_APPLICATION_STOPS
        && let Some(symbol) = i.token(scan_pattern_symbol_colon)
    {
        Some(token_payload(symbol))
    } else if stops & crate::pattern::PATTERN_STOP_ARROW != 0
        && let Some(arrow) = i.token(scan_arm_arrow)
    {
        Some(token_payload(arrow))
    } else {
        Some(token_payload(i.token(scan_pattern_tail_token)?))
    }
}

fn token_payload(token: Token) -> AcceptedPayload {
    AcceptedPayload {
        payload: CurrentPayload::Token(token),
        next_line_entry: LineEntry::InLine,
    }
}

fn scan_pattern_tail_token(mut i: LexIn) -> Option<Token> {
    i.check(choice((
        token(scan_pattern_colon),
        token(scan_path_segment),
        token(scan_pattern_negative_integer),
        token(scan_integer),
        token(scan_pattern_range_marker),
        token(scan_exact_equals),
        token(scan_exact_pipe),
        choice((
            token(scan_pattern_malformed_fixed_operator),
            token(scan_punctuation),
            token(scan_unknown),
        )),
    )))
}

fn scan_pattern_negative_integer(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut signed| {
        (signed.next()? == '-').then_some(())?;
        signed.token(scan_integer)?;
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Integer,
        text: text.into(),
    })
}

fn scan_pattern_range_marker(mut i: LexIn) -> Option<Token> {
    if let Some(marker) = i.token(scan_record_spread_marker) {
        return Some(marker);
    }
    let mut source = i.remainder().strip_prefix("..")?;
    let mut recover = LexRecover::new(i.recovery().operators());
    let mut probe = chasa_recover::In::<_, _, ()>::new(&mut source, &mut recover, ());
    probe.token(scan_pattern_negative_integer)?;
    let (accepted, text) = i.with_str(|mut marker| scan_pair(marker.rb(), '.', '.'));
    accepted?;
    Some(Token {
        kind: TokenKind::DotDot,
        text: text.into(),
    })
}

/// Keep a rejected exact record marker or field introducer as one malformed
/// item.  This comes after their exact scanners, so plain `.` remains a
/// punctuation token and exact `..` / `=` retain their normal owners. An
/// inactive or longer arm-arrow spelling remains whole for recovery.
fn scan_pattern_malformed_fixed_operator(i: LexIn) -> Option<Token> {
    (i.remainder().starts_with("..")
        || i.remainder().starts_with('=')
        || i.remainder().starts_with("->"))
    .then_some(())?;
    scan_operator_shaped_unknown(i)
}

pub(crate) fn scan_operator_shaped_unknown(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut operator| {
        scan_operator_shaped_character(operator.rb())?;
        while operator
            .remainder()
            .chars()
            .next()
            .is_some_and(is_operator_shaped_character)
        {
            operator.next();
        }
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Unknown,
        text: text.into(),
    })
}

pub(crate) fn is_operator_shaped_unknown(item: &Item) -> bool {
    item.payload_view().token_kind() == Some(TokenKind::Unknown)
        && item
            .payload_view()
            .spelling()
            .is_some_and(|text| text.chars().all(is_operator_shaped_character))
}

#[cfg(test)]
pub(crate) fn scan_trivia(mut i: LexIn) -> LeadingTrivia {
    let mut parts = Vec::new();
    while let Some(part) = i.token(scan_trivia_part) {
        parts.push(part);
    }
    LeadingTrivia::ordinary(parts.into_boxed_slice())
}

pub(crate) fn scan_trivia_part(mut i: LexIn) -> Option<Trivia> {
    i.check(choice((
        token(scan_horizontal_whitespace),
        token(scan_newline),
        token(scan_line_comment),
        token(scan_block_comment),
    )))
}

fn scan_horizontal_whitespace(mut i: LexIn) -> Option<Trivia> {
    let (accepted, text) = i.rb().with_str(|mut whitespace| {
        matches!(whitespace.remainder().chars().next()?, ' ' | '\t').then_some(())?;
        while matches!(whitespace.remainder().chars().next(), Some(' ' | '\t')) {
            whitespace.next();
        }
        Some(())
    });
    accepted?;
    Some(Trivia::whitespace(text.into()))
}

fn scan_newline(mut i: LexIn) -> Option<Trivia> {
    let (accepted, text) = i.rb().with_str(|mut newline| match newline.next()? {
        '\r' => {
            let _ = newline.token(scan_line_feed);
            Some(())
        }
        '\n' => Some(()),
        _ => None,
    });
    accepted?;
    Some(Trivia::newline(text.into()))
}

fn scan_line_feed(mut i: LexIn) -> Option<()> {
    (i.next()? == '\n').then_some(())
}

fn scan_line_comment(mut i: LexIn) -> Option<Trivia> {
    let (accepted, text) = i.rb().with_str(|mut comment| {
        scan_pair(comment.rb(), '/', '/')?;
        while comment
            .remainder()
            .chars()
            .next()
            .is_some_and(|ch| !matches!(ch, '\r' | '\n'))
        {
            comment.next();
        }
        Some(())
    });
    accepted?;
    Some(Trivia::line_comment(text.into()))
}

fn scan_block_comment(mut i: LexIn) -> Option<Trivia> {
    let (accepted, text) = i.rb().with_str(|mut comment| {
        scan_pair(comment.rb(), '/', '*')?;
        let mut depth = 1usize;
        loop {
            if comment.token(scan_block_open).is_some() {
                depth += 1;
                continue;
            }
            if comment.token(scan_block_close).is_some() {
                depth -= 1;
                if depth == 0 {
                    return Some(());
                }
                continue;
            }
            if comment.next().is_none() {
                return Some(());
            }
        }
    });
    accepted?;
    Some(Trivia::block_comment(text.into()))
}

/// Fence-aware result for a multiline block-comment leading-trivia owner.
/// The surrounding current-Item constructor owns its one carrier and final
/// Item construction; the ordinary scanner and callers remain unchanged.
#[derive(Debug, Eq, PartialEq)]
pub(crate) enum FencedBlockComment {
    Complete(Trivia),
    Boundary {
        accepted: Trivia,
        pending: PendingBoundary,
    },
}

/// Scans one accepted fenced block comment. The caller supplies only the
/// current Item's immediate origin and lazy split accumulator.
pub(crate) fn scan_block_comment_fenced(
    mut i: LexIn,
    part_origin: usize,
    fence: &FenceBoundary,
    foreign: &mut Option<Vec<ForeignSplit>>,
) -> Option<FencedBlockComment> {
    let part = i.remainder();
    let (outcome, text) = i.rb().with_str(|mut comment| {
        scan_pair(comment.rb(), '/', '*')?;
        Some(scan_fenced_block_comment_body(
            comment,
            part,
            part_origin,
            fence,
            foreign,
        ))
    });
    let outcome = outcome?;
    let accepted = Trivia::block_comment(text.into());
    Some(match outcome {
        FencedBlockCommentBody::Complete => FencedBlockComment::Complete(accepted),
        FencedBlockCommentBody::Boundary(pending) => {
            FencedBlockComment::Boundary { accepted, pending }
        }
    })
}

enum FencedBlockCommentBody {
    Complete,
    Boundary(PendingBoundary),
}

fn scan_fenced_block_comment_body(
    mut i: LexIn,
    part: &str,
    part_origin: usize,
    fence: &FenceBoundary,
    foreign: &mut Option<Vec<ForeignSplit>>,
) -> FencedBlockCommentBody {
    let mut depth = 1usize;
    loop {
        if i.remainder().is_empty() {
            let coordinate = checked_suffix_coordinate(part, part_origin, i.remainder());
            return fenced_comment_line_decision(i, coordinate, fence, foreign)
                .unwrap_or_else(|| unreachable!("physical EOF is always a fence boundary"));
        }
        if i.token(scan_block_open).is_some() {
            depth = depth
                .checked_add(1)
                .expect("block-comment depth must fit usize");
            continue;
        }
        if i.token(scan_block_close).is_some() {
            depth -= 1;
            if depth == 0 {
                return FencedBlockCommentBody::Complete;
            }
            continue;
        }

        let character = i
            .next()
            .expect("the fenced block-comment cursor is known nonempty");
        let transitioned = match character {
            '\n' => true,
            '\r' if i.remainder().starts_with('\n') => {
                assert_eq!(i.next(), Some('\n'));
                true
            }
            _ => false,
        };
        if transitioned {
            let coordinate = checked_suffix_coordinate(part, part_origin, i.remainder());
            if let Some(boundary) = fenced_comment_line_decision(i.rb(), coordinate, fence, foreign)
            {
                return boundary;
            }
        }
    }
}

fn fenced_comment_line_decision(
    mut i: LexIn,
    coordinate: usize,
    fence: &FenceBoundary,
    foreign: &mut Option<Vec<ForeignSplit>>,
) -> Option<FencedBlockCommentBody> {
    match judge_fence_line(i.remainder(), coordinate, fence) {
        FenceLineDecision::Boundary(pending) => Some(FencedBlockCommentBody::Boundary(pending)),
        FenceLineDecision::Body { prefix: None, .. } => None,
        FenceLineDecision::Body {
            prefix: Some(prefix),
            content,
        } => {
            let prefix_length = content
                .checked_sub(prefix.facts.extent.start)
                .expect("accepted body coordinate follows its prefix start");
            assert_eq!(prefix.facts.extent.start, coordinate);
            assert!(content <= prefix.facts.extent.end);
            PendingFragments::record(
                foreign,
                ForeignSplit::quote_prefix(prefix.facts.extent.start, prefix_length),
            )
            .expect("accepted prefix ranges must stay ordered in one source root");
            consume_exact_bytes(i.rb(), prefix_length);
            None
        }
    }
}

fn consume_exact_bytes(mut i: LexIn, length: usize) {
    let mut consumed = 0usize;
    while consumed < length {
        consumed = consumed
            .checked_add(
                i.next()
                    .expect("accepted prefix must exist in the live suffix")
                    .len_utf8(),
            )
            .expect("accepted prefix length must fit usize");
    }
    assert_eq!(
        consumed, length,
        "accepted prefix must end at a UTF-8 boundary"
    );
}

#[cfg(test)]
pub(crate) fn scan_fenced_prior_trivia_part(mut i: LexIn) -> Option<Trivia> {
    i.check(choice((
        token(scan_horizontal_whitespace),
        token(scan_newline),
        token(scan_line_comment),
    )))
}

fn checked_suffix_coordinate(part: &str, part_origin: usize, suffix: &str) -> usize {
    let consumed = part
        .len()
        .checked_sub(suffix.len())
        .expect("live comment suffix cannot be longer than its entry suffix");
    assert_eq!(
        part.as_ptr().wrapping_add(consumed),
        suffix.as_ptr(),
        "live comment suffix must remain within its entry suffix"
    );
    part_origin
        .checked_add(consumed)
        .expect("physical comment coordinate must fit usize")
}

fn scan_block_open(i: LexIn) -> Option<()> {
    scan_pair(i, '/', '*')
}

fn scan_block_close(i: LexIn) -> Option<()> {
    scan_pair(i, '*', '/')
}

fn scan_pair(mut i: LexIn, first: char, second: char) -> Option<()> {
    (i.next()? == first).then_some(())?;
    (i.next()? == second).then_some(())
}

/// Complete headers reserve only their introducer, at both expression sites.
/// The lookahead borrows source; each accepted header Item is scanned later.
fn scan_lambda_backslash(
    mut i: LexIn,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<Token> {
    let source = i.remainder();
    let mut suffix = source.strip_prefix('\\')?;
    let mut suffix_origin = origin.checked_add(1)?;
    suffix = lambda_inline_suffix(suffix, suffix_origin, fence)?;
    suffix_origin = origin.checked_add(source.len().checked_sub(suffix.len())?)?;

    let mut parameters = 0usize;
    loop {
        if parameters != 0 && is_exact_arm_arrow(suffix) {
            break;
        }
        let next = if let Some(after_reference) = lambda_reference_suffix(suffix) {
            after_reference
        } else if let Some((_, after_identifier)) = source_identifier(suffix) {
            after_identifier
        } else {
            lambda_parenthesized_suffix(suffix, suffix_origin, fence)?
        };
        parameters = parameters.checked_add(1)?;
        suffix_origin = suffix_origin.checked_add(suffix.len().checked_sub(next.len())?)?;
        suffix = lambda_inline_suffix(next, suffix_origin, fence)?;
        suffix_origin = suffix_origin.checked_add(next.len().checked_sub(suffix.len())?)?;
    }
    let (_, text) = i.rb().with_str(|mut lex| lex.next());
    Some(Token {
        kind: TokenKind::Backslash,
        text: text.into(),
    })
}

/// A bare reference pattern is one lambda parameter, while a bare `&` that
/// cannot introduce an identifier remains available to operator parsing.
fn lambda_reference_suffix(source: &str) -> Option<&str> {
    let suffix = source.strip_prefix('&')?;
    source_identifier(suffix).map(|(_, remainder)| remainder)
}

/// Balance one parenthesized lambda parameter using source-only evidence.
/// Literal and trivia bodies are opaque so their parentheses cannot affect the
/// header decision. The real Pattern parser still owns all accepted contents.
fn lambda_parenthesized_suffix<'source>(
    mut source: &'source str,
    mut origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<&'source str> {
    source = source.strip_prefix('(')?;
    origin = origin.checked_add(1)?;
    let mut depth = 1usize;

    loop {
        use crate::lexical::trivia::{TriviaObservation, observe_logical_fenced_trivia};
        match observe_logical_fenced_trivia(source, origin, LineEntry::InLine, fence) {
            TriviaObservation::Boundary => return None,
            TriviaObservation::Visible(visible) if visible.source.len() != source.len() => {
                origin = origin.checked_add(source.len().checked_sub(visible.source.len())?)?;
                source = visible.source;
                continue;
            }
            TriviaObservation::Visible(_) => {}
        }

        if source.starts_with('"') || source.starts_with("~\"") {
            let next = lambda_literal_suffix(source, origin, fence)?;
            origin = origin.checked_add(source.len().checked_sub(next.len())?)?;
            source = next;
            continue;
        }
        let character = source.chars().next()?;
        source = &source[character.len_utf8()..];
        origin = origin.checked_add(character.len_utf8())?;
        match character {
            '(' => depth = depth.checked_add(1)?,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(source);
                }
            }
            _ => {}
        }
    }
}

/// Skip one rule/string literal while balancing a parenthesized parameter.
/// This recognizes the literal delimiters only; literal CST and recovery stay
/// with the committed Pattern parser.
fn lambda_literal_suffix<'source>(
    mut source: &'source str,
    mut origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<&'source str> {
    if source.starts_with('~') {
        source = &source[1..];
        origin = origin.checked_add(1)?;
    }
    let quotes = source.bytes().take_while(|byte| *byte == b'"').count();
    let delimiter = if quotes >= 3 { quotes } else { 1 };
    source = source.get(delimiter..)?;
    origin = origin.checked_add(delimiter)?;

    loop {
        let run = source.bytes().take_while(|byte| *byte == b'"').count();
        if run != 0 && (delimiter == 1 || run == delimiter) {
            return source.get(delimiter..);
        }
        if run != 0 {
            source = source.get(run..)?;
            origin = origin.checked_add(run)?;
            continue;
        }
        if source.starts_with('\\') {
            let mut characters = source.chars();
            let lead = characters.next()?.len_utf8();
            let target = characters.next()?.len_utf8();
            let width = lead.checked_add(target)?;
            source = source.get(width..)?;
            origin = origin.checked_add(width)?;
            continue;
        }
        let character = source.chars().next()?;
        let width = if character == '\r' && source.starts_with("\r\n") {
            2
        } else {
            character.len_utf8()
        };
        source = source.get(width..)?;
        origin = origin.checked_add(width)?;
        if matches!(character, '\r' | '\n') {
            let Some(fence) = fence else {
                continue;
            };
            match judge_fence_line(source, origin, fence) {
                FenceLineDecision::Boundary(_) => return None,
                FenceLineDecision::Body { prefix: None, .. } => {}
                FenceLineDecision::Body { content, .. } => {
                    let prefix = content.checked_sub(origin)?;
                    source = source.get(prefix..)?;
                    origin = content;
                }
            }
        }
    }
}

fn lambda_inline_suffix<'source>(
    source: &'source str,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<&'source str> {
    use crate::lexical::trivia::{TriviaObservation, observe_logical_fenced_trivia};
    match observe_logical_fenced_trivia(source, origin, LineEntry::InLine, fence) {
        TriviaObservation::Visible(visible) if visible.indentation.is_none() => {
            Some(visible.source)
        }
        _ => None,
    }
}

pub(crate) fn scan_identifier(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut word| {
        if !identifier_starts(word.remainder()) {
            return None;
        }
        let _ = word.next()?;
        while word.remainder().chars().next().is_some_and(is_xid_continue) {
            word.next();
        }
        if matches!(word.remainder().chars().next(), Some('?' | '!')) {
            word.next();
        }
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Identifier,
        text: text.into(),
    })
}

/// Contextual NUD keywords stay identifier-shaped until the accepting owner
/// chooses their CST kind. This source-only scanner enforces maximal words
/// before dynamic word operators are considered.
fn scan_nud_keyword(mut i: LexIn) -> Option<Token> {
    scan_exact_word(i.rb(), "if")
        .or_else(|| scan_exact_word(i.rb(), "case"))
        .or_else(|| scan_exact_word(i, "catch"))
}

fn scan_statement_keyword(mut i: LexIn) -> Option<Token> {
    scan_exact_word(i.rb(), "my")
        .or_else(|| scan_exact_word(i.rb(), "our"))
        .or_else(|| scan_exact_word(i.rb(), "pub"))
        .or_else(|| scan_exact_word(i.rb(), "use"))
        .or_else(|| scan_exact_word(i.rb(), "mod"))
        .or_else(|| scan_exact_word(i.rb(), "struct"))
        .or_else(|| scan_exact_word(i.rb(), "type"))
        .or_else(|| scan_exact_word(i, "for"))
}

/// Split the same maximal identifier spelling accepted by [`scan_identifier`]
/// without consuming source.
pub(crate) fn source_identifier(source: &str) -> Option<(&str, &str)> {
    if !identifier_starts(source) {
        return None;
    }
    let mut end = source.chars().next()?.len_utf8();
    for character in source[end..].chars() {
        if is_xid_continue(character) {
            end += character.len_utf8();
        } else {
            break;
        }
    }
    if matches!(source[end..].chars().next(), Some('?' | '!')) {
        end += 1;
    }
    Some((&source[..end], &source[end..]))
}

/// Report whether source begins with declaration-head lexical evidence.
///
/// This source-only predicate is for contextual declaration admission.  An
/// admitted owner still applies its own name-slot grammar; in particular, a
/// sigil identifier can admit a declaration whose required raw identifier
/// subsequently recovers it as malformed.
pub(crate) fn source_declaration_head(source: &str) -> bool {
    if source_identifier(source).is_some() {
        return true;
    }
    matches!(source.chars().next(), Some('$' | '&' | '\''))
        && source
            .chars()
            .next()
            .and_then(|sigil| source.get(sigil.len_utf8()..))
            .is_some_and(|suffix| source_identifier(suffix).is_some())
}

pub(crate) fn scan_apostrophe_sigil_identifier(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut segment| {
        (segment.next()? == '\'').then_some(())?;
        scan_identifier(segment.rb())?;
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::SigilIdentifier,
        text: text.into(),
    })
}

fn scan_expression_sigil_identifier(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut segment| {
        matches!(segment.next()?, '$' | '&' | '\'').then_some(())?;
        scan_identifier(segment.rb())?;
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::SigilIdentifier,
        text: text.into(),
    })
}

/// An arm owns only the complete fixed `->` spelling. A longer
/// operator-shaped spelling, such as `->>`, remains whole for ordinary
/// operator selection or recovery.
pub(crate) fn scan_arm_arrow(mut i: LexIn) -> Option<Token> {
    let remainder = i.remainder();
    is_exact_arm_arrow(remainder).then_some(())?;
    let (accepted, text) = i.rb().with_str(|mut arrow| scan_pair(arrow.rb(), '-', '>'));
    accepted?;
    Some(Token {
        kind: TokenKind::Arrow,
        text: text.into(),
    })
}

pub(crate) fn is_exact_arm_arrow(remainder: &str) -> bool {
    remainder.starts_with("->")
        && !remainder[2..]
            .chars()
            .next()
            .is_some_and(is_operator_shaped_character)
}

fn scan_exact_word(mut i: LexIn, word: &str) -> Option<Token> {
    let suffix = i.remainder().strip_prefix(word)?;
    if suffix
        .chars()
        .next()
        .is_some_and(|character| is_xid_continue(character) || matches!(character, '?' | '!'))
    {
        return None;
    }
    let (accepted, text) = i.rb().with_str(|mut keyword| {
        for expected in word.chars() {
            (keyword.next()? == expected).then_some(())?;
        }
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Identifier,
        text: text.into(),
    })
}

/// Classify the next scalar without consuming it.
///
/// `:identifier` needs this one-scalar category probe to decide whether its
/// colon is a composite Pattern token or a caller-owned colon stop.  The
/// identifier's spelling is still consumed only by [`scan_identifier`].
fn identifier_starts(remainder: &str) -> bool {
    remainder
        .chars()
        .next()
        .is_some_and(|first| first == '_' || is_xid_start(first))
}

pub(crate) fn scan_path_segment(mut i: LexIn) -> Option<Token> {
    if let Some(mut word) = i.token(scan_identifier) {
        if word.text.starts_with('_') && &*word.text != "_" {
            word.kind = TokenKind::SigilIdentifier;
        }
        return Some(word);
    }

    scan_sigil_path_segment(i)
}

fn scan_sigil_path_segment(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut segment| {
        matches!(segment.next()?, '$' | '&' | '\'').then_some(())?;
        scan_identifier(segment.rb())?;
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::SigilIdentifier,
        text: text.into(),
    })
}

/// Preserve declaration-parameter sigils without applying TypeExpression's
/// underscore-to-sigil path-segment classification.
pub(crate) fn scan_declaration_type_parameter(mut i: LexIn) -> Option<Token> {
    if let Some(word) = i.token(scan_identifier) {
        return Some(word);
    }
    i.token(scan_sigil_path_segment)
}

pub(crate) fn is_declaration_starter_word(word: &str) -> bool {
    matches!(
        word,
        "use"
            | "mod"
            | "struct"
            | "type"
            | "enum"
            | "error"
            | "role"
            | "impl"
            | "cast"
            | "act"
            | "for"
            | "my"
            | "our"
            | "pub"
            | "lazy"
            | "prefix"
            | "infix"
            | "suffix"
            | "nullfix"
    )
}

pub(crate) fn scan_integer(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut number| {
        let radix = number.token(|mut prefix| {
            (prefix.next()? == '0').then_some(())?;
            let radix = match prefix.next()? {
                'x' | 'X' => 16,
                'b' | 'B' => 2,
                'o' | 'O' => 8,
                _ => return None,
            };
            scan_radix_digit_run(prefix.rb(), radix)?;
            Some(())
        });
        if radix.is_none() {
            scan_decimal_digit_run(number.rb())?;
        }
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Integer,
        text: text.into(),
    })
}

fn scan_number(mut i: LexIn) -> Option<Token> {
    let (kind, text) = i.rb().with_str(|mut number| {
        let (digits, integer_text) = number.rb().with_str(scan_decimal_digit_run);
        digits?;

        let decimal = number.token(|mut decimal| {
            (decimal.next()? == '.').then_some(())?;
            scan_decimal_digit_run(decimal.rb())?;
            Some(())
        });
        let exponent = number.token(scan_float_exponent);
        if decimal.is_some() || exponent.is_some() {
            return Some(TokenKind::Float);
        }
        if integer_text == "0" {
            number.token(|mut prefix| {
                let radix = match prefix.next()? {
                    'x' | 'X' => 16,
                    'b' | 'B' => 2,
                    'o' | 'O' => 8,
                    _ => return None,
                };
                scan_radix_digit_run(prefix.rb(), radix)
            });
        }
        Some(TokenKind::Integer)
    });
    Some(Token {
        kind: kind?,
        text: text.into(),
    })
}

fn scan_float_exponent(mut i: LexIn) -> Option<()> {
    matches!(i.next()?, 'e' | 'E').then_some(())?;
    if matches!(i.remainder().chars().next(), Some('+' | '-')) {
        i.next();
    }
    scan_decimal_digit_run(i.rb())?;
    Some(())
}

fn scan_decimal_digit_run(mut i: LexIn) -> Option<()> {
    scan_radix_digit_run(i.rb(), 10)
}

fn scan_radix_digit_run(mut i: LexIn, radix: u32) -> Option<()> {
    let digit = |ch: char| ch.to_digit(radix).is_some();
    digit(i.next()?).then_some(())?;
    loop {
        let mut next = i.remainder().chars();
        match next.next() {
            Some(ch) if digit(ch) => {
                i.next();
            }
            Some('_') if next.next().is_some_and(digit) => {
                i.next();
                i.next();
            }
            _ => break,
        }
    }
    Some(())
}

pub(crate) fn scan_punctuation(i: LexIn) -> Option<Token> {
    let (kind, text) = i.with_str(|mut punctuation| match punctuation.next()? {
        '(' => Some(TokenKind::LParen),
        ')' => Some(TokenKind::RParen),
        '[' => Some(TokenKind::LBracket),
        ']' => Some(TokenKind::RBracket),
        '{' => Some(TokenKind::LBrace),
        '}' => Some(TokenKind::RBrace),
        ',' => Some(TokenKind::Comma),
        ';' => Some(TokenKind::Semicolon),
        '.' => punctuation
            .token(scan_dot)
            .is_none()
            .then_some(TokenKind::Dot),
        ':' => (punctuation.next()? == ':').then_some(TokenKind::PathSeparator),
        _ => None,
    });
    Some(Token {
        kind: kind?,
        text: text.into(),
    })
}

/// The expression tail owns only a lone colon; the longer `::` spelling
/// remains the path separator recognized by [`scan_punctuation`].
fn scan_expression_colon(mut i: LexIn) -> Option<Token> {
    scan_lone_colon(&i)?;
    let (accepted, text) = i
        .rb()
        .with_str(|mut colon| (colon.next()? == ':').then_some(()));
    accepted?;
    Some(Token {
        kind: TokenKind::Colon,
        text: text.into(),
    })
}

fn scan_expression_symbol_colon(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut symbol| {
        (symbol.next()? == ':').then_some(())?;
        identifier_starts(symbol.remainder()).then_some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::ExpressionSymbolColon,
        text: text.into(),
    })
}

pub(crate) fn is_expression_symbol_item(remaining: &str, item: &Item) -> bool {
    item.payload_view().token_kind() == Some(TokenKind::Colon) && identifier_starts(remaining)
}

/// Expression-only vocabulary; generic declaration scans retain plain Colon.
/// Consume only the colon so an outer Pattern owner can receive the same Item.
pub(crate) fn scan_expression_payload_with_symbols(
    mut i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
) -> Option<AcceptedPayload> {
    let mut accepted = scan_expression_payload(
        i.rb(),
        site,
        has_leading_trivia,
        payload_origin,
        fence,
        baseline,
        stops,
    )?;
    if (matches!(site, OperatorSite::Nud) || has_leading_trivia)
        && identifier_starts(i.remainder())
        && let CurrentPayload::Token(token) = &mut accepted.payload
        && token.kind == TokenKind::Colon
    {
        token.kind = TokenKind::ExpressionSymbolColon;
    }
    Some(accepted)
}

fn scan_type_arrow(i: LexIn) -> Option<Token> {
    let (accepted, text) = i.with_str(|mut arrow| scan_pair(arrow.rb(), '-', '>'));
    accepted?;
    Some(Token {
        kind: TokenKind::Arrow,
        text: text.into(),
    })
}

fn scan_type_forall(mut i: LexIn) -> Option<Token> {
    let suffix = i.remainder().strip_prefix("for")?;
    if suffix
        .chars()
        .next()
        .is_some_and(|character| is_xid_continue(character) || matches!(character, '?' | '!'))
    {
        return None;
    }
    let (accepted, text) = i.rb().with_str(|mut keyword| {
        (keyword.next()? == 'f').then_some(())?;
        (keyword.next()? == 'o').then_some(())?;
        (keyword.next()? == 'r').then_some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Forall,
        text: text.into(),
    })
}

fn scan_type_effect_row_apostrophe(mut i: LexIn) -> Option<Token> {
    i.remainder().starts_with("'[").then_some(())?;
    let (accepted, text) = i
        .rb()
        .with_str(|mut apostrophe| (apostrophe.next()? == '\'').then_some(()));
    accepted?;
    Some(Token {
        kind: TokenKind::EffectRowApostrophe,
        text: text.into(),
    })
}

fn scan_type_polymorphic_variant_colon(mut i: LexIn, allow_tag: bool) -> Option<Token> {
    let remainder = i.remainder();
    let after_colon = remainder.strip_prefix(':')?;
    let is_variant_colon = after_colon.starts_with('{')
        || (allow_tag && after_colon.chars().next().is_some_and(is_xid_start));
    is_variant_colon.then_some(())?;
    let (accepted, text) = i
        .rb()
        .with_str(|mut colon| (colon.next()? == ':').then_some(()));
    accepted?;
    Some(Token {
        kind: TokenKind::PolymorphicVariantColon,
        text: text.into(),
    })
}

fn scan_type_colon(mut i: LexIn) -> Option<Token> {
    scan_lone_colon(&i)?;
    let (accepted, text) = i
        .rb()
        .with_str(|mut colon| (colon.next()? == ':').then_some(()));
    accepted?;
    Some(Token {
        kind: TokenKind::Colon,
        text: text.into(),
    })
}

fn scan_pattern_colon(mut i: LexIn) -> Option<Token> {
    scan_lone_colon(&i)?;
    let (accepted, text) = i
        .rb()
        .with_str(|mut colon| (colon.next()? == ':').then_some(()));
    accepted?;
    Some(Token {
        kind: TokenKind::Colon,
        text: text.into(),
    })
}

fn scan_pattern_symbol_colon(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut colon| {
        (colon.next()? == ':').then_some(())?;
        identifier_starts(colon.remainder()).then_some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::PatternSymbolColon,
        text: text.into(),
    })
}

pub(crate) fn scan_exact_pipe(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i
        .rb()
        .with_str(|mut pipe| (pipe.next()? == '|').then_some(()));
    accepted?;
    Some(Token {
        kind: TokenKind::Pipe,
        text: text.into(),
    })
}

/// Expression assignment falls back to one character after dynamic LED admission.
fn scan_assignment_equals(i: LexIn) -> Option<Token> {
    i.remainder().starts_with('=').then_some(())?;
    let (_, text) = i.with_str(|mut lex| lex.next());
    Some(Token {
        kind: TokenKind::Equals,
        text: text.into(),
    })
}

/// Fixed declaration `=` requires the whole operator-shaped spelling.
pub(crate) fn scan_exact_equals(i: LexIn) -> Option<Token> {
    is_exact_equals_source(i.remainder()).then_some(())?;
    let (accepted, text) = i.with_str(|mut equals| {
        (equals.next()? == '=').then_some(())?;
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Equals,
        text: text.into(),
    })
}

pub(crate) fn is_exact_equals_source(source: &str) -> bool {
    source.starts_with('=')
        && !source[1..]
            .chars()
            .next()
            .is_some_and(is_operator_shaped_character)
}

fn scan_record_spread_marker(i: LexIn) -> Option<Token> {
    let (accepted, text) = i.with_str(|mut marker| {
        scan_pair(marker.rb(), '.', '.')?;
        marker
            .token(scan_operator_shaped_character)
            .is_none()
            .then_some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::DotDot,
        text: text.into(),
    })
}

fn scan_lone_colon(i: &LexIn) -> Option<()> {
    let remainder = i.remainder();
    (remainder.starts_with(':') && !remainder.starts_with("::")).then_some(())
}

fn scan_fixed_opener(i: LexIn, expected: char, kind: TokenKind) -> Option<Token> {
    let (accepted, text) = i.with_str(|mut opener| (opener.next()? == expected).then_some(()));
    accepted?;
    Some(Token {
        kind,
        text: text.into(),
    })
}

fn scan_lparen(i: LexIn) -> Option<Token> {
    scan_fixed_opener(i, '(', TokenKind::LParen)
}

pub(crate) fn scan_lbrace(i: LexIn) -> Option<Token> {
    scan_fixed_opener(i, '{', TokenKind::LBrace)
}

fn scan_dot(mut i: LexIn) -> Option<()> {
    (i.next()? == '.').then_some(())
}

fn scan_operator_shaped_character(mut i: LexIn) -> Option<()> {
    is_operator_shaped_character(i.next()?).then_some(())
}

fn is_operator_shaped_character(character: char) -> bool {
    !character.is_whitespace()
        && !character.is_ascii_digit()
        && character != '_'
        && !is_xid_continue(character)
        && !matches!(
            character,
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';' | '\\' | '\'' | '@'
        )
}

pub(crate) fn scan_unknown(i: LexIn) -> Option<Token> {
    let (character, text) = i.with_str(|mut one| one.next());
    character?;
    Some(Token {
        kind: TokenKind::Unknown,
        text: text.into(),
    })
}
