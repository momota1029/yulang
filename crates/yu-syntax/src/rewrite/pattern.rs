//! Source-free direct Pattern construction.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

mod delimited;
#[cfg(test)]
mod literal;

use super::{
    RewriteIn, Stops,
    current_item::{CurrentItem, LineEntry, current_item},
    driver::{
        Either, NormalizedExit, TailExit, advanced_origin, complete, delimited_baseline, handoff,
        implicit_delimited_newline, ordinary_exit, scan_pattern_literal_payload, suffix_marker,
        token_kind,
    },
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{scan_identifier, scan_pattern_nud_payload, scan_pattern_payload},
    literal::{
        NormalizedRuleLiteralExit, NormalizedStringLiteralExit, rule_literal_normalized,
        string_literal_with_virtual_statements_normalized, string_mode_from_opener,
    },
    operator::{STOP_COMMA, STOP_IN, STOP_SEMICOLON, stops_for},
    statement::StatementLineHandoff,
    type_expr::{
        required_type_expr_normalized,
        required_type_expr_with_caller_stops_and_completion_normalized, type_nud_item_normalized,
    },
    yumark::FenceBoundary,
};

use self::delimited::{list_pattern, parenthesized_pattern, record_pattern};
#[cfg(test)]
pub(super) use self::literal::{PatternLiteralWitnessExit, pattern_literal_witness};

/// Caller-owned Pattern grammar boundaries. Nested delimiters replace its
/// non-close bits with their local comma/close mask; only the separate,
/// explicitly filtered caller-close capability is carried inward.
pub(super) type PatternStops = u16;

pub(super) const PATTERN_STOP_COLON: PatternStops = 1 << 0;
pub(super) const PATTERN_STOP_ARROW: PatternStops = 1 << 1;
pub(super) const PATTERN_STOP_ARM_GUARD_IF: PatternStops = 1 << 2;
pub(super) const PATTERN_STOP_ARM_GUARD_WHERE: PatternStops = 1 << 3;
pub(super) const PATTERN_STOP_COMMA: PatternStops = 1 << 4;
pub(super) const PATTERN_STOP_SEMICOLON: PatternStops = 1 << 5;
pub(super) const PATTERN_STOP_RPAREN: PatternStops = 1 << 6;
pub(super) const PATTERN_STOP_RBRACKET: PatternStops = 1 << 7;
pub(super) const PATTERN_STOP_RBRACE: PatternStops = 1 << 8;
pub(super) const PATTERN_STOP_EQUALS: PatternStops = 1 << 9;
/// An arm owner may preserve a comma only while recovering a missing or
/// malformed first Pattern. It is deliberately not a completed-Pattern tail
/// boundary, so it cannot change ordinary case-arm grammar.
pub(super) const PATTERN_STOP_ARM_RECOVERY_SEPARATOR: PatternStops = 1 << 10;
pub(super) const PATTERN_STOP_IN: PatternStops = 1 << 11;
pub(super) const PATTERN_STOP_LBRACE: PatternStops = 1 << 12;
pub(super) const PATTERN_STOP_PRIMARY_COLON: PatternStops = 1 << 13;

pub(super) const PATTERN_DEFAULT_STOPS: PatternStops = PATTERN_STOP_COMMA
    | PATTERN_STOP_SEMICOLON
    | PATTERN_STOP_RPAREN
    | PATTERN_STOP_RBRACKET
    | PATTERN_STOP_RBRACE
    | PATTERN_STOP_EQUALS;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct PatternMandatorySlotPolicy {
    pub(super) fresh_primary_recovery_stops: PatternStops,
    pub(super) recovered_primary_tail_stops: PatternStops,
}

/// Explicit right-close authority for one mandatory Pattern call. The sealed
/// representation cannot carry general Pattern stop bits.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct PatternCallerCloses(u8);

impl PatternCallerCloses {
    pub(super) const NONE: Self = Self(0);
    pub(super) const RPAREN: Self = Self(1 << 0);
    pub(super) const RBRACKET: Self = Self(1 << 1);
    pub(super) const RBRACE: Self = Self(1 << 2);

    pub(super) const fn union(self, additional: Self) -> Self {
        Self(self.0 | additional.0)
    }

    fn with_close(self, close: TokenKind) -> Self {
        let close = match close {
            TokenKind::RParen => Self::RPAREN,
            TokenKind::RBracket => Self::RBRACKET,
            TokenKind::RBrace => Self::RBRACE,
            _ => unreachable!("Pattern caller-close capability contains only right closes"),
        };
        self.union(close)
    }

    fn contains(self, kind: TokenKind) -> bool {
        self.0 & Self::from_close(kind).0 != 0
    }

    fn from_close(kind: TokenKind) -> Self {
        match kind {
            TokenKind::RParen => Self::RPAREN,
            TokenKind::RBracket => Self::RBRACKET,
            TokenKind::RBrace => Self::RBRACE,
            _ => Self::NONE,
        }
    }

    fn pattern_stops(self) -> PatternStops {
        [
            (Self::RPAREN, PATTERN_STOP_RPAREN),
            (Self::RBRACKET, PATTERN_STOP_RBRACKET),
            (Self::RBRACE, PATTERN_STOP_RBRACE),
        ]
        .into_iter()
        .filter_map(|(close, stop)| self.contains_capability(close).then_some(stop))
        .fold(0, |stops, close| stops | close)
    }

    fn type_stops(self) -> Stops {
        [
            (TokenKind::RParen, Self::RPAREN),
            (TokenKind::RBracket, Self::RBRACKET),
            (TokenKind::RBrace, Self::RBRACE),
        ]
        .into_iter()
        .filter_map(|(kind, close)| self.contains_capability(close).then_some(stops_for(kind)))
        .fold(0, |stops, close| stops | close)
            & !(STOP_COMMA | STOP_SEMICOLON)
    }

    fn contains_capability(self, close: Self) -> bool {
        self.0 & close.0 != 0
    }
}

pub(super) fn pattern_stops_from_owner(stops: Stops) -> PatternStops {
    [
        (TokenKind::Colon, PATTERN_STOP_COLON),
        (TokenKind::Comma, PATTERN_STOP_COMMA),
        (TokenKind::Semicolon, PATTERN_STOP_SEMICOLON),
        (TokenKind::RParen, PATTERN_STOP_RPAREN),
        (TokenKind::RBracket, PATTERN_STOP_RBRACKET),
        (TokenKind::RBrace, PATTERN_STOP_RBRACE),
        (TokenKind::Arrow, PATTERN_STOP_ARROW),
    ]
    .into_iter()
    .filter_map(|(kind, stop)| super::operator::active_stop_item(kind, stops).then_some(stop))
    .fold(0, |stops, stop| stops | stop)
}

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
enum PatternPrecedence {
    Lowest,
    TypeAnnotation,
    Alternation,
    Alias,
}

pub(super) fn pattern(i: RewriteIn) -> TailExit {
    pattern_with_stops(i, PATTERN_DEFAULT_STOPS)
}

pub(super) fn pattern_with_stops(i: RewriteIn, stops: PatternStops) -> TailExit {
    ordinary_exit(pattern_normalized(i, 0, LineEntry::InLine, None, stops))
}

pub(super) fn pattern_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    stops: PatternStops,
) -> NormalizedExit {
    let (item, item_origin, line_entry) =
        pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, stops);
    pattern_from_item_normalized(
        i,
        item,
        PatternPrecedence::Lowest,
        0,
        stops,
        StatementLineHandoff::OrdinaryLayout,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn pattern_from_item_normalized(
    i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    pattern_from_item_with_completion_normalized(
        i,
        item,
        minimum,
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
    )
    .0
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum PatternCompletion {
    Complete,
    Incomplete,
}

pub(super) struct PatternOutcome {
    pub(super) exit: TailExit,
    pub(super) completion: PatternCompletion,
}

#[allow(clippy::too_many_arguments)]
fn pattern_from_item_with_completion_normalized(
    i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, PatternCompletion) {
    let mut completion = PatternCompletion::Incomplete;
    let exit = pattern_from_item_recording_normalized(
        i,
        item,
        minimum,
        baseline,
        stops,
        line_handoff,
        &mut completion,
        item_origin,
        line_entry,
        fence,
    );
    (exit, completion)
}

#[allow(clippy::too_many_arguments)]
fn pattern_from_item_recording_normalized(
    i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    pattern_from_item_recording_with_policy_normalized(
        i,
        item,
        minimum,
        baseline,
        stops,
        line_handoff,
        PatternMandatorySlotPolicy::default(),
        PatternCallerCloses::NONE,
        completion,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn pattern_from_item_recording_with_policy_normalized(
    mut i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    policy: PatternMandatorySlotPolicy,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let baseline = delimited_baseline(baseline, item.leading_view());
    i.state.start_node(SyntaxKind::Pattern.into());
    let exit = pattern_from_item_core_normalized(
        i.rb(),
        item,
        minimum,
        baseline,
        stops,
        line_handoff,
        policy,
        caller_closes,
        completion,
        item_origin,
        line_entry,
        fence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn pattern_from_item_core_normalized(
    i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    policy: PatternMandatorySlotPolicy,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        *completion = PatternCompletion::Incomplete;
        let mut i = i;
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if is_mandatory_slot_fresh_primary_stop(&item, policy.fresh_primary_recovery_stops) {
        *completion = PatternCompletion::Incomplete;
        let mut i = i;
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if is_pattern_nud(&item, stops) {
        *completion = PatternCompletion::Complete;
        pattern_from_primary_with_recovered_tail_stops_normalized(
            i,
            item,
            minimum,
            baseline,
            stops,
            line_handoff,
            policy.recovered_primary_tail_stops,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        )
    } else {
        recover_pattern_primary_normalized(
            i,
            item,
            minimum,
            baseline,
            stops,
            line_handoff,
            policy,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        )
    }
}

pub(super) fn pattern_from_entry_item(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
) -> TailExit {
    ordinary_exit(pattern_from_entry_item_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        0,
        LineEntry::InLine,
        None,
    ))
}

pub(super) fn pattern_from_entry_item_with_completion(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
) -> PatternOutcome {
    let (exit, completion) = pattern_from_entry_item_with_completion_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        0,
        LineEntry::InLine,
        None,
    );
    PatternOutcome {
        exit: ordinary_exit(exit),
        completion,
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn pattern_from_entry_item_normalized(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    required_pattern_from_entry_item_with_policy_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        PatternMandatorySlotPolicy::default(),
        PatternCallerCloses::NONE,
        item_origin,
        line_entry,
        fence,
    )
    .0
}

#[allow(clippy::too_many_arguments)]
pub(super) fn pattern_from_entry_item_with_completion_normalized(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, PatternCompletion) {
    required_pattern_from_entry_item_with_policy_normalized(
        i,
        item,
        baseline,
        stops,
        line_handoff,
        PatternMandatorySlotPolicy::default(),
        PatternCallerCloses::NONE,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn required_pattern_from_entry_item_with_policy_normalized(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    policy: PatternMandatorySlotPolicy,
    caller_closes: PatternCallerCloses,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, PatternCompletion) {
    let stops = stops | caller_closes.pattern_stops();
    let mut completion = PatternCompletion::Incomplete;
    let exit = pattern_from_item_recording_with_policy_normalized(
        i,
        item,
        PatternPrecedence::Lowest,
        baseline,
        stops,
        line_handoff,
        policy,
        caller_closes,
        &mut completion,
        item_origin,
        line_entry,
        fence,
    );
    (exit, completion)
}

#[allow(clippy::too_many_arguments)]
fn recover_pattern_primary_normalized(
    mut i: RewriteIn,
    mut item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    policy: PatternMandatorySlotPolicy,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    *completion = PatternCompletion::Incomplete;
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if is_mandatory_slot_fresh_primary_stop(&item, policy.fresh_primary_recovery_stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if is_pattern_primary_boundary(&item, baseline, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(item), line_entry);
    }
    if is_current_pattern_tail(&item, stops) {
        emit_missing(&mut i, LeadingTrivia::default());
        return pattern_tail_normalized(
            i,
            item,
            minimum,
            baseline,
            stops,
            line_handoff,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        );
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) =
            pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, stops);
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if is_mandatory_slot_fresh_primary_stop(&item, policy.fresh_primary_recovery_stops) {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if is_pattern_primary_boundary(&item, baseline, stops) {
            i.state.finish_node();
            return complete(handoff(item), line_entry);
        }
        if is_current_pattern_tail(&item, stops) {
            i.state.finish_node();
            return pattern_tail_normalized(
                i,
                item,
                minimum,
                baseline,
                stops,
                line_handoff,
                caller_closes,
                completion,
                item_origin,
                line_entry,
                fence,
            );
        }
        if is_pattern_nud(&item, stops) {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.finish_node();
            *completion = PatternCompletion::Complete;
            return pattern_from_primary_with_recovered_tail_stops_normalized(
                i,
                item,
                minimum,
                baseline,
                stops,
                line_handoff,
                policy.recovered_primary_tail_stops,
                caller_closes,
                completion,
                item_origin,
                line_entry,
                fence,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn pattern_from_primary_normalized(
    i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    pattern_from_primary_with_recovered_tail_stops_normalized(
        i,
        item,
        minimum,
        baseline,
        stops,
        line_handoff,
        0,
        PatternCallerCloses::NONE,
        completion,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn pattern_from_primary_with_recovered_tail_stops_normalized(
    mut i: RewriteIn,
    item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    recovered_primary_tail_stops: PatternStops,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if item.payload_view().spelling() == Some("\"") {
        let entry = suffix_marker(i.rb());
        let exit = rule_literal_normalized(i.rb(), item, item_origin, line_entry, fence);
        item_origin = advanced_origin(item_origin, entry, i.rb());
        return match exit {
            NormalizedRuleLiteralExit::Complete(line_entry) => scan_pattern_tail_normalized(
                i,
                minimum,
                baseline,
                stops,
                line_handoff,
                caller_closes,
                completion,
                item_origin,
                line_entry,
                fence,
            ),
            NormalizedRuleLiteralExit::Boundary(item, line_entry) => {
                *completion = PatternCompletion::Incomplete;
                complete(handoff(item), line_entry)
            }
        };
    }
    if let Some(mode) = string_mode_from_opener(&item) {
        let entry = suffix_marker(i.rb());
        let exit = string_literal_with_virtual_statements_normalized(
            i.rb(),
            item,
            mode,
            item_origin,
            fence,
        );
        item_origin = advanced_origin(item_origin, entry, i.rb());
        return match exit {
            NormalizedStringLiteralExit::Complete(line_entry) => scan_pattern_tail_normalized(
                i,
                minimum,
                baseline,
                stops,
                line_handoff,
                caller_closes,
                completion,
                item_origin,
                line_entry,
                fence,
            ),
            NormalizedStringLiteralExit::Boundary(item, line_entry) => {
                *completion = PatternCompletion::Incomplete;
                complete(handoff(item), line_entry)
            }
        };
    }
    match token_kind(&item) {
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier) => {
            i.state.start_node(SyntaxKind::IdentifierPattern.into());
            emit_token_item(&mut i, item);
            i.state.finish_node();
            scan_pattern_tail_normalized(
                i,
                minimum,
                baseline,
                stops,
                line_handoff,
                caller_closes,
                completion,
                item_origin,
                line_entry,
                fence,
            )
        }
        Some(TokenKind::Integer) => {
            i.state.start_node(SyntaxKind::IntegerPattern.into());
            emit_token_item(&mut i, item);
            i.state.finish_node();
            scan_pattern_tail_normalized(
                i,
                minimum,
                baseline,
                stops,
                line_handoff,
                caller_closes,
                completion,
                item_origin,
                line_entry,
                fence,
            )
        }
        Some(TokenKind::Colon | TokenKind::PatternSymbolColon) => {
            i.state.start_node(SyntaxKind::SymbolPattern.into());
            emit_token_item(&mut i, item);
            let entry = suffix_marker(i.rb());
            if let Some(name) = i.token(scan_identifier) {
                emit_token_item(
                    &mut i,
                    Item::plain(LeadingTrivia::default(), Payload::Token(name)),
                );
                item_origin = advanced_origin(item_origin, entry, i.rb());
                line_entry = LineEntry::InLine;
            } else {
                emit_missing(&mut i, LeadingTrivia::default());
                *completion = PatternCompletion::Incomplete;
            }
            i.state.finish_node();
            scan_pattern_tail_normalized(
                i,
                minimum,
                baseline,
                stops,
                line_handoff,
                caller_closes,
                completion,
                item_origin,
                line_entry,
                fence,
            )
        }
        Some(TokenKind::LParen) => parenthesized_pattern(
            i,
            item,
            minimum,
            baseline,
            stops,
            line_handoff,
            recovered_primary_tail_stops,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        ),
        Some(TokenKind::LBracket) => list_pattern(
            i,
            item,
            minimum,
            baseline,
            stops,
            line_handoff,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        ),
        Some(TokenKind::LBrace) => record_pattern(
            i,
            item,
            minimum,
            baseline,
            stops,
            line_handoff,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        ),
        _ => unreachable!("the Pattern NUD judge accepted only Pattern primaries"),
    }
}

fn pattern_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    stops: PatternStops,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |lex, leading, origin, fence, _| {
                    scan_pattern_payload(lex, leading, origin, fence, stops)
                },
            )
        })
        .expect("Pattern payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

fn pattern_nud_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    stops: PatternStops,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
                item_origin,
                line_entry,
                fence,
                |mut lex, leading, origin, fence, _| {
                    scan_pattern_literal_payload(lex.rb())
                        .or_else(|| scan_pattern_nud_payload(lex, leading, origin, fence, stops))
                },
            )
        })
        .expect("Pattern NUD payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

#[allow(clippy::too_many_arguments)]
fn scan_pattern_tail_normalized(
    mut i: RewriteIn,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, item_origin, line_entry) =
        pattern_item_normalized(i.rb(), item_origin, line_entry, fence, stops);
    pattern_tail_normalized(
        i,
        item,
        minimum,
        baseline,
        stops,
        line_handoff,
        caller_closes,
        completion,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn pattern_tail_normalized(
    mut i: RewriteIn,
    mut item: Item,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if implicit_delimited_newline(baseline, item.leading_view()) {
        return complete(handoff(item), line_entry);
    }
    if is_pattern_tail_boundary(i.rb(), &item, stops) {
        return complete(handoff(item), line_entry);
    }
    if is_pattern_alias(&item) && minimum <= PatternPrecedence::Alias {
        *completion = PatternCompletion::Incomplete;
        item.emit_all_remaining_leading(&mut *i.state);
        i.state.start_node(SyntaxKind::PatternAliasTail.into());
        emit_pattern_alias_keyword(&mut i, item);
        (item, item_origin, line_entry) =
            pattern_item_normalized(i.rb(), item_origin, line_entry, fence, stops);
        if !item.payload_view().is_boundary()
            && token_kind(&item) == Some(TokenKind::Identifier)
            && !is_pattern_word_stop(&item, stops)
        {
            emit_token_item(&mut i, item);
            *completion = PatternCompletion::Complete;
            (item, item_origin, line_entry) =
                pattern_item_normalized(i.rb(), item_origin, line_entry, fence, stops);
        } else {
            (item, item_origin, line_entry) = recover_pattern_alias_binding_normalized(
                i.rb(),
                item,
                baseline,
                stops,
                completion,
                item_origin,
                line_entry,
                fence,
            );
        }
        i.state.finish_node();
        return pattern_tail_normalized(
            i,
            item,
            minimum,
            baseline,
            stops,
            line_handoff,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        );
    }
    if token_kind(&item) == Some(TokenKind::Pipe) && minimum <= PatternPrecedence::Alternation {
        item.emit_all_remaining_leading(&mut *i.state);
        i.state
            .start_node(SyntaxKind::PatternAlternationTail.into());
        emit_token_item(&mut i, item);
        *completion = PatternCompletion::Incomplete;
        let (mut rhs, rhs_origin, rhs_line_entry) =
            pattern_nud_item_normalized(i.rb(), item_origin, line_entry, fence, stops);
        let rhs_baseline = delimited_baseline(baseline, rhs.leading_view());
        if !rhs.payload_view().is_boundary()
            && !token_kind(&rhs).is_some_and(|kind| caller_closes.contains(kind))
        {
            rhs.emit_all_remaining_leading(&mut *i.state);
        }
        let entry = suffix_marker(i.rb());
        let exit = pattern_from_item_recording_with_policy_normalized(
            i.rb(),
            rhs,
            PatternPrecedence::Alternation,
            rhs_baseline,
            stops,
            line_handoff,
            PatternMandatorySlotPolicy::default(),
            caller_closes,
            completion,
            rhs_origin,
            rhs_line_entry,
            fence,
        );
        item_origin = advanced_origin(rhs_origin, entry, i.rb());
        i.state.finish_node();
        return continue_pattern_tail_normalized(
            i,
            exit,
            minimum,
            baseline,
            stops,
            line_handoff,
            caller_closes,
            completion,
            item_origin,
            fence,
        );
    }
    if token_kind(&item) == Some(TokenKind::Colon)
        && stops & PATTERN_STOP_COLON == 0
        && minimum <= PatternPrecedence::TypeAnnotation
    {
        item.emit_all_remaining_leading(&mut *i.state);
        i.state.start_node(SyntaxKind::PatternTypeAnnotation.into());
        emit_token_item(&mut i, item);
        *completion = PatternCompletion::Incomplete;
        let exit = pattern_type_annotation_rhs_normalized(
            i.rb(),
            baseline,
            stops,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        );
        i.state.finish_node();
        return exit;
    }
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn recover_pattern_alias_binding_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    stops: PatternStops,
    completion: &mut PatternCompletion,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    if item.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return (item, item_origin, line_entry);
    }
    if is_pattern_primary_boundary(&item, baseline, stops) || is_current_pattern_tail(&item, stops)
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return (item, item_origin, line_entry);
    }

    item.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) =
            pattern_item_normalized(i.rb(), item_origin, line_entry, fence, stops);
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
        if token_kind(&item) == Some(TokenKind::Identifier) && !is_pattern_word_stop(&item, stops) {
            item.emit_all_remaining_leading(&mut *i.state);
            i.state.finish_node();
            emit_token_item(&mut i, item);
            *completion = PatternCompletion::Complete;
            return pattern_item_normalized(i, item_origin, line_entry, fence, stops);
        }
        if is_pattern_primary_boundary(&item, baseline, stops)
            || is_current_pattern_tail(&item, stops)
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn continue_pattern_tail_normalized(
    i: RewriteIn,
    exit: NormalizedExit,
    minimum: PatternPrecedence,
    baseline: usize,
    stops: PatternStops,
    line_handoff: StatementLineHandoff,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => scan_pattern_tail_normalized(
            i,
            minimum,
            baseline,
            stops,
            line_handoff,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        ),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => pattern_tail_normalized(
            i,
            item,
            minimum,
            baseline,
            stops,
            line_handoff,
            caller_closes,
            completion,
            item_origin,
            line_entry,
            fence,
        ),
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            complete(Err(Either::Right(end)), line_entry)
        }
        deferred @ NormalizedExit::Deferred(_, _) => deferred,
    }
}

#[allow(clippy::too_many_arguments)]
fn pattern_type_annotation_rhs_normalized(
    mut i: RewriteIn,
    baseline: usize,
    stops: PatternStops,
    caller_closes: PatternCallerCloses,
    completion: &mut PatternCompletion,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (mut primary, item_origin, line_entry) =
        type_nud_item_normalized(i.rb(), item_origin, line_entry, fence);
    if !primary.payload_view().is_boundary()
        && !implicit_delimited_newline(baseline, primary.leading_view())
        && !token_kind(&primary).is_some_and(|kind| caller_closes.contains(kind))
    {
        primary.emit_all_remaining_leading(&mut *i.state);
    }
    let caller_stops = caller_closes.type_stops();
    if stops & PATTERN_STOP_IN != 0 {
        let (exit, primary_found) = required_type_expr_with_caller_stops_and_completion_normalized(
            i,
            primary,
            baseline,
            caller_stops | STOP_IN,
            item_origin,
            line_entry,
            fence,
        );
        if primary_found {
            *completion = PatternCompletion::Complete;
        }
        exit
    } else if caller_stops != 0 {
        *completion = PatternCompletion::Complete;
        required_type_expr_with_caller_stops_and_completion_normalized(
            i,
            primary,
            baseline,
            caller_stops,
            item_origin,
            line_entry,
            fence,
        )
        .0
    } else {
        *completion = PatternCompletion::Complete;
        required_type_expr_normalized(i, primary, baseline, item_origin, line_entry, fence)
    }
}

fn is_pattern_primary(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(
            TokenKind::Identifier
                | TokenKind::SigilIdentifier
                | TokenKind::Integer
                | TokenKind::LParen
                | TokenKind::LBracket
                | TokenKind::LBrace
        )
    )
}

pub(super) fn is_pattern_nud(item: &Item, stops: PatternStops) -> bool {
    (!is_pattern_word_stop(item, stops)
        && is_pattern_primary(item)
        && !(stops & PATTERN_STOP_LBRACE != 0 && token_kind(item) == Some(TokenKind::LBrace)))
        || token_kind(item) == Some(TokenKind::PatternSymbolColon)
        || (token_kind(item) == Some(TokenKind::Colon)
            && stops & (PATTERN_STOP_COLON | PATTERN_STOP_PRIMARY_COLON) == 0)
        || item.payload_view().spelling() == Some("\"")
        || string_mode_from_opener(item)
            .is_some_and(|mode| matches!(mode, super::literal::StringMode::Heredoc { .. }))
}

fn is_pattern_primary_boundary(item: &Item, baseline: usize, stops: PatternStops) -> bool {
    implicit_delimited_newline(baseline, item.leading_view())
        || item.payload_view().is_eof()
        || is_pattern_word_stop(item, stops)
        || token_kind(item).is_some_and(|kind| pattern_primary_stop_token(kind, stops))
}

fn is_pattern_tail_boundary(mut i: RewriteIn, item: &Item, stops: PatternStops) -> bool {
    token_kind(item).is_some_and(|kind| pattern_tail_stop_token(kind, stops))
        || (stops & PATTERN_STOP_ARM_GUARD_IF != 0
            && super::driver::is_contextual_word(i.rb(), item, "if"))
        || (stops & PATTERN_STOP_ARM_GUARD_WHERE != 0
            && super::driver::is_contextual_word(i, item, "where"))
        || is_pattern_word_stop(item, stops)
}

fn is_pattern_word_stop(item: &Item, stops: PatternStops) -> bool {
    stops & PATTERN_STOP_IN != 0
        && item.payload_view().token_kind() == Some(TokenKind::Identifier)
        && item.payload_view().spelling() == Some("in")
}

fn pattern_primary_stop_token(kind: TokenKind, stops: PatternStops) -> bool {
    match kind {
        TokenKind::Colon => stops & (PATTERN_STOP_COLON | PATTERN_STOP_PRIMARY_COLON) != 0,
        TokenKind::Arrow => stops & PATTERN_STOP_ARROW != 0,
        TokenKind::Comma => stops & (PATTERN_STOP_COMMA | PATTERN_STOP_ARM_RECOVERY_SEPARATOR) != 0,
        TokenKind::Semicolon => stops & PATTERN_STOP_SEMICOLON != 0,
        TokenKind::RParen => stops & PATTERN_STOP_RPAREN != 0,
        TokenKind::RBracket => stops & PATTERN_STOP_RBRACKET != 0,
        TokenKind::RBrace => stops & PATTERN_STOP_RBRACE != 0,
        TokenKind::Equals => stops & PATTERN_STOP_EQUALS != 0,
        TokenKind::LBrace => stops & PATTERN_STOP_LBRACE != 0,
        _ => false,
    }
}

fn is_mandatory_slot_fresh_primary_stop(item: &Item, stops: PatternStops) -> bool {
    token_kind(item).is_some_and(|kind| pattern_primary_stop_token(kind, stops))
}

fn pattern_tail_stop_token(kind: TokenKind, stops: PatternStops) -> bool {
    match kind {
        TokenKind::Colon => stops & PATTERN_STOP_COLON != 0,
        TokenKind::Comma => stops & PATTERN_STOP_COMMA != 0,
        _ => pattern_primary_stop_token(kind, stops),
    }
}

fn is_current_pattern_tail(item: &Item, stops: PatternStops) -> bool {
    is_pattern_alias(item)
        || token_kind(item) == Some(TokenKind::Pipe)
        || (stops & PATTERN_STOP_COLON == 0 && token_kind(item) == Some(TokenKind::Colon))
}

fn is_pattern_alias(item: &Item) -> bool {
    item.payload_view().token_kind() == Some(TokenKind::Identifier)
        && item.payload_view().spelling() == Some("as")
}

fn emit_pattern_alias_keyword(i: &mut RewriteIn, item: Item) {
    debug_assert_eq!(item.payload_view().spelling(), Some("as"));
    item.emit_payload(&mut *i.state, SyntaxKind::AsKw);
}
