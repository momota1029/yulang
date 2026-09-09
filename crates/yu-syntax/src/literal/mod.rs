//! Isolated literal Item construction before expression or Pattern dispatch.

use crate::{
    recovery_record::{
        Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole, LiteralExpected, LiteralRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};
use reborrow_generic::Reborrow as _;
use std::{ops::Range, sync::Arc};

use crate::{
    cursor::recovery::{
        RecoveryDraft,
        emit::{emit_literal_item, emit_recovery_error_run, emit_recovery_missing},
    },
    cursor::{LexIn, SyntaxIn},
    lexical::{
        current_item::LineEntry,
        item::{
            ForeignSplit, Item, LeadingTrivia, Payload, PendingFragments, PhysicalLeadingTrivia,
            Token, TokenKind,
        },
        yumark::{AcceptedQuotePrefix, FenceBoundary, FenceLineDecision, judge_fence_line},
    },
    virtual_statement_block::{VirtualStatementBlockExit, virtual_statement_block_normalized},
};

mod rule_literal;

pub(super) use rule_literal::{
    NormalizedRuleLiteralExit, rule_literal_normalized, scan_expression_rule_literal_opener_token,
    scan_pattern_literal_opener_token,
};

#[cfg(test)]
pub(super) use rule_literal::{
    PatternLiteralOpener, RuleLiteralExit, rule_literal_witness,
    scan_expression_rule_literal_opener_witness, scan_pattern_literal_opener_witness,
};

#[derive(Debug, Eq, PartialEq)]
pub(super) enum LiteralPiece {
    Complete(Item),
    Boundary {
        accepted: Option<Item>,
        pending: Item,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum StringMode {
    Normal,
    Heredoc { quotes: usize },
}

#[derive(Debug, Eq, PartialEq)]
#[cfg(test)]
pub(super) enum StringLiteralExit {
    Complete,
    Boundary(Item),
}

pub(super) enum NormalizedStringLiteralExit {
    Complete(LineEntry),
    Boundary(Item, LineEntry),
}

struct LiteralScan {
    piece: Option<LiteralPiece>,
    next_prefix: Option<AcceptedQuotePrefix>,
}

enum LiteralLineTransition {
    Continue,
    Structural(Option<AcceptedQuotePrefix>),
    Boundary(Item),
}

enum InterpolationBodyExit {
    Close { item: Item, line_entry: LineEntry },
    Boundary { item: Item, line_entry: LineEntry },
}

/// Accepts only a complete literal opener candidate. Two adjacent quotes are
/// the opener and terminator of one normal string; three or more form one
/// heredoc opener.
#[cfg(test)]
pub(super) fn scan_string_opener_witness(mut i: LexIn) -> Option<(Item, StringMode)> {
    let (token, mode) = i.token(scan_string_opener_token)?;
    Some((
        Item::plain(LeadingTrivia::default(), Payload::Token(token)),
        mode,
    ))
}

pub(super) fn scan_string_opener_token(mut i: LexIn) -> Option<(Token, StringMode)> {
    let run = quote_run(i.remainder());
    let (width, mode) = match run {
        0 => return None,
        1 | 2 => (1, StringMode::Normal),
        quotes => (quotes, StringMode::Heredoc { quotes }),
    };
    let (_, text) = i.rb().with_str(|opener| consume_exact_bytes(opener, width));
    Some((
        Token {
            kind: TokenKind::Unknown,
            text: text.into(),
        },
        mode,
    ))
}

/// Accepts the mode's terminator without partially consuming a heredoc quote
/// run of a different width.
pub(super) fn scan_string_close_witness(mut i: LexIn, mode: StringMode) -> Option<Item> {
    let (accepted, text) = i.rb().with_str(|close| accept_string_close(close, mode));
    accepted?;
    Some(literal_token(text))
}

pub(super) fn string_mode_from_opener(item: &Item) -> Option<StringMode> {
    if item.payload_view().token_kind().is_none() {
        return None;
    }
    let text = item.payload_view().spelling()?;
    let quotes = quote_run(text);
    if quotes != text.len() {
        return None;
    }
    match quotes {
        1 => Some(StringMode::Normal),
        3.. => Some(StringMode::Heredoc { quotes }),
        _ => None,
    }
}

fn accept_string_close(mut i: LexIn, mode: StringMode) -> Option<()> {
    let run = quote_run(i.remainder());
    let width = match mode {
        StringMode::Normal => (run != 0).then_some(1)?,
        StringMode::Heredoc { quotes } => (run == quotes).then_some(quotes)?,
    };
    consume_exact_bytes(i.rb(), width);
    Some(())
}

/// Scans one maximal nonempty StringText Item, or returns the first fence/EOF
/// boundary together with the text Item completed before it. The caller has
/// already ruled out a structural starter at the entry cursor.
#[cfg(test)]
pub(super) fn scan_string_text_witness(
    i: LexIn,
    part_origin: usize,
    fence: &FenceBoundary,
    mode: StringMode,
) -> LiteralPiece {
    scan_multiline_literal_item(i, part_origin, Some(fence), false, |source| {
        string_text_stop(source, mode)
    })
    .piece
    .expect("a text witness is entered only after ruling out a structural starter")
}

/// Builds one isolated StringLiteral through an injected interpolation-body
/// witness. The witness is the sole source of a successful borrowed `RBrace`;
/// this callback surface remains the preserved L3 primitive, while the L6
/// adapter below supplies full virtual-statement construction.
#[cfg(test)]
pub(super) fn string_literal_witness<'source, 'operators, 'frozen>(
    i: SyntaxIn<'_, 'source, 'operators, 'frozen>,
    opener: Item,
    mode: StringMode,
    part_origin: usize,
    fence: &FenceBoundary,
    mut interpolation_body: impl for<'a> FnMut(SyntaxIn<'a, 'source, 'operators, 'frozen>) -> Item,
) -> StringLiteralExit {
    match string_literal_with_interpolation_body(
        i,
        opener,
        mode,
        part_origin,
        Some(fence),
        |child, _, line_entry| InterpolationBodyExit::Close {
            item: interpolation_body(child),
            line_entry,
        },
    ) {
        NormalizedStringLiteralExit::Complete(_) => StringLiteralExit::Complete,
        NormalizedStringLiteralExit::Boundary(item, _) => StringLiteralExit::Boundary(item),
    }
}

/// L6 isolated StringLiteral construction using the canonical virtual
/// Statement sequence for every interpolation body.
#[cfg(test)]
pub(super) fn string_literal_with_virtual_statements_witness<'source, 'operators, 'frozen>(
    i: SyntaxIn<'_, 'source, 'operators, 'frozen>,
    opener: Item,
    mode: StringMode,
    part_origin: usize,
    fence: &FenceBoundary,
) -> StringLiteralExit {
    match string_literal_with_virtual_statements_normalized(
        i,
        opener,
        mode,
        part_origin,
        Some(fence),
        None.into(),
    ) {
        NormalizedStringLiteralExit::Complete(_) => StringLiteralExit::Complete,
        NormalizedStringLiteralExit::Boundary(item, _) => StringLiteralExit::Boundary(item),
    }
}

pub(super) fn string_literal_with_virtual_statements_normalized(
    i: SyntaxIn,
    opener: Item,
    mode: StringMode,
    part_origin: usize,
    fence: Option<&FenceBoundary>,
    ambient: crate::ambient_claim::AmbientClaimContext<'_>,
) -> NormalizedStringLiteralExit {
    string_literal_with_interpolation_body(
        i,
        opener,
        mode,
        part_origin,
        fence,
        |child, body_origin, line_entry| match virtual_statement_block_normalized(
            child,
            body_origin,
            line_entry,
            fence,
            ambient.unavailable(),
        ) {
            VirtualStatementBlockExit::Close(item, line_entry) => {
                InterpolationBodyExit::Close { item, line_entry }
            }
            VirtualStatementBlockExit::Boundary(item, line_entry) => {
                InterpolationBodyExit::Boundary { item, line_entry }
            }
        },
    )
}

fn string_literal_with_interpolation_body<'source, 'operators, 'frozen>(
    mut i: SyntaxIn<'_, 'source, 'operators, 'frozen>,
    opener: Item,
    mode: StringMode,
    mut part_origin: usize,
    fence: Option<&FenceBoundary>,
    mut interpolation_body: impl for<'a> FnMut(
        SyntaxIn<'a, 'source, 'operators, 'frozen>,
        usize,
        LineEntry,
    ) -> InterpolationBodyExit,
) -> NormalizedStringLiteralExit {
    i.state.start_node(SyntaxKind::StringLiteral.into());
    let mut opener = opener;
    opener.emit_all_remaining_leading(&mut *i.state);
    emit_literal_item(&mut i, opener, SyntaxKind::StringStart);
    let mut next_prefix = None;

    loop {
        let lead = if let Some(prefix) = next_prefix.take() {
            let structural = i
                .token(|lex| {
                    accepted_prefix_content(lex.remainder(), part_origin, &prefix)
                        .chars()
                        .next()
                })
                .expect("a deferred prefix has a structural successor");
            match structural {
                '"' => {
                    let close = i
                        .token(|lex| {
                            scan_prefixed_literal_token(lex, part_origin, &prefix, |token| {
                                accept_string_close(token, mode)
                            })
                        })
                        .expect("a judged prefixed terminator is accepted");
                    emit_literal_item(&mut i, close, SyntaxKind::StringEnd);
                    i.state.finish_node();
                    return NormalizedStringLiteralExit::Complete(LineEntry::InLine);
                }
                '%' => {
                    match emit_string_interpolation(
                        i.rb(),
                        Some(prefix),
                        &mut part_origin,
                        fence,
                        &mut interpolation_body,
                    ) {
                        Ok(()) => continue,
                        Err(pending) => return finish_string_boundary(i, pending, part_origin),
                    }
                }
                '\\' => Some(
                    i.token(|lex| {
                        scan_prefixed_literal_token(lex, part_origin, &prefix, accept_escape_lead)
                    })
                    .expect("a judged prefixed escape lead is accepted"),
                ),
                _ => unreachable!("only a structural literal starter defers a prefix"),
            }
        } else if let Some(close) = i.token(|lex| scan_string_close_witness(lex, mode)) {
            emit_literal_item(&mut i, close, SyntaxKind::StringEnd);
            i.state.finish_node();
            return NormalizedStringLiteralExit::Complete(LineEntry::InLine);
        } else if i
            .token(|lex| Some(lex.remainder().starts_with('%')))
            .expect("the literal source probe is total")
        {
            match emit_string_interpolation(
                i.rb(),
                None,
                &mut part_origin,
                fence,
                &mut interpolation_body,
            ) {
                Ok(()) => continue,
                Err(pending) => return finish_string_boundary(i, pending, part_origin),
            }
        } else {
            i.token(scan_escape_lead)
        };

        if let Some(lead) = lead {
            match emit_string_escape(i.rb(), lead, &mut part_origin, fence, mode) {
                EscapeExit::Continue => continue,
                EscapeExit::AfterLine => {
                    let scan = i
                        .token(|lex| {
                            Some(scan_multiline_literal_item(
                                lex,
                                part_origin,
                                fence,
                                true,
                                |source| string_text_stop(source, mode),
                            ))
                        })
                        .expect("the post-line literal scanner is total");
                    match emit_text_scan(&mut i, scan, &mut part_origin) {
                        Ok(prefix) => {
                            next_prefix = prefix;
                            continue;
                        }
                        Err(pending) => return finish_string_boundary(i, pending, part_origin),
                    }
                }
                EscapeExit::NextPrefix(prefix) => {
                    next_prefix = Some(prefix);
                    continue;
                }
                EscapeExit::Boundary(pending) => {
                    return finish_string_boundary(i, pending, part_origin);
                }
            }
        }

        let scan = i
            .token(|lex| {
                Some(scan_multiline_literal_item(
                    lex,
                    part_origin,
                    fence,
                    false,
                    |source| string_text_stop(source, mode),
                ))
            })
            .expect("the committed literal text scanner is total");
        match emit_text_scan(&mut i, scan, &mut part_origin) {
            Ok(prefix) => next_prefix = prefix,
            Err(pending) => return finish_string_boundary(i, pending, part_origin),
        }
    }
}

fn pending_line_entry(item: &Item) -> LineEntry {
    if item.payload_view().is_eof() || item.payload_view().is_eof_after_trivia_boundary() {
        LineEntry::InLine
    } else {
        LineEntry::PhysicalStart
    }
}

fn emit_string_interpolation<'source, 'operators, 'frozen>(
    mut i: SyntaxIn<'_, 'source, 'operators, 'frozen>,
    prefix: Option<AcceptedQuotePrefix>,
    part_origin: &mut usize,
    fence: Option<&FenceBoundary>,
    interpolation_body: &mut impl for<'a> FnMut(
        SyntaxIn<'a, 'source, 'operators, 'frozen>,
        usize,
        LineEntry,
    ) -> InterpolationBodyExit,
) -> Result<(), Item> {
    i.state.start_node(SyntaxKind::StringInterpolation.into());

    let percent = if let Some(prefix) = prefix {
        i.token(|lex| {
            scan_prefixed_literal_token(lex, *part_origin, &prefix, accept_interpolation_percent)
        })
        .expect("a deferred interpolation prefix has a percent successor")
    } else {
        i.token(scan_interpolation_percent)
            .expect("an interpolation starts at a percent sign")
    };
    advance_item_origin(part_origin, &percent);
    emit_literal_item(&mut i, percent, SyntaxKind::StringInterpolationPercent);

    let scan = i
        .token(|lex| {
            Some(scan_multiline_literal_item(
                lex,
                *part_origin,
                fence,
                false,
                interpolation_format_stop,
            ))
        })
        .expect("the committed interpolation format scanner is total");
    let next_prefix = match emit_literal_scan(
        &mut i,
        scan,
        part_origin,
        SyntaxKind::StringInterpolationFormatText,
    ) {
        Ok(prefix) => prefix,
        Err(pending) => {
            emit_literal_missing(
                i.rb(),
                LiteralRole::StringInterpolationOpenBrace,
                boundary_coordinate(&pending, *part_origin),
            );
            i.state.finish_node();
            return Err(pending);
        }
    };

    let open = if let Some(prefix) = next_prefix {
        i.token(|lex| {
            scan_prefixed_literal_token(lex, *part_origin, &prefix, accept_interpolation_open)
        })
        .expect("a deferred interpolation prefix has an open-brace successor")
    } else {
        i.token(scan_interpolation_open)
            .expect("a completed interpolation format is followed by an open brace")
    };
    advance_item_origin(part_origin, &open);
    emit_literal_item(&mut i, open, SyntaxKind::StringInterpolationOpenBrace);

    let child_start = i
        .token(|lex| Some(lex.remainder()))
        .expect("the interpolation child source probe is total");
    i.state
        .start_node(SyntaxKind::StringInterpolationBody.into());
    let body = interpolation_body(i.rb(), *part_origin, LineEntry::InLine);
    let child_end = i
        .token(|lex| Some(lex.remainder()))
        .expect("the interpolation child source probe is total");
    advance_suffix_origin(part_origin, child_start, child_end);

    match body {
        InterpolationBodyExit::Close {
            mut item,
            line_entry,
        } => {
            let _ = line_entry;
            i.state.finish_node();
            item.emit_all_remaining_leading(&mut *i.state);
            assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RBrace));
            item.emit_payload(&mut *i.state, SyntaxKind::StringInterpolationCloseBrace);
            i.state.finish_node();
            Ok(())
        }
        InterpolationBodyExit::Boundary { item, line_entry } => {
            let _ = line_entry;
            i.state.finish_node();
            emit_literal_missing(
                i.rb(),
                LiteralRole::StringInterpolationCloseBrace,
                boundary_coordinate(&item, *part_origin),
            );
            i.state.finish_node();
            Err(item)
        }
    }
}

fn scan_multiline_literal_item(
    mut i: LexIn,
    part_origin: usize,
    fence: Option<&FenceBoundary>,
    after_line: bool,
    stop: impl Copy + Fn(&str) -> bool,
) -> LiteralScan {
    let part = i.remainder();
    let mut foreign = None;
    let (transition, text) = i.rb().with_str(|mut text| {
        if after_line {
            let coordinate = checked_suffix_coordinate(part, part_origin, text.remainder());
            match literal_line_transition(text.rb(), coordinate, fence, &mut foreign, |source| {
                stop(source)
            }) {
                LiteralLineTransition::Continue => {}
                transition => return transition,
            }
        }

        loop {
            let remainder = text.remainder();
            if remainder.is_empty() {
                let coordinate = checked_suffix_coordinate(part, part_origin, remainder);
                break literal_line_transition(text, coordinate, fence, &mut foreign, |source| {
                    stop(source)
                });
            }

            if stop(remainder) {
                break LiteralLineTransition::Structural(None);
            }
            if remainder.starts_with('"') {
                let run = quote_run(remainder);
                consume_exact_bytes(text.rb(), run);
                continue;
            }

            let character = text
                .next()
                .expect("the literal text cursor is known nonempty");
            let transitioned = match character {
                '\n' => true,
                '\r' if text.remainder().starts_with('\n') => {
                    assert_eq!(text.next(), Some('\n'));
                    true
                }
                _ => false,
            };
            if transitioned {
                let coordinate = checked_suffix_coordinate(part, part_origin, text.remainder());
                match literal_line_transition(text.rb(), coordinate, fence, &mut foreign, stop) {
                    LiteralLineTransition::Continue => {}
                    transition => break transition,
                }
            }
        }
    });

    let accepted = (!text.is_empty()).then(|| literal_text_item(text, part_origin, foreign));
    match transition {
        LiteralLineTransition::Continue => unreachable!("a literal scan ends only at a stop"),
        LiteralLineTransition::Structural(next_prefix) => LiteralScan {
            piece: accepted.map(LiteralPiece::Complete),
            next_prefix,
        },
        LiteralLineTransition::Boundary(pending) => LiteralScan {
            piece: Some(LiteralPiece::Boundary { accepted, pending }),
            next_prefix: None,
        },
    }
}

fn string_text_stop(source: &str, mode: StringMode) -> bool {
    source.starts_with(['\\', '%']) || is_string_close_source(source, mode)
}

fn unicode_error_stop(source: &str, mode: StringMode) -> bool {
    source.starts_with(['}', '%']) || is_string_close_source(source, mode)
}

fn emit_text_scan(
    i: &mut SyntaxIn,
    scan: LiteralScan,
    part_origin: &mut usize,
) -> Result<Option<AcceptedQuotePrefix>, Item> {
    emit_literal_scan(i, scan, part_origin, SyntaxKind::StringText)
}

fn emit_literal_scan(
    i: &mut SyntaxIn,
    scan: LiteralScan,
    part_origin: &mut usize,
    kind: SyntaxKind,
) -> Result<Option<AcceptedQuotePrefix>, Item> {
    let Some(piece) = scan.piece else {
        return Ok(scan.next_prefix);
    };
    match piece {
        LiteralPiece::Complete(item) => {
            *part_origin = part_origin
                .checked_add(literal_item_length(&item))
                .expect("literal source coordinate must fit usize");
            emit_literal_item(i, item, kind);
            Ok(scan.next_prefix)
        }
        LiteralPiece::Boundary { accepted, pending } => {
            if let Some(item) = accepted {
                *part_origin = part_origin
                    .checked_add(literal_item_length(&item))
                    .expect("literal source coordinate must fit usize");
                emit_literal_item(i, item, kind);
            }
            Err(pending)
        }
    }
}

enum EscapeExit {
    Continue,
    AfterLine,
    NextPrefix(AcceptedQuotePrefix),
    Boundary(Item),
}

fn emit_string_escape(
    mut i: SyntaxIn,
    lead: Item,
    part_origin: &mut usize,
    fence: Option<&FenceBoundary>,
    mode: StringMode,
) -> EscapeExit {
    i.state.start_node(SyntaxKind::StringEscape.into());
    advance_item_origin(part_origin, &lead);
    emit_literal_item(&mut i, lead, SyntaxKind::StringEscapeLead);

    if let Some(start) = i.token(scan_unicode_start) {
        advance_item_origin(part_origin, &start);
        emit_literal_item(&mut i, start, SyntaxKind::StringEscapeUnicodeStart);
        return emit_unicode_escape(i, part_origin, fence, mode);
    }

    let at_close = i
        .token(|lex| Some(is_string_close_source(lex.remainder(), mode)))
        .expect("the literal close probe is total");
    let at_eof = i
        .token(|lex| Some(lex.remainder().is_empty()))
        .expect("the literal EOF probe is total");
    if at_close || at_eof {
        emit_literal_missing(i.rb(), LiteralRole::StringEscapeSimpleTarget, *part_origin);
        i.state.finish_node();
        if at_eof {
            return EscapeExit::Boundary(current_boundary_item(i.rb(), *part_origin, fence));
        }
        return EscapeExit::Continue;
    }

    let (target, after_line) = i
        .token(scan_simple_escape_target)
        .expect("a non-sentinel escape target is one scalar");
    advance_item_origin(part_origin, &target);
    emit_literal_item(&mut i, target, SyntaxKind::StringEscapeSimple);
    i.state.finish_node();
    if after_line {
        EscapeExit::AfterLine
    } else {
        EscapeExit::Continue
    }
}

fn emit_unicode_escape(
    mut i: SyntaxIn,
    part_origin: &mut usize,
    fence: Option<&FenceBoundary>,
    mode: StringMode,
) -> EscapeExit {
    let hex = i.token(scan_unicode_hex);
    let has_hex = hex.is_some();
    if let Some(hex) = hex {
        advance_item_origin(part_origin, &hex);
        emit_literal_item(&mut i, hex, SyntaxKind::StringEscapeUnicodeHex);
    }

    if let Some(end) = i.token(scan_unicode_end) {
        if !has_hex {
            emit_literal_missing(i.rb(), LiteralRole::StringEscapeUnicodeHex, *part_origin);
        }
        advance_item_origin(part_origin, &end);
        emit_literal_item(&mut i, end, SyntaxKind::StringEscapeUnicodeEnd);
        i.state.finish_node();
        return EscapeExit::Continue;
    }

    let at_sentinel = i
        .token(|lex| {
            Some(
                lex.remainder().is_empty()
                    || lex.remainder().starts_with('%')
                    || is_string_close_source(lex.remainder(), mode),
            )
        })
        .expect("the unicode sentinel probe is total");
    if at_sentinel {
        if !has_hex {
            emit_literal_missing(i.rb(), LiteralRole::StringEscapeUnicodeHex, *part_origin);
        }
        emit_literal_missing(i.rb(), LiteralRole::StringEscapeUnicodeEnd, *part_origin);
        i.state.finish_node();
        if i.token(|lex| Some(lex.remainder().is_empty()))
            .expect("the unicode EOF probe is total")
        {
            return EscapeExit::Boundary(current_boundary_item(i.rb(), *part_origin, fence));
        }
        return EscapeExit::Continue;
    }

    let (pending, next_prefix) = emit_recovery_error_run(
        i.rb(),
        |run| {
            let scan = run.lexical(|lex| {
                scan_multiline_literal_item(lex, *part_origin, fence, false, |source| {
                    unicode_error_stop(source, mode)
                })
            });
            let (error, pending) = match scan
                .piece
                .expect("unicode recovery starts on one malformed scalar")
            {
                LiteralPiece::Complete(error) => (error, None),
                LiteralPiece::Boundary { accepted, pending } => (
                    accepted.expect("unicode recovery consumes its initial malformed scalar"),
                    Some(pending),
                ),
            };
            advance_item_origin(part_origin, &error);
            let extent = run.emit_item_as(error, *part_origin, SyntaxKind::StringEscapeUnicodeHex);
            run.append_unexpected(UnexpectedSyntax::Token {
                range: extent.recovery_range(),
                category: UnexpectedCategory::OtherCharacter,
            });
            (pending, scan.next_prefix)
        },
        |range, unexpected| {
            literal_draft(
                LiteralRole::StringEscapeUnicodeHex,
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    );
    match pending {
        None => {
            if let Some(prefix) = next_prefix {
                let structural = i
                    .token(|lex| {
                        accepted_prefix_content(lex.remainder(), *part_origin, &prefix)
                            .chars()
                            .next()
                    })
                    .expect("a deferred unicode prefix has a structural successor");
                if structural == '}' {
                    let end = i
                        .token(|lex| {
                            scan_prefixed_literal_token(
                                lex,
                                *part_origin,
                                &prefix,
                                accept_unicode_end,
                            )
                        })
                        .expect("a judged prefixed unicode end is accepted");
                    advance_item_origin(part_origin, &end);
                    emit_literal_item(&mut i, end, SyntaxKind::StringEscapeUnicodeEnd);
                    i.state.finish_node();
                    return EscapeExit::Continue;
                }
                emit_literal_missing(i.rb(), LiteralRole::StringEscapeUnicodeEnd, *part_origin);
                i.state.finish_node();
                return EscapeExit::NextPrefix(prefix);
            }
            if let Some(end) = i.token(scan_unicode_end) {
                advance_item_origin(part_origin, &end);
                emit_literal_item(&mut i, end, SyntaxKind::StringEscapeUnicodeEnd);
            } else {
                emit_literal_missing(i.rb(), LiteralRole::StringEscapeUnicodeEnd, *part_origin);
            }
            i.state.finish_node();
            EscapeExit::Continue
        }
        Some(pending) => {
            emit_literal_missing(
                i.rb(),
                LiteralRole::StringEscapeUnicodeEnd,
                boundary_coordinate(&pending, *part_origin),
            );
            i.state.finish_node();
            EscapeExit::Boundary(pending)
        }
    }
}

fn literal_draft(
    role: LiteralRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        LiteralRole::StringTerminator => ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
        LiteralRole::StringEscapeSimpleTarget => {
            ExpectedSyntax::Literal(LiteralExpected::StringEscapeTarget)
        }
        LiteralRole::StringEscapeUnicodeHex => {
            ExpectedSyntax::Literal(LiteralExpected::UnicodeHexDigit)
        }
        LiteralRole::StringEscapeUnicodeEnd | LiteralRole::StringInterpolationCloseBrace => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace))
        }
        LiteralRole::StringInterpolationOpenBrace => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace))
        }
        _ => unreachable!("Rule recovery belongs to its own owner"),
    };
    let role = GrammarRole::Literal(role);
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

fn emit_literal_missing(i: SyntaxIn, role: LiteralRole, at: usize) {
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        literal_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn boundary_coordinate(item: &Item, origin: usize) -> usize {
    item.payload_view()
        .pending_boundary()
        .map_or_else(|| origin, |boundary| boundary.coordinate())
}

fn finish_string_boundary(
    mut i: SyntaxIn,
    pending: Item,
    origin: usize,
) -> NormalizedStringLiteralExit {
    let line_entry = pending_line_entry(&pending);
    emit_literal_missing(
        i.rb(),
        LiteralRole::StringTerminator,
        boundary_coordinate(&pending, origin),
    );
    i.state.finish_node();
    NormalizedStringLiteralExit::Boundary(pending, line_entry)
}

fn current_boundary_item(
    mut i: SyntaxIn,
    coordinate: usize,
    fence: Option<&FenceBoundary>,
) -> Item {
    i.token(|lex| {
        let mut foreign = None;
        Some(
            match literal_line_transition(lex, coordinate, fence, &mut foreign, |_| false) {
                LiteralLineTransition::Boundary(pending) => pending,
                _ => panic!("the current source is a literal boundary"),
            },
        )
    })
    .expect("the boundary scanner is total")
}

fn scan_escape_lead(mut i: LexIn) -> Option<Item> {
    let (accepted, text) = i.rb().with_str(accept_escape_lead);
    accepted?;
    Some(literal_token(text))
}

fn scan_interpolation_percent(mut i: LexIn) -> Option<Item> {
    let (accepted, text) = i.rb().with_str(accept_interpolation_percent);
    accepted?;
    Some(literal_token(text))
}

fn accept_interpolation_percent(mut i: LexIn) -> Option<()> {
    (i.next()? == '%').then_some(())
}

fn scan_interpolation_open(mut i: LexIn) -> Option<Item> {
    let (accepted, text) = i.rb().with_str(accept_interpolation_open);
    accepted?;
    Some(literal_token(text))
}

fn accept_interpolation_open(mut i: LexIn) -> Option<()> {
    (i.next()? == '{').then_some(())
}

fn accept_escape_lead(mut i: LexIn) -> Option<()> {
    (i.next()? == '\\').then_some(())
}

fn scan_simple_escape_target(mut i: LexIn) -> Option<(Item, bool)> {
    let (character, text) = i.rb().with_str(|mut target| target.next());
    let character = character?;
    Some((literal_token(text), character == '\n'))
}

fn scan_unicode_start(mut i: LexIn) -> Option<Item> {
    i.remainder().starts_with("u{").then_some(())?;
    let (_, text) = i.rb().with_str(|start| consume_exact_bytes(start, 2));
    Some(literal_token(text))
}

fn scan_unicode_hex(mut i: LexIn) -> Option<Item> {
    i.remainder()
        .as_bytes()
        .first()
        .is_some_and(u8::is_ascii_hexdigit)
        .then_some(())?;
    let (_, text) = i.rb().with_str(|mut hex| {
        while hex
            .remainder()
            .as_bytes()
            .first()
            .is_some_and(u8::is_ascii_hexdigit)
        {
            assert!(hex.next().is_some());
        }
    });
    Some(literal_token(text))
}

fn scan_unicode_end(mut i: LexIn) -> Option<Item> {
    let (accepted, text) = i.rb().with_str(accept_unicode_end);
    accepted?;
    Some(literal_token(text))
}

fn accept_unicode_end(mut i: LexIn) -> Option<()> {
    (i.next()? == '}').then_some(())
}

fn advance_item_origin(origin: &mut usize, item: &Item) {
    *origin = origin
        .checked_add(literal_item_length(item))
        .expect("literal source coordinate must fit usize");
}

fn literal_item_length(item: &Item) -> usize {
    item.payload_view()
        .spelling()
        .expect("a literal lexical Item has a token payload")
        .len()
}

fn is_string_close_source(source: &str, mode: StringMode) -> bool {
    let run = quote_run(source);
    match mode {
        StringMode::Normal => run != 0,
        StringMode::Heredoc { quotes } => run == quotes,
    }
}

fn interpolation_format_stop(source: &str) -> bool {
    source.starts_with('{')
}

/// The sole literal physical-line transition: classify without advancing,
/// then consume and record only an accepted body prefix.
fn literal_line_transition(
    i: LexIn,
    coordinate: usize,
    fence: Option<&FenceBoundary>,
    foreign: &mut Option<Vec<ForeignSplit>>,
    starts_new_item: impl FnOnce(&str) -> bool,
) -> LiteralLineTransition {
    let Some(fence) = fence else {
        if i.remainder().is_empty() {
            return LiteralLineTransition::Boundary(Item::plain(
                LeadingTrivia::default(),
                Payload::Eof,
            ));
        }
        return if starts_new_item(i.remainder()) {
            LiteralLineTransition::Structural(None)
        } else {
            LiteralLineTransition::Continue
        };
    };
    match judge_fence_line(i.remainder(), coordinate, fence) {
        FenceLineDecision::Boundary(pending) => LiteralLineTransition::Boundary(Item::plain(
            LeadingTrivia::default(),
            Payload::Boundary(pending),
        )),
        FenceLineDecision::Body {
            prefix: None,
            content,
        } => {
            assert_eq!(content, coordinate);
            if starts_new_item(i.remainder()) {
                LiteralLineTransition::Structural(None)
            } else {
                LiteralLineTransition::Continue
            }
        }
        FenceLineDecision::Body {
            prefix: Some(prefix),
            content,
        } => {
            assert_eq!(prefix.facts.extent.start, coordinate);
            assert_eq!(prefix.content, content);
            assert!(content <= prefix.facts.extent.end);
            let content = accepted_prefix_content(i.remainder(), coordinate, &prefix);
            if starts_new_item(content) {
                LiteralLineTransition::Structural(Some(prefix))
            } else {
                consume_accepted_prefix(i, &prefix, foreign);
                LiteralLineTransition::Continue
            }
        }
    }
}

fn scan_prefixed_literal_token(
    mut i: LexIn,
    part_origin: usize,
    prefix: &AcceptedQuotePrefix,
    accept: impl FnOnce(LexIn) -> Option<()>,
) -> Option<Item> {
    let mut foreign = None;
    let (accepted, text) = i.rb().with_str(|mut token| {
        consume_accepted_prefix(token.rb(), prefix, &mut foreign);
        accept(token)
    });
    accepted?;
    Some(literal_text_item(text, part_origin, foreign))
}

fn consume_accepted_prefix(
    mut i: LexIn,
    prefix: &AcceptedQuotePrefix,
    foreign: &mut Option<Vec<ForeignSplit>>,
) {
    let prefix_length = prefix
        .content
        .checked_sub(prefix.facts.extent.start)
        .expect("accepted body coordinate follows its prefix start");
    PendingFragments::record(
        foreign,
        ForeignSplit::quote_prefix(prefix.facts.extent.start, prefix_length),
    )
    .expect("accepted prefixes stay ordered within one literal Item");
    consume_exact_bytes(i.rb(), prefix_length);
}

fn accepted_prefix_content<'source>(
    source: &'source str,
    coordinate: usize,
    prefix: &AcceptedQuotePrefix,
) -> &'source str {
    assert_eq!(prefix.facts.extent.start, coordinate);
    assert!(prefix.content <= prefix.facts.extent.end);
    let prefix_length = prefix
        .content
        .checked_sub(coordinate)
        .expect("accepted prefix content follows its line coordinate");
    &source[prefix_length..]
}

fn literal_text_item(text: &str, part_origin: usize, foreign: Option<Vec<ForeignSplit>>) -> Item {
    Item::finish(
        PhysicalLeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: text.into(),
        }),
        foreign,
        part_origin,
    )
    .expect("literal fragment coordinates derive from one live suffix")
}

fn literal_token(text: &str) -> Item {
    Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: text.into(),
        }),
    )
}

pub(super) fn quote_run(source: &str) -> usize {
    source.bytes().take_while(|byte| *byte == b'"').count()
}

fn consume_exact_bytes(mut i: LexIn, length: usize) {
    let mut consumed = 0usize;
    while consumed < length {
        consumed = consumed
            .checked_add(
                i.next()
                    .expect("accepted literal source must remain live")
                    .len_utf8(),
            )
            .expect("accepted literal length must fit usize");
    }
    assert_eq!(consumed, length, "accepted source ends at a UTF-8 boundary");
}

fn checked_suffix_coordinate(part: &str, part_origin: usize, suffix: &str) -> usize {
    let consumed = part
        .len()
        .checked_sub(suffix.len())
        .expect("live literal suffix cannot exceed its entry suffix");
    assert_eq!(
        part.as_ptr().wrapping_add(consumed),
        suffix.as_ptr(),
        "live literal input remains a suffix of its entry input"
    );
    part_origin
        .checked_add(consumed)
        .expect("physical literal coordinate must fit usize")
}

fn advance_suffix_origin(origin: &mut usize, start: &str, end: &str) {
    let consumed = start
        .len()
        .checked_sub(end.len())
        .expect("an interpolation child cannot lengthen its live suffix");
    assert_eq!(
        start.as_ptr().wrapping_add(consumed),
        end.as_ptr(),
        "an interpolation child keeps the live input on one source suffix"
    );
    *origin = origin
        .checked_add(consumed)
        .expect("literal source coordinate must fit usize");
}
