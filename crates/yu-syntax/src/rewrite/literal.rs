//! Isolated literal Item construction before expression or Pattern dispatch.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn,
    emit::{emit_literal_item, emit_missing},
    item::{ForeignSplit, Item, LeadingTrivia, Payload, PendingFragments, Token, TokenKind},
    yumark::{AcceptedQuotePrefix, FenceBoundary, FenceLineDecision, judge_fence_line},
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
pub(super) enum StringLiteralExit {
    Complete,
    Boundary(Item),
    InterpolationStop,
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

/// Accepts only a complete literal opener candidate. Two adjacent quotes are
/// the opener and terminator of one normal string; three or more form one
/// heredoc opener.
pub(super) fn scan_string_opener_witness(mut i: LexIn) -> Option<(Item, StringMode)> {
    let run = quote_run(i.remainder());
    let (width, mode) = match run {
        0 => return None,
        1 | 2 => (1, StringMode::Normal),
        quotes => (quotes, StringMode::Heredoc { quotes }),
    };
    let (_, text) = i.rb().with_str(|opener| consume_exact_bytes(opener, width));
    Some((literal_token(text), mode))
}

/// Accepts the mode's terminator without partially consuming a heredoc quote
/// run of a different width.
pub(super) fn scan_string_close_witness(mut i: LexIn, mode: StringMode) -> Option<Item> {
    let (accepted, text) = i.rb().with_str(|close| accept_string_close(close, mode));
    accepted?;
    Some(literal_token(text))
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
pub(super) fn scan_string_text_witness(
    i: LexIn,
    part_origin: usize,
    fence: &FenceBoundary,
    mode: StringMode,
) -> LiteralPiece {
    scan_multiline_literal_item(i, part_origin, fence, mode, false, string_text_stop)
        .piece
        .expect("a text witness is entered only after ruling out a structural starter")
}

/// Builds one isolated non-interpolating StringLiteral. A percent sign is a
/// borrowed construction stop for L3 and causes no terminator recovery here.
pub(super) fn string_literal_witness(
    mut i: RewriteIn,
    opener: Item,
    mode: StringMode,
    mut part_origin: usize,
    fence: &FenceBoundary,
) -> StringLiteralExit {
    i.state.start_node(SyntaxKind::StringLiteral.into());
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
                    return StringLiteralExit::Complete;
                }
                '%' => {
                    i.state.finish_node();
                    return StringLiteralExit::InterpolationStop;
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
            return StringLiteralExit::Complete;
        } else if i
            .token(|lex| Some(lex.remainder().starts_with('%')))
            .expect("the literal source probe is total")
        {
            i.state.finish_node();
            return StringLiteralExit::InterpolationStop;
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
                                mode,
                                true,
                                string_text_stop,
                            ))
                        })
                        .expect("the post-line literal scanner is total");
                    match emit_text_scan(&mut i, scan, &mut part_origin) {
                        Ok(prefix) => {
                            next_prefix = prefix;
                            continue;
                        }
                        Err(pending) => return finish_string_boundary(i, pending),
                    }
                }
                EscapeExit::NextPrefix(prefix) => {
                    next_prefix = Some(prefix);
                    continue;
                }
                EscapeExit::Boundary(pending) => return finish_string_boundary(i, pending),
            }
        }

        let scan = i
            .token(|lex| {
                Some(scan_multiline_literal_item(
                    lex,
                    part_origin,
                    fence,
                    mode,
                    false,
                    string_text_stop,
                ))
            })
            .expect("the committed literal text scanner is total");
        match emit_text_scan(&mut i, scan, &mut part_origin) {
            Ok(prefix) => next_prefix = prefix,
            Err(pending) => return finish_string_boundary(i, pending),
        }
    }
}

fn scan_multiline_literal_item(
    mut i: LexIn,
    part_origin: usize,
    fence: &FenceBoundary,
    mode: StringMode,
    after_line: bool,
    stop: fn(&str, StringMode) -> bool,
) -> LiteralScan {
    let part = i.remainder();
    let mut foreign = None;
    let (transition, text) = i.rb().with_str(|mut text| {
        if after_line {
            let coordinate = checked_suffix_coordinate(part, part_origin, text.remainder());
            match literal_line_transition(text.rb(), coordinate, fence, &mut foreign, |source| {
                stop(source, mode)
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
                    stop(source, mode)
                });
            }

            if stop(remainder, mode) {
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
                match literal_line_transition(
                    text.rb(),
                    coordinate,
                    fence,
                    &mut foreign,
                    |source| stop(source, mode),
                ) {
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
    i: &mut RewriteIn,
    scan: LiteralScan,
    part_origin: &mut usize,
) -> Result<Option<AcceptedQuotePrefix>, Item> {
    let Some(piece) = scan.piece else {
        return Ok(scan.next_prefix);
    };
    match piece {
        LiteralPiece::Complete(item) => {
            *part_origin = part_origin
                .checked_add(literal_item_length(&item))
                .expect("literal source coordinate must fit usize");
            emit_literal_item(i, item, SyntaxKind::StringText);
            Ok(scan.next_prefix)
        }
        LiteralPiece::Boundary { accepted, pending } => {
            if let Some(item) = accepted {
                *part_origin = part_origin
                    .checked_add(literal_item_length(&item))
                    .expect("literal source coordinate must fit usize");
                emit_literal_item(i, item, SyntaxKind::StringText);
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
    mut i: RewriteIn,
    lead: Item,
    part_origin: &mut usize,
    fence: &FenceBoundary,
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
        emit_missing(&mut i, LeadingTrivia::default());
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
    mut i: RewriteIn,
    part_origin: &mut usize,
    fence: &FenceBoundary,
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
            emit_missing(&mut i, LeadingTrivia::default());
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
            emit_missing(&mut i, LeadingTrivia::default());
        }
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        if i.token(|lex| Some(lex.remainder().is_empty()))
            .expect("the unicode EOF probe is total")
        {
            return EscapeExit::Boundary(current_boundary_item(i.rb(), *part_origin, fence));
        }
        return EscapeExit::Continue;
    }

    let scan = i
        .token(|lex| {
            Some(scan_multiline_literal_item(
                lex,
                *part_origin,
                fence,
                mode,
                false,
                unicode_error_stop,
            ))
        })
        .expect("the committed unicode error scanner is total");
    let piece = scan
        .piece
        .expect("unicode recovery starts on one malformed scalar");
    match piece {
        LiteralPiece::Complete(error) => {
            advance_item_origin(part_origin, &error);
            emit_literal_error(&mut i, error, SyntaxKind::StringEscapeUnicodeHex);
            if let Some(prefix) = scan.next_prefix {
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
                emit_missing(&mut i, LeadingTrivia::default());
                i.state.finish_node();
                return EscapeExit::NextPrefix(prefix);
            }
            if let Some(end) = i.token(scan_unicode_end) {
                advance_item_origin(part_origin, &end);
                emit_literal_item(&mut i, end, SyntaxKind::StringEscapeUnicodeEnd);
            } else {
                emit_missing(&mut i, LeadingTrivia::default());
            }
            i.state.finish_node();
            EscapeExit::Continue
        }
        LiteralPiece::Boundary { accepted, pending } => {
            if let Some(error) = accepted {
                advance_item_origin(part_origin, &error);
                emit_literal_error(&mut i, error, SyntaxKind::StringEscapeUnicodeHex);
            }
            emit_missing(&mut i, LeadingTrivia::default());
            i.state.finish_node();
            EscapeExit::Boundary(pending)
        }
    }
}

fn emit_literal_error(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    i.state.start_node(SyntaxKind::Error.into());
    emit_literal_item(i, item, kind);
    i.state.finish_node();
}

fn finish_string_boundary(mut i: RewriteIn, pending: Item) -> StringLiteralExit {
    emit_missing(&mut i, LeadingTrivia::default());
    i.state.finish_node();
    StringLiteralExit::Boundary(pending)
}

fn current_boundary_item(mut i: RewriteIn, coordinate: usize, fence: &FenceBoundary) -> Item {
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
    let Payload::Token(token) = &item.payload else {
        unreachable!("a literal lexical Item has a token payload")
    };
    token.text.len()
}

fn is_string_close_source(source: &str, mode: StringMode) -> bool {
    let run = quote_run(source);
    match mode {
        StringMode::Normal => run != 0,
        StringMode::Heredoc { quotes } => run == quotes,
    }
}

/// The sole literal physical-line transition: classify without advancing,
/// then consume and record only an accepted body prefix.
fn literal_line_transition(
    i: LexIn,
    coordinate: usize,
    fence: &FenceBoundary,
    foreign: &mut Option<Vec<ForeignSplit>>,
    starts_new_item: impl FnOnce(&str) -> bool,
) -> LiteralLineTransition {
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
            assert_eq!(prefix.facts.extent.end, content);
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
        .facts
        .extent
        .end
        .checked_sub(prefix.facts.extent.start)
        .expect("accepted prefix extent must be ordered");
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
    assert_eq!(prefix.facts.extent.end, prefix.content);
    let prefix_length = prefix
        .content
        .checked_sub(coordinate)
        .expect("accepted prefix content follows its line coordinate");
    &source[prefix_length..]
}

fn literal_text_item(text: &str, part_origin: usize, foreign: Option<Vec<ForeignSplit>>) -> Item {
    let fragments = PendingFragments::finish(foreign, part_origin, text.len())
        .expect("literal fragment coordinates derive from one live suffix");
    let mut item = literal_token(text);
    if let Some(fragments) = fragments {
        item.with_fragments(fragments)
            .expect("one literal carrier covers its complete token payload");
    }
    item
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

fn quote_run(source: &str) -> usize {
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
