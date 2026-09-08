//! L7 RuleLiteral construction shared by Expression and Pattern owners.

use crate::ambient_claim::AmbientClaimContext;
#[cfg(test)]
use crate::ambient_claim::AmbientClaimView;
use unicode_ident::is_xid_continue;

use crate::literal::*;
use crate::rule::{
    RuleLiteralSequenceExit, emit_rule_missing, rule_literal_sequence_normalized, rule_recovery_at,
};

#[derive(Debug, Eq, PartialEq)]
#[cfg(test)]
pub(crate) enum RuleLiteralExit {
    Complete,
    Boundary(Item),
}

pub(crate) enum NormalizedRuleLiteralExit {
    Complete(LineEntry),
    Boundary(Item, LineEntry),
}

#[cfg(test)]
pub(crate) enum PatternLiteralOpener {
    Rule(Item),
    String(Item, StringMode),
}

#[cfg(test)]
pub(crate) fn scan_expression_rule_literal_opener_witness(mut i: LexIn) -> Option<Item> {
    let token = i.token(scan_expression_rule_literal_opener_token)?;
    Some(Item::plain(LeadingTrivia::default(), Payload::Token(token)))
}

pub(crate) fn scan_expression_rule_literal_opener_token(mut i: LexIn) -> Option<Token> {
    i.remainder().starts_with("~\"").then_some(())?;
    let (_, text) = i.rb().with_str(|opener| consume_exact_bytes(opener, 2));
    Some(Token {
        kind: TokenKind::Unknown,
        text: text.into(),
    })
}

#[cfg(test)]
pub(crate) fn scan_pattern_literal_opener_witness(mut i: LexIn) -> Option<PatternLiteralOpener> {
    let token = i.token(scan_pattern_literal_opener_token)?;
    if token.text.len() == 1 {
        return Some(PatternLiteralOpener::Rule(Item::plain(
            LeadingTrivia::default(),
            Payload::Token(token),
        )));
    }
    let mode = match token.text.len() {
        quotes @ 3.. => StringMode::Heredoc { quotes },
        _ => unreachable!("a Pattern StringLiteral opener is a heredoc quote run"),
    };
    Some(PatternLiteralOpener::String(
        Item::plain(LeadingTrivia::default(), Payload::Token(token)),
        mode,
    ))
}

pub(crate) fn scan_pattern_literal_opener_token(mut i: LexIn) -> Option<Token> {
    let run = quote_run(i.remainder());
    match run {
        1 => {
            let (_, text) = i.rb().with_str(|opener| consume_exact_bytes(opener, 1));
            Some(Token {
                kind: TokenKind::Unknown,
                text: text.into(),
            })
        }
        3.. => i.token(scan_string_opener_token).map(|(token, _)| token),
        _ => None,
    }
}

/// Builds the non-interpolation portion of an isolated RuleLiteral. A plain
/// `{` is completed as the exact next Item and handed to the L7 owner.
#[cfg(test)]
pub(crate) fn rule_literal_witness(
    i: SyntaxIn,
    opener: Item,
    part_origin: usize,
    fence: &FenceBoundary,
) -> RuleLiteralExit {
    match rule_literal_normalized(
        i,
        opener,
        part_origin,
        LineEntry::InLine,
        Some(fence),
        Some(AmbientClaimView::root_statement(0)).into(),
    ) {
        NormalizedRuleLiteralExit::Complete(_) => RuleLiteralExit::Complete,
        NormalizedRuleLiteralExit::Boundary(item, _) => RuleLiteralExit::Boundary(item),
    }
}

pub(crate) fn rule_literal_normalized(
    mut i: SyntaxIn,
    opener: Item,
    mut part_origin: usize,
    _line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedRuleLiteralExit {
    i.state.start_node(SyntaxKind::RuleLiteral.into());
    let mut opener = opener;
    opener.emit_all_remaining_leading(&mut *i.state);
    emit_literal_item(&mut i, opener, SyntaxKind::RuleLiteralStart);
    let mut next_prefix = None;

    loop {
        let structural = if let Some(prefix) = next_prefix.take() {
            let next = i
                .token(|lex| {
                    accepted_prefix_content(lex.remainder(), part_origin, &prefix)
                        .chars()
                        .next()
                })
                .expect("a deferred RuleLiteral prefix has a structural successor");
            Some((next, Some(prefix)))
        } else {
            i.token(|lex| {
                Some(
                    lex.remainder()
                        .chars()
                        .next()
                        .filter(|next| matches!(next, '"' | ':' | '{')),
                )
            })
            .expect("the RuleLiteral structural probe is total")
            .map(|next| (next, None))
        };

        match structural {
            Some(('"', prefix)) => {
                let end = i
                    .token(|lex| Some(scan_rule_literal_structural(lex, part_origin, prefix, '"')))
                    .expect("checked RuleLiteral terminator");
                advance_item_origin(&mut part_origin, &end);
                emit_literal_item(&mut i, end, SyntaxKind::RuleLiteralEnd);
                i.state.finish_node();
                return NormalizedRuleLiteralExit::Complete(LineEntry::InLine);
            }
            Some(('{', prefix)) => {
                let open = i
                    .token(|lex| Some(scan_rule_literal_structural(lex, part_origin, prefix, '{')))
                    .expect("checked RuleLiteral interpolation opener");
                advance_item_origin(&mut part_origin, &open);
                i.state
                    .start_node(SyntaxKind::RuleLiteralInterpolation.into());
                emit_literal_item(&mut i, open, SyntaxKind::RuleLiteralOpenBrace);
                match rule_literal_sequence_normalized(
                    i.rb(),
                    &mut part_origin,
                    LineEntry::InLine,
                    fence,
                    ambient,
                ) {
                    RuleLiteralSequenceExit::Close(mut close, _) => {
                        close.emit_all_remaining_leading(&mut *i.state);
                        debug_assert_eq!(
                            close.payload_view().token_kind(),
                            Some(TokenKind::RBrace)
                        );
                        close.emit_payload(&mut *i.state, SyntaxKind::RuleLiteralCloseBrace);
                        i.state.finish_node();
                        continue;
                    }
                    RuleLiteralSequenceExit::OuterTerminator(mut end, line_entry) => {
                        end.emit_all_remaining_leading(&mut *i.state);
                        emit_rule_missing(
                            i.rb(),
                            LiteralRole::RuleLiteralInterpolationCloseBrace,
                            rule_recovery_at(&end, part_origin),
                        );
                        i.state.finish_node();
                        debug_assert_eq!(end.payload_view().spelling(), Some("\""));
                        end.emit_payload(&mut *i.state, SyntaxKind::RuleLiteralEnd);
                        i.state.finish_node();
                        return NormalizedRuleLiteralExit::Complete(line_entry);
                    }
                    RuleLiteralSequenceExit::Boundary(pending, _) => {
                        emit_rule_missing(
                            i.rb(),
                            LiteralRole::RuleLiteralInterpolationCloseBrace,
                            rule_recovery_at(&pending, part_origin),
                        );
                        i.state.finish_node();
                        return finish_rule_literal_boundary(i, pending, part_origin);
                    }
                }
            }
            Some((':', prefix)) => {
                let colon = i
                    .token(|lex| Some(scan_rule_literal_structural(lex, part_origin, prefix, ':')))
                    .expect("checked RuleLiteral capture colon");
                advance_item_origin(&mut part_origin, &colon);
                match emit_rule_lazy_capture(i.rb(), colon, &mut part_origin, fence) {
                    Ok(()) => continue,
                    Err(pending) => return finish_rule_literal_boundary(i, pending, part_origin),
                }
            }
            Some(_) => unreachable!("RuleLiteral has only three structural starters"),
            None => {}
        }

        let scan = i
            .token(|lex| {
                Some(scan_multiline_literal_item(
                    lex,
                    part_origin,
                    fence,
                    false,
                    rule_literal_text_stop,
                ))
            })
            .expect("the committed RuleLiteral text scanner is total");
        match emit_literal_scan(&mut i, scan, &mut part_origin, SyntaxKind::RuleLiteralText) {
            Ok(prefix) => next_prefix = prefix,
            Err(pending) => return finish_rule_literal_boundary(i, pending, part_origin),
        }
    }
}

fn emit_rule_lazy_capture(
    mut i: SyntaxIn,
    colon: Item,
    part_origin: &mut usize,
    fence: Option<&FenceBoundary>,
) -> Result<(), Item> {
    i.state.start_node(SyntaxKind::RuleLazyCapture.into());
    emit_literal_item(&mut i, colon, SyntaxKind::RuleLiteralColon);

    if i.token(|lex| Some(lex.remainder().starts_with('{')))
        .expect("the RuleLazyCapture opener probe is total")
    {
        let open = i
            .token(|lex| scan_plain_literal_character(lex, '{'))
            .expect("checked braced RuleLazyCapture opener");
        advance_item_origin(part_origin, &open);
        emit_literal_item(&mut i, open, SyntaxKind::RuleLiteralOpenBrace);

        let scan = i
            .token(|lex| {
                Some(scan_multiline_literal_item(
                    lex,
                    *part_origin,
                    fence,
                    false,
                    |source| source.starts_with('}'),
                ))
            })
            .expect("the committed RuleCapture text scanner is total");
        let prefix = match emit_literal_scan(&mut i, scan, part_origin, SyntaxKind::RuleLiteralText)
        {
            Ok(prefix) => prefix,
            Err(pending) => {
                emit_rule_missing(
                    i.rb(),
                    LiteralRole::RuleLazyCaptureCloseBrace,
                    rule_recovery_at(&pending, *part_origin),
                );
                i.state.finish_node();
                return Err(pending);
            }
        };

        let close = if let Some(prefix) = prefix {
            i.token(|lex| {
                Some(scan_rule_literal_structural(
                    lex,
                    *part_origin,
                    Some(prefix),
                    '}',
                ))
            })
            .expect("judged RuleLazyCapture close")
        } else {
            i.token(|lex| scan_plain_literal_character(lex, '}'))
                .expect("completed RuleCapture text is followed by its close")
        };
        advance_item_origin(part_origin, &close);
        emit_literal_item(&mut i, close, SyntaxKind::RuleLiteralCloseBrace);
        i.state.finish_node();
        return Ok(());
    }

    if let Some(name) = i.token(scan_rule_capture_name) {
        advance_item_origin(part_origin, &name);
        emit_literal_item(&mut i, name, SyntaxKind::RuleLiteralText);
    } else {
        emit_rule_missing(i.rb(), LiteralRole::RuleLazyCaptureName, *part_origin);
    }
    i.state.finish_node();
    Ok(())
}

fn scan_rule_capture_name(mut i: LexIn) -> Option<Item> {
    let (accepted, text) = i.rb().with_str(|mut name| {
        is_xid_continue(name.next()?).then_some(())?;
        while name
            .token(|mut next: LexIn| is_xid_continue(next.next()?).then_some(()))
            .is_some()
        {}
        Some(())
    });
    accepted?;
    Some(literal_token(text))
}

fn scan_rule_literal_structural(
    mut i: LexIn,
    part_origin: usize,
    prefix: Option<AcceptedQuotePrefix>,
    expected: char,
) -> Item {
    if let Some(prefix) = prefix {
        return i
            .token(|lex| {
                scan_prefixed_literal_token(lex, part_origin, &prefix, |token| {
                    accept_literal_character(token, expected)
                })
            })
            .expect("a judged RuleLiteral prefix has the expected successor");
    }
    i.token(|lex| scan_plain_literal_character(lex, expected))
        .expect("checked RuleLiteral structural successor")
}

fn scan_plain_literal_character(mut i: LexIn, expected: char) -> Option<Item> {
    let (accepted, text) = i
        .rb()
        .with_str(|token| accept_literal_character(token, expected));
    accepted?;
    Some(literal_token(text))
}

fn accept_literal_character(mut i: LexIn, expected: char) -> Option<()> {
    (i.next()? == expected).then_some(())
}

fn rule_literal_text_stop(source: &str) -> bool {
    source.starts_with(['"', ':', '{'])
}

fn finish_rule_literal_boundary(
    mut i: SyntaxIn,
    pending: Item,
    origin: usize,
) -> NormalizedRuleLiteralExit {
    let line_entry = pending_line_entry(&pending);
    emit_rule_missing(
        i.rb(),
        LiteralRole::RuleLiteralTerminator,
        rule_recovery_at(&pending, origin),
    );
    i.state.finish_node();
    NormalizedRuleLiteralExit::Boundary(pending, line_entry)
}
