//! L5 RuleLiteral construction shared by expression and Pattern witnesses.

use unicode_ident::is_xid_continue;

use super::*;

#[derive(Debug, Eq, PartialEq)]
pub(in crate::rewrite) enum RuleLiteralExit {
    Complete,
    Boundary(Item),
    DeferredInterpolation(Item),
}

pub(in crate::rewrite) enum PatternLiteralOpener {
    Rule(Item),
    String(Item, StringMode),
}

pub(in crate::rewrite) fn scan_expression_rule_literal_opener_witness(
    mut i: LexIn,
) -> Option<Item> {
    i.remainder().starts_with("~\"").then_some(())?;
    let (_, text) = i.rb().with_str(|opener| consume_exact_bytes(opener, 2));
    Some(literal_token(text))
}

pub(in crate::rewrite) fn scan_pattern_literal_opener_witness(
    mut i: LexIn,
) -> Option<PatternLiteralOpener> {
    let run = quote_run(i.remainder());
    if run == 0 {
        return None;
    }
    if run >= 3 {
        let (opener, mode) = scan_string_opener_witness(i)?;
        return Some(PatternLiteralOpener::String(opener, mode));
    }
    let (_, text) = i.rb().with_str(|opener| consume_exact_bytes(opener, 1));
    Some(PatternLiteralOpener::Rule(literal_token(text)))
}

/// Builds the non-interpolation portion of an isolated RuleLiteral. A plain
/// `{` is completed as the exact next Item and handed to the L7 owner.
pub(in crate::rewrite) fn rule_literal_witness(
    mut i: RewriteIn,
    opener: Item,
    mut part_origin: usize,
    fence: &FenceBoundary,
) -> RuleLiteralExit {
    i.state.start_node(SyntaxKind::RuleLiteral.into());
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
                return RuleLiteralExit::Complete;
            }
            Some(('{', prefix)) => {
                let open = i
                    .token(|lex| Some(scan_rule_literal_structural(lex, part_origin, prefix, '{')))
                    .expect("checked RuleLiteral interpolation opener");
                i.state.finish_node();
                return RuleLiteralExit::DeferredInterpolation(open);
            }
            Some((':', prefix)) => {
                let colon = i
                    .token(|lex| Some(scan_rule_literal_structural(lex, part_origin, prefix, ':')))
                    .expect("checked RuleLiteral capture colon");
                advance_item_origin(&mut part_origin, &colon);
                match emit_rule_lazy_capture(i.rb(), colon, &mut part_origin, fence) {
                    Ok(()) => continue,
                    Err(pending) => return finish_rule_literal_boundary(i, pending),
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
            Err(pending) => return finish_rule_literal_boundary(i, pending),
        }
    }
}

fn emit_rule_lazy_capture(
    mut i: RewriteIn,
    colon: Item,
    part_origin: &mut usize,
    fence: &FenceBoundary,
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
                emit_missing(&mut i, LeadingTrivia::default());
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
        emit_missing(&mut i, LeadingTrivia::default());
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

fn finish_rule_literal_boundary(mut i: RewriteIn, pending: Item) -> RuleLiteralExit {
    emit_missing(&mut i, LeadingTrivia::default());
    i.state.finish_node();
    RuleLiteralExit::Boundary(pending)
}
