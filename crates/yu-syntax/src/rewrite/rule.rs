//! Isolated RuleSequenceCore construction before RuleExpression dispatch.

use reborrow_generic::Reborrow as _;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn,
    emit::{emit_error_item, emit_leading_trivia},
    item::{
        ForeignKind, Item, ItemTextPart, LeadingTrivia, Payload, Token, TokenKind, Trivia,
        TriviaKind,
    },
    lexer::{
        scan_exact_equals, scan_integer, scan_operator_shaped_unknown, scan_ordinary_trivia_part,
        scan_punctuation, scan_unknown,
    },
};

#[cfg(test)]
use super::{
    item::{ForeignSplit, PendingBoundary, PendingFragments},
    lexer::{FencedBlockComment, scan_block_comment_fenced_witness, scan_fenced_prior_trivia_part},
    yumark::{FenceBoundary, FenceLineDecision, judge_fence_line},
};

#[derive(Clone, Copy)]
enum RuleFrame {
    Body,
    Parenthesis,
}

#[derive(Debug, Eq, PartialEq)]
pub(super) enum RuleWitnessExit {
    Complete,
    Returned(Item),
    Deferred(Item),
}

enum SequenceExit {
    Stop(Item),
    Deferred(Item),
}

enum ItemExit {
    Continue(Item),
    Deferred(Item),
}

/// Builds one isolated RuleBody from an already accepted `{` and one current
/// Item. It does not recognize `rule` or enter production expression dispatch.
pub(super) fn rule_body_witness(mut i: RewriteIn, opener: Item, current: Item) -> RuleWitnessExit {
    debug_assert!(is_token(&opener, TokenKind::LBrace));
    i.state.start_node(SyntaxKind::RuleBody.into());
    emit_item_as(&mut i, opener, SyntaxKind::LBrace);

    let exit = rule_alternation(i.rb(), current, RuleFrame::Body);
    let exit = match exit {
        SequenceExit::Stop(close) if is_token(&close, TokenKind::RBrace) => {
            emit_item_as(&mut i, close, SyntaxKind::RBrace);
            RuleWitnessExit::Complete
        }
        SequenceExit::Stop(pending) => {
            emit_missing(&mut i);
            RuleWitnessExit::Returned(pending)
        }
        SequenceExit::Deferred(item) => RuleWitnessExit::Deferred(item),
    };
    i.state.finish_node();
    exit
}

/// Scans one rule-local current Item. Newlines are payload Items so the
/// alternatives owner can consume each physical separator without rewriting
/// the next Item's leading trivia.
pub(super) fn scan_rule_item_witness(i: LexIn) -> Option<Item> {
    scan_rule_item(i)
}

/// Reads the sole successor after a contextual `rule` candidate. The result
/// is still one ordinary current Item: accepted trivia and quote-prefix
/// fragments stay attached to it, while a fence decision is its exact payload.
#[cfg(test)]
pub(super) fn scan_rule_introducer_successor_witness(
    mut i: LexIn,
    origin: usize,
    fence: &FenceBoundary,
) -> Item {
    let source = i.remainder();
    let mut leading = Vec::new();
    let mut foreign = None;

    let payload = loop {
        if i.remainder().starts_with("/*") {
            let part_origin = origin + suffix_distance(source, i.remainder());
            match i
                .token(|comment| {
                    scan_block_comment_fenced_witness(comment, part_origin, fence, &mut foreign)
                })
                .expect("checked fenced block-comment opener")
            {
                FencedBlockComment::Complete(comment) => leading.push(comment),
                FencedBlockComment::Boundary { accepted, pending } => {
                    leading.push(accepted);
                    break Payload::Boundary(pending);
                }
            }
            continue;
        }
        if let Some(trivia) = i.token(scan_fenced_prior_trivia_part) {
            let is_newline = trivia.kind == TriviaKind::Newline;
            leading.push(trivia);
            if is_newline {
                if let Some(boundary) = introducer_line_transition(
                    i.rb(),
                    source,
                    origin,
                    fence,
                    &mut foreign,
                    &mut leading,
                ) {
                    break Payload::Boundary(boundary);
                }
            }
            continue;
        }

        break if i.remainder().is_empty() {
            Payload::Eof
        } else {
            Payload::Token(
                i.token(scan_rule_token)
                    .expect("a nonempty rule successor has one lexical token"),
            )
        };
    };

    let physical_length = suffix_distance(source, i.remainder());
    let mut item = Item::plain(LeadingTrivia(leading.into_boxed_slice()), payload);
    if let Some(fragments) = PendingFragments::finish(foreign, origin, physical_length)
        .expect("accepted introducer prefixes remain inside the current Item")
    {
        item.with_fragments(fragments)
            .expect("the introducer carrier covers exactly one current Item");
    }
    item
}

fn rule_alternation(mut i: RewriteIn, mut current: Item, frame: RuleFrame) -> SequenceExit {
    i.state.start_node(SyntaxKind::RuleAlternation.into());
    loop {
        i.state.start_node(SyntaxKind::RuleSequence.into());
        let exit = rule_sequence(i.rb(), current, frame);
        i.state.finish_node();

        match exit {
            SequenceExit::Deferred(item) => {
                i.state.finish_node();
                return SequenceExit::Deferred(item);
            }
            SequenceExit::Stop(item) if is_separator(&item, frame) => {
                emit_separator(&mut i, item);
                current = next_rule_item(i.rb());
            }
            SequenceExit::Stop(item) => {
                i.state.finish_node();
                return SequenceExit::Stop(item);
            }
        }
    }
}

fn rule_sequence(mut i: RewriteIn, mut current: Item, frame: RuleFrame) -> SequenceExit {
    loop {
        if is_rule_stop(&current, frame) {
            return SequenceExit::Stop(current);
        }
        if is_deferred_atom(&current) {
            return SequenceExit::Deferred(current);
        }
        if is_rule_atom_start(&current) {
            match rule_item(i.rb(), current, frame) {
                ItemExit::Continue(next) => current = next,
                ItemExit::Deferred(item) => return SequenceExit::Deferred(item),
            }
            continue;
        }

        emit_unexpected(&mut i, current);
        current = next_rule_item(i.rb());
    }
}

fn rule_item(mut i: RewriteIn, current: Item, frame: RuleFrame) -> ItemExit {
    i.state.start_node(SyntaxKind::RuleItem.into());
    let mut current = if is_token(&current, TokenKind::LParen) {
        emit_item_as(&mut i, current, SyntaxKind::LParen);
        let nested_current = next_rule_item(i.rb());
        let nested = rule_alternation(i.rb(), nested_current, RuleFrame::Parenthesis);
        match nested {
            SequenceExit::Stop(close) if is_token(&close, TokenKind::RParen) => {
                emit_item_as(&mut i, close, SyntaxKind::RParen);
                next_rule_item(i.rb())
            }
            SequenceExit::Stop(pending) => {
                emit_missing(&mut i);
                i.state.finish_node();
                return ItemExit::Continue(pending);
            }
            SequenceExit::Deferred(item) => {
                i.state.finish_node();
                return ItemExit::Deferred(item);
            }
        }
    } else {
        emit_rule_atom(&mut i, current);
        next_rule_item(i.rb())
    };

    loop {
        if is_token(&current, TokenKind::Equals) {
            i.state.start_node(SyntaxKind::RuleCapture.into());
            emit_item_as(&mut i, current, SyntaxKind::Equals);
            let right = next_rule_item(i.rb());
            match required_rule_item(i.rb(), right, frame) {
                ItemExit::Continue(next) => {
                    i.state.finish_node();
                    i.state.finish_node();
                    return ItemExit::Continue(next);
                }
                ItemExit::Deferred(item) => {
                    i.state.finish_node();
                    i.state.finish_node();
                    return ItemExit::Deferred(item);
                }
            }
        }

        if !current.leading.0.is_empty() {
            i.state.finish_node();
            return ItemExit::Continue(current);
        }

        if is_quantifier(&current) {
            i.state.start_node(SyntaxKind::RuleQuantifier.into());
            emit_item_as(&mut i, current, SyntaxKind::RuleQuantifierToken);
            i.state.finish_node();
            current = next_rule_item(i.rb());
            continue;
        }

        if is_token(&current, TokenKind::Dot) || is_token(&current, TokenKind::PathSeparator) {
            current = rule_named_postfix(i.rb(), current, frame);
            continue;
        }

        if is_token(&current, TokenKind::LParen) || is_token(&current, TokenKind::LBracket) {
            i.state.finish_node();
            return ItemExit::Deferred(current);
        }

        i.state.finish_node();
        return ItemExit::Continue(current);
    }
}

fn required_rule_item(mut i: RewriteIn, mut current: Item, frame: RuleFrame) -> ItemExit {
    loop {
        if is_rule_stop(&current, frame) {
            emit_missing(&mut i);
            return ItemExit::Continue(current);
        }
        if is_deferred_atom(&current) {
            return ItemExit::Deferred(current);
        }
        if is_rule_atom_start(&current) {
            return rule_item(i, current, frame);
        }
        emit_unexpected(&mut i, current);
        current = next_rule_item(i.rb());
    }
}

fn rule_named_postfix(mut i: RewriteIn, introducer: Item, frame: RuleFrame) -> Item {
    let (node, missing) = if is_token(&introducer, TokenKind::Dot) {
        (SyntaxKind::RuleField, SyntaxKind::Dot)
    } else {
        (SyntaxKind::RulePath, SyntaxKind::ColonColon)
    };
    i.state.start_node(node.into());
    emit_item_as(&mut i, introducer, missing);

    let current = next_rule_item(i.rb());
    if is_rule_identifier(&current) && !is_stop_keyword(&current) {
        emit_item_as(&mut i, current, SyntaxKind::Identifier);
        let next = next_rule_item(i.rb());
        i.state.finish_node();
        return next;
    }

    if is_rule_stop(&current, frame) {
        emit_missing(&mut i);
        i.state.finish_node();
        return current;
    }

    emit_unexpected(&mut i, current);
    let next = next_rule_item(i.rb());
    i.state.finish_node();
    next
}

fn next_rule_item(mut i: RewriteIn) -> Item {
    i.token(scan_rule_item)
        .expect("the rule current-item scanner is total")
}

fn scan_rule_item(mut i: LexIn) -> Option<Item> {
    let mut leading = Vec::new();
    while let Some(trivia) = i.token(scan_inline_trivia) {
        leading.push(trivia);
    }
    let payload = if i.remainder().is_empty() {
        Payload::Eof
    } else {
        Payload::Token(i.token(scan_rule_token)?)
    };
    Some(Item::plain(
        LeadingTrivia(leading.into_boxed_slice()),
        payload,
    ))
}

fn scan_inline_trivia(i: LexIn) -> Option<Trivia> {
    if i.remainder().starts_with(['\n', '\r']) {
        return None;
    }
    scan_ordinary_trivia_part(i)
}

fn scan_rule_token(mut i: LexIn) -> Option<Token> {
    if let Some(token) = i.token(scan_rule_sigil_identifier) {
        return Some(token);
    }
    if let Some(token) = i.token(scan_rule_identifier) {
        return Some(token);
    }
    if let Some(token) = i.token(scan_integer) {
        return Some(token);
    }
    i.token(scan_rule_fixed)
        .or_else(|| i.token(scan_exact_equals))
        .or_else(|| i.token(scan_punctuation))
        .or_else(|| i.token(scan_operator_shaped_unknown))
        .or_else(|| i.token(scan_unknown))
}

fn scan_rule_fixed(mut i: LexIn) -> Option<Token> {
    let (kind, width) = if i.remainder().starts_with("..") {
        (TokenKind::DotDot, 2)
    } else if i.remainder().starts_with("*?") || i.remainder().starts_with("+?") {
        (TokenKind::Unknown, 2)
    } else if i.remainder().starts_with("\r\n") {
        (TokenKind::Unknown, 2)
    } else {
        match i.remainder().chars().next()? {
            '|' => (TokenKind::Pipe, 1),
            '\n' | '*' | '+' | '?' => (TokenKind::Unknown, 1),
            _ => return None,
        }
    };
    let (_, text) = i.rb().with_str(|token| consume_bytes(token, width));
    Some(Token {
        kind,
        text: text.into(),
    })
}

fn scan_rule_identifier(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(scan_rule_identifier_text);
    accepted?;
    Some(Token {
        kind: TokenKind::Identifier,
        text: text.into(),
    })
}

fn scan_rule_sigil_identifier(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut sigil| {
        matches!(sigil.next()?, '$' | '&' | '_' | '\'').then_some(())?;
        scan_rule_identifier_text(sigil.rb())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::SigilIdentifier,
        text: text.into(),
    })
}

fn scan_rule_identifier_text(mut i: LexIn) -> Option<()> {
    let first = i.next()?;
    if first == '_' {
        return Some(());
    }
    is_xid_start(first).then_some(())?;
    while i
        .token(|mut continuation: LexIn| is_xid_continue(continuation.next()?).then_some(()))
        .is_some()
    {}
    Some(())
}

#[cfg(test)]
fn introducer_line_transition(
    mut i: LexIn,
    source: &str,
    origin: usize,
    fence: &FenceBoundary,
    foreign: &mut Option<Vec<ForeignSplit>>,
    leading: &mut Vec<Trivia>,
) -> Option<PendingBoundary> {
    let coordinate = origin + suffix_distance(source, i.remainder());
    match judge_fence_line(i.remainder(), coordinate, fence) {
        FenceLineDecision::Boundary(boundary) => Some(boundary),
        FenceLineDecision::Body { prefix: None, .. } => None,
        FenceLineDecision::Body {
            prefix: Some(prefix),
            content,
        } => {
            let length = content - coordinate;
            let start = i.remainder();
            consume_bytes(i.rb(), length).expect("the judged prefix is live source text");
            let text = consumed_prefix(start, i.remainder());
            PendingFragments::record(
                foreign,
                ForeignSplit::quote_prefix(prefix.facts.extent.start, length),
            )
            .expect("fence judge returns ordered prefix ranges");
            if !leading.is_empty() {
                leading.push(Trivia {
                    kind: TriviaKind::Whitespace,
                    text: text.into(),
                });
            }
            None
        }
    }
}

fn emit_rule_atom(i: &mut RewriteIn, item: Item) {
    let kind = match &item.payload {
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            ..
        }) => SyntaxKind::Identifier,
        Payload::Token(Token {
            kind: TokenKind::SigilIdentifier,
            ..
        }) => SyntaxKind::SigilIdentifier,
        Payload::Token(Token {
            kind: TokenKind::Integer,
            ..
        }) => SyntaxKind::Integer,
        Payload::Token(Token {
            kind: TokenKind::DotDot,
            ..
        }) => SyntaxKind::DotDot,
        _ => unreachable!("a RuleItem starts with a RuleSequenceCore atom"),
    };
    emit_item_as(i, item, kind);
}

fn emit_separator(i: &mut RewriteIn, item: Item) {
    let kind = if is_token(&item, TokenKind::Pipe) {
        SyntaxKind::Pipe
    } else if is_token(&item, TokenKind::Comma) {
        SyntaxKind::Comma
    } else {
        SyntaxKind::Newline
    };
    emit_item_as(i, item, kind);
}

fn emit_unexpected(i: &mut RewriteIn, item: Item) {
    emit_error_item(i, item);
}

fn emit_missing(i: &mut RewriteIn) {
    i.state.start_node(SyntaxKind::Missing.into());
    i.state.finish_node();
}

fn emit_item_as(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    if item.fragments().is_some() {
        for part in item
            .fragmented_parts()
            .expect("a segmented rule Item retains its carrier")
        {
            let ordinary = match part.kind {
                ItemTextPart::LeadingTrivia(index) => {
                    trivia_syntax_kind(item.leading.0[index].kind)
                }
                ItemTextPart::PayloadToken => kind,
                ItemTextPart::PayloadOperator => {
                    unreachable!("RuleSequenceCore does not accept operator payloads")
                }
            };
            let mut cursor = 0;
            for split in part.foreign {
                let start = split.offset - part.physical.start;
                let end = start + split.length;
                if cursor < start {
                    i.state.token(ordinary.into(), &part.text[cursor..start]);
                }
                let foreign = match split.kind {
                    ForeignKind::YmQuotePrefix => SyntaxKind::YmQuotePrefix,
                };
                i.state.token(foreign.into(), &part.text[start..end]);
                cursor = end;
            }
            if cursor < part.text.len() {
                i.state.token(ordinary.into(), &part.text[cursor..]);
            }
        }
        return;
    }

    emit_leading_trivia(i, &item.leading);
    let Payload::Token(token) = item.payload else {
        unreachable!("only an accepted lexical token can be emitted")
    };
    i.state.token(kind.into(), &token.text);
}

fn trivia_syntax_kind(kind: TriviaKind) -> SyntaxKind {
    match kind {
        TriviaKind::Whitespace => SyntaxKind::Whitespace,
        TriviaKind::Newline => SyntaxKind::Newline,
        TriviaKind::LineComment => SyntaxKind::LineComment,
        TriviaKind::BlockComment => SyntaxKind::BlockComment,
    }
}

fn is_rule_atom_start(item: &Item) -> bool {
    (is_rule_identifier(item) && !is_stop_keyword(item))
        || is_token(item, TokenKind::SigilIdentifier)
        || is_token(item, TokenKind::Integer)
        || is_token(item, TokenKind::DotDot)
        || is_token(item, TokenKind::LParen)
}

fn is_deferred_atom(item: &Item) -> bool {
    is_token(item, TokenKind::LBracket) || token_text(item).is_some_and(|text| text == "\"")
}

fn is_rule_identifier(item: &Item) -> bool {
    is_token(item, TokenKind::Identifier)
}

fn is_stop_keyword(item: &Item) -> bool {
    token_text(item).is_some_and(|text| {
        matches!(text, "do" | "if" | "else" | "case" | "catch" | "rule")
            && is_token(item, TokenKind::Identifier)
    })
}

fn is_rule_stop(item: &Item, frame: RuleFrame) -> bool {
    matches!(item.payload, Payload::Boundary(_) | Payload::Eof)
        || is_stop_keyword(item)
        || is_close(item)
        || is_separator(item, frame)
}

fn is_close(item: &Item) -> bool {
    matches!(
        &item.payload,
        Payload::Token(Token {
            kind: TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace,
            ..
        })
    )
}

fn is_separator(item: &Item, frame: RuleFrame) -> bool {
    is_token(item, TokenKind::Pipe)
        || is_newline(item)
        || matches!(frame, RuleFrame::Parenthesis) && is_token(item, TokenKind::Comma)
}

fn is_newline(item: &Item) -> bool {
    token_text(item).is_some_and(|text| matches!(text, "\n" | "\r\n"))
}

fn is_quantifier(item: &Item) -> bool {
    token_text(item).is_some_and(|text| matches!(text, "*" | "+" | "?" | "*?" | "+?"))
}

fn is_token(item: &Item, kind: TokenKind) -> bool {
    matches!(&item.payload, Payload::Token(token) if token.kind == kind)
}

fn token_text(item: &Item) -> Option<&str> {
    match &item.payload {
        Payload::Token(token) => Some(&token.text),
        Payload::Operator(operator) => Some(&operator.text),
        Payload::Boundary(_) | Payload::Eof => None,
    }
}

fn consume_bytes(mut i: LexIn, width: usize) -> Option<()> {
    let mut consumed = 0usize;
    while consumed < width {
        consumed += i.next()?.len_utf8();
    }
    (consumed == width).then_some(())
}

#[cfg(test)]
fn suffix_distance(source: &str, suffix: &str) -> usize {
    let consumed = source
        .len()
        .checked_sub(suffix.len())
        .expect("live suffix cannot exceed its source");
    assert_eq!(source.as_ptr().wrapping_add(consumed), suffix.as_ptr());
    consumed
}

#[cfg(test)]
fn consumed_prefix<'source>(source: &'source str, suffix: &str) -> &'source str {
    &source[..suffix_distance(source, suffix)]
}
