//! Isolated RuleSequenceCore construction before RuleExpression dispatch.

mod expression_list;

use reborrow_generic::Reborrow as _;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn,
    emit::emit_error_item,
    item::{
        ForeignSplit, Item, LeadingTrivia, Payload, PendingFragments, PhysicalLeadingTrivia, Token,
        TokenKind, Trivia,
    },
    lexer::{
        scan_exact_equals, scan_integer, scan_operator_shaped_unknown, scan_ordinary_trivia_part,
        scan_punctuation, scan_unknown,
    },
    literal::{
        NonInterpolatingStringExit, non_interpolating_string_body_witness,
        scan_string_opener_token, string_mode_from_opener,
    },
    yumark::{FenceBoundary, FenceLineDecision, judge_fence_line},
};

use self::expression_list::{ExpressionListExit, expression_list, first_item as first_list_item};

#[cfg(test)]
use super::{
    item::PendingBoundary,
    lexer::{FencedBlockComment, scan_block_comment_fenced_witness, scan_fenced_prior_trivia_part},
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
pub(super) fn rule_body_witness(
    mut i: RewriteIn,
    opener: Item,
    current: Item,
    mut origin: usize,
    fence: &FenceBoundary,
) -> RuleWitnessExit {
    debug_assert!(is_token(&opener, TokenKind::LBrace));
    i.state.start_node(SyntaxKind::RuleBody.into());
    emit_item_as(&mut i, opener, SyntaxKind::LBrace);

    let exit = rule_alternation(i.rb(), current, RuleFrame::Body, &mut origin, fence);
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

#[cfg(test)]
pub(super) fn expression_list_handoff_witness(
    i: RewriteIn,
    current: Item,
    close: TokenKind,
    origin: usize,
) -> RuleWitnessExit {
    let mut origin = origin;
    match expression_list(i, current, close, &mut origin) {
        ExpressionListExit::Close(item) | ExpressionListExit::Returned(item) => {
            RuleWitnessExit::Returned(item)
        }
    }
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
    let mut leading = PhysicalLeadingTrivia::default();
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
                FencedBlockComment::Complete(comment) => leading.push_ordinary(comment),
                FencedBlockComment::Boundary { accepted, pending } => {
                    leading.push_ordinary(accepted);
                    break Payload::Boundary(pending);
                }
            }
            continue;
        }
        if let Some(trivia) = i.token(scan_fenced_prior_trivia_part) {
            let is_newline = trivia.is_newline();
            leading.push_ordinary(trivia);
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

    Item::finish(leading, payload, foreign, origin)
        .expect("accepted introducer prefixes remain inside the current Item")
}

fn rule_alternation(
    mut i: RewriteIn,
    mut current: Item,
    frame: RuleFrame,
    origin: &mut usize,
    fence: &FenceBoundary,
) -> SequenceExit {
    i.state.start_node(SyntaxKind::RuleAlternation.into());
    loop {
        i.state.start_node(SyntaxKind::RuleSequence.into());
        let exit = rule_sequence(i.rb(), current, frame, origin, fence);
        i.state.finish_node();

        match exit {
            SequenceExit::Deferred(item) => {
                i.state.finish_node();
                return SequenceExit::Deferred(item);
            }
            SequenceExit::Stop(item) if is_separator(&item, frame) => {
                let after_line = is_newline(&item);
                emit_separator(&mut i, item);
                current = next_rule_item(i.rb(), origin, fence, after_line);
            }
            SequenceExit::Stop(item) => {
                i.state.finish_node();
                return SequenceExit::Stop(item);
            }
        }
    }
}

fn rule_sequence(
    mut i: RewriteIn,
    mut current: Item,
    frame: RuleFrame,
    origin: &mut usize,
    fence: &FenceBoundary,
) -> SequenceExit {
    loop {
        if is_rule_stop(&current, frame) {
            return SequenceExit::Stop(current);
        }
        if is_rule_atom_start(&current) {
            match rule_item(i.rb(), current, frame, origin, fence) {
                ItemExit::Continue(next) => current = next,
                ItemExit::Deferred(item) => return SequenceExit::Deferred(item),
            }
            continue;
        }

        emit_unexpected(&mut i, current);
        current = next_rule_item(i.rb(), origin, fence, false);
    }
}

fn rule_item(
    mut i: RewriteIn,
    current: Item,
    frame: RuleFrame,
    origin: &mut usize,
    fence: &FenceBoundary,
) -> ItemExit {
    i.state.start_node(SyntaxKind::RuleItem.into());
    let mut current = if is_token(&current, TokenKind::LParen) {
        emit_item_as(&mut i, current, SyntaxKind::LParen);
        let nested_current = next_rule_item(i.rb(), origin, fence, false);
        let nested = rule_alternation(
            i.rb(),
            nested_current,
            RuleFrame::Parenthesis,
            origin,
            fence,
        );
        match nested {
            SequenceExit::Stop(close) if is_token(&close, TokenKind::RParen) => {
                emit_item_as(&mut i, close, SyntaxKind::RParen);
                next_rule_item(i.rb(), origin, fence, false)
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
    } else if let Some(mode) = string_mode_from_opener(&current) {
        i.state.start_node(SyntaxKind::StringLiteral.into());
        emit_item_as(&mut i, current, SyntaxKind::StringStart);
        let start = current_suffix_marker(i.rb());
        let exit = non_interpolating_string_body_witness(i.rb(), mode, *origin, fence);
        advance_origin(origin, start, current_suffix_marker(i.rb()));
        match exit {
            NonInterpolatingStringExit::Complete => next_rule_item(i.rb(), origin, fence, false),
            NonInterpolatingStringExit::Boundary(pending) => {
                i.state.finish_node();
                return ItemExit::Continue(pending);
            }
            NonInterpolatingStringExit::DeferredInterpolation(item) => {
                i.state.finish_node();
                return ItemExit::Deferred(item);
            }
        }
    } else if is_token(&current, TokenKind::LBracket) {
        emit_item_as(&mut i, current, SyntaxKind::LBracket);
        let first = first_list_item(i.rb(), TokenKind::RBracket, origin);
        match expression_list(i.rb(), first, TokenKind::RBracket, origin) {
            ExpressionListExit::Close(close) => {
                emit_item_as(&mut i, close, SyntaxKind::RBracket);
                next_rule_item(i.rb(), origin, fence, false)
            }
            ExpressionListExit::Returned(pending) => {
                i.state.finish_node();
                return ItemExit::Continue(pending);
            }
        }
    } else {
        emit_rule_atom(&mut i, current);
        next_rule_item(i.rb(), origin, fence, false)
    };

    loop {
        if is_token(&current, TokenKind::Equals) {
            i.state.start_node(SyntaxKind::RuleCapture.into());
            emit_item_as(&mut i, current, SyntaxKind::Equals);
            let right = next_rule_item(i.rb(), origin, fence, false);
            match required_rule_item(i.rb(), right, frame, origin, fence) {
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

        if !current.leading_view().is_grammar_empty() {
            i.state.finish_node();
            return ItemExit::Continue(current);
        }

        if is_quantifier(&current) {
            i.state.start_node(SyntaxKind::RuleQuantifier.into());
            emit_item_as(&mut i, current, SyntaxKind::RuleQuantifierToken);
            i.state.finish_node();
            current = next_rule_item(i.rb(), origin, fence, false);
            continue;
        }

        if is_token(&current, TokenKind::Dot) || is_token(&current, TokenKind::PathSeparator) {
            current = rule_named_postfix(i.rb(), current, frame, origin, fence);
            continue;
        }

        if is_token(&current, TokenKind::LParen) || is_token(&current, TokenKind::LBracket) {
            let (node, close, open_kind, close_kind) = if is_token(&current, TokenKind::LParen) {
                (
                    SyntaxKind::RuleCall,
                    TokenKind::RParen,
                    SyntaxKind::LParen,
                    SyntaxKind::RParen,
                )
            } else {
                (
                    SyntaxKind::RuleIndex,
                    TokenKind::RBracket,
                    SyntaxKind::LBracket,
                    SyntaxKind::RBracket,
                )
            };
            i.state.start_node(node.into());
            emit_item_as(&mut i, current, open_kind);
            let first = first_list_item(i.rb(), close, origin);
            match expression_list(i.rb(), first, close, origin) {
                ExpressionListExit::Close(close) => {
                    emit_item_as(&mut i, close, close_kind);
                    i.state.finish_node();
                    current = next_rule_item(i.rb(), origin, fence, false);
                    continue;
                }
                ExpressionListExit::Returned(pending) => {
                    i.state.finish_node();
                    i.state.finish_node();
                    return ItemExit::Continue(pending);
                }
            }
        }

        i.state.finish_node();
        return ItemExit::Continue(current);
    }
}

fn required_rule_item(
    mut i: RewriteIn,
    mut current: Item,
    frame: RuleFrame,
    origin: &mut usize,
    fence: &FenceBoundary,
) -> ItemExit {
    loop {
        if is_rule_stop(&current, frame) {
            emit_missing(&mut i);
            return ItemExit::Continue(current);
        }
        if is_rule_atom_start(&current) {
            return rule_item(i, current, frame, origin, fence);
        }
        emit_unexpected(&mut i, current);
        current = next_rule_item(i.rb(), origin, fence, false);
    }
}

fn rule_named_postfix(
    mut i: RewriteIn,
    introducer: Item,
    frame: RuleFrame,
    origin: &mut usize,
    fence: &FenceBoundary,
) -> Item {
    let (node, missing) = if is_token(&introducer, TokenKind::Dot) {
        (SyntaxKind::RuleField, SyntaxKind::Dot)
    } else {
        (SyntaxKind::RulePath, SyntaxKind::ColonColon)
    };
    i.state.start_node(node.into());
    emit_item_as(&mut i, introducer, missing);

    let current = next_rule_item(i.rb(), origin, fence, false);
    if is_rule_identifier(&current) && !is_stop_keyword(&current) {
        emit_item_as(&mut i, current, SyntaxKind::Identifier);
        let next = next_rule_item(i.rb(), origin, fence, false);
        i.state.finish_node();
        return next;
    }

    if is_rule_stop(&current, frame) {
        emit_missing(&mut i);
        i.state.finish_node();
        return current;
    }

    emit_unexpected(&mut i, current);
    let next = next_rule_item(i.rb(), origin, fence, false);
    i.state.finish_node();
    next
}

fn next_rule_item(
    mut i: RewriteIn,
    origin: &mut usize,
    fence: &FenceBoundary,
    after_line: bool,
) -> Item {
    let start = current_suffix_marker(i.rb());
    let item = i
        .token(|lex| Some(scan_rule_item_fenced(lex, *origin, fence, after_line)))
        .expect("the rule current-item scanner is total");
    advance_origin(origin, start, current_suffix_marker(i));
    item
}

fn scan_rule_item_fenced(
    mut i: LexIn,
    origin: usize,
    fence: &FenceBoundary,
    after_line: bool,
) -> Item {
    let source = i.remainder();
    let mut leading = PhysicalLeadingTrivia::default();
    let mut foreign = None;

    if after_line {
        match judge_fence_line(source, origin, fence) {
            FenceLineDecision::Boundary(pending) => {
                return Item::plain(LeadingTrivia::default(), Payload::Boundary(pending));
            }
            FenceLineDecision::Body { prefix: None, .. } => {}
            FenceLineDecision::Body {
                prefix: Some(prefix),
                ..
            } => {
                let length = prefix.facts.extent.end - prefix.facts.extent.start;
                let (_, text) = i.rb().with_str(|prefix| consume_bytes(prefix, length));
                leading.push_quote_prefix(text.into());
                PendingFragments::record(
                    &mut foreign,
                    ForeignSplit::quote_prefix(prefix.facts.extent.start, length),
                )
                .expect("the fence judge returns one in-range body prefix");
            }
        }
    }

    while let Some(trivia) = i.token(scan_inline_trivia) {
        leading.push_ordinary(trivia);
    }
    let payload = if i.remainder().is_empty() {
        Payload::Eof
    } else {
        Payload::Token(
            i.token(scan_rule_token)
                .expect("a nonempty rule suffix has one lexical token"),
        )
    };
    Item::finish(leading, payload, foreign, origin)
        .expect("an accepted rule body prefix remains in its current Item")
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
        LeadingTrivia::ordinary(leading.into_boxed_slice()),
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
    if let Some((token, _)) = i.token(scan_string_opener_token) {
        return Some(token);
    }
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
    leading: &mut PhysicalLeadingTrivia,
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
            leading.push_quote_prefix(text.into());
            None
        }
    }
}

fn emit_rule_atom(i: &mut RewriteIn, item: Item) {
    let kind = match item.payload_view().token_kind() {
        Some(TokenKind::Identifier) => SyntaxKind::Identifier,
        Some(TokenKind::SigilIdentifier) => SyntaxKind::SigilIdentifier,
        Some(TokenKind::Integer) => SyntaxKind::Integer,
        Some(TokenKind::DotDot) => SyntaxKind::DotDot,
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
    debug_assert!(item.payload_view().token_kind().is_some());
    item.emit_remaining(&mut *i.state, kind);
}

fn is_rule_atom_start(item: &Item) -> bool {
    (is_rule_identifier(item) && !is_stop_keyword(item))
        || is_token(item, TokenKind::SigilIdentifier)
        || is_token(item, TokenKind::Integer)
        || is_token(item, TokenKind::DotDot)
        || is_token(item, TokenKind::LParen)
        || is_token(item, TokenKind::LBracket)
        || string_mode_from_opener(item).is_some()
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
    item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || is_stop_keyword(item)
        || is_close(item)
        || is_separator(item, frame)
}

fn is_close(item: &Item) -> bool {
    matches!(
        item.payload_view().token_kind(),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
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
    item.payload_view().token_kind() == Some(kind)
}

fn token_text(item: &Item) -> Option<&str> {
    item.payload_view().spelling()
}

fn consume_bytes(mut i: LexIn, width: usize) -> Option<()> {
    let mut consumed = 0usize;
    while consumed < width {
        consumed += i.next()?.len_utf8();
    }
    (consumed == width).then_some(())
}

fn current_suffix_marker(mut i: RewriteIn) -> (usize, usize) {
    i.token(|lex| Some((lex.remainder().as_ptr() as usize, lex.remainder().len())))
        .expect("the live suffix probe is total")
}

fn advance_origin(origin: &mut usize, start: (usize, usize), end: (usize, usize)) {
    let consumed = start
        .1
        .checked_sub(end.1)
        .expect("a direct rule child cannot lengthen its live suffix");
    assert_eq!(
        start.0.wrapping_add(consumed),
        end.0,
        "a direct rule child keeps the input on one source suffix"
    );
    *origin = origin
        .checked_add(consumed)
        .expect("the rule source coordinate must fit usize");
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
