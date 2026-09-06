//! Isolated RuleSequenceCore construction before RuleExpression dispatch.

mod expression_list;

use reborrow_generic::Reborrow as _;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, RewriteIn,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    driver::{advanced_origin, suffix_marker},
    emit::emit_error_item,
    item::{Item, Token, TokenKind},
    lexer::{
        scan_exact_equals, scan_integer, scan_operator_shaped_unknown, scan_punctuation,
        scan_unknown,
    },
    literal::{
        NormalizedStringLiteralExit, scan_string_opener_token,
        string_literal_with_virtual_statements_normalized, string_mode_from_opener,
    },
    yumark::FenceBoundary,
};

use self::expression_list::{ExpressionListExit, expression_list, first_item as first_list_item};

#[derive(Clone, Copy)]
enum RuleFrame {
    Body,
    Parenthesis { outer_literal_quote: bool },
    LiteralInterpolation,
}

#[derive(Debug, Eq, PartialEq)]
pub(super) enum RuleLiteralSequenceExit {
    Close(Item, LineEntry),
    OuterTerminator(Item, LineEntry),
    Boundary(Item, LineEntry),
}

#[derive(Debug, Eq, PartialEq)]
pub(super) enum RuleWitnessExit {
    Complete,
    Returned(Item),
    Deferred(Item),
}

enum NormalizedRuleWitnessExit {
    Complete(LineEntry),
    Returned(Item, LineEntry),
    Deferred(Item, LineEntry),
}

enum SequenceExit {
    Stop(Item, LineEntry),
    Deferred(Item, LineEntry),
}

enum ItemExit {
    Continue(Item, LineEntry),
    Deferred(Item, LineEntry),
}

/// Builds one isolated RuleBody from an already accepted `{` and one current
/// Item. It does not recognize `rule` or enter production expression dispatch.
pub(super) fn rule_body_witness(
    i: RewriteIn,
    opener: Item,
    current: Item,
    line_entry: LineEntry,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> RuleWitnessExit {
    match rule_body_normalized(i, opener, current, origin, line_entry, fence) {
        NormalizedRuleWitnessExit::Complete(_) => RuleWitnessExit::Complete,
        NormalizedRuleWitnessExit::Returned(item, _) => RuleWitnessExit::Returned(item),
        NormalizedRuleWitnessExit::Deferred(item, _) => RuleWitnessExit::Deferred(item),
    }
}

#[cfg(test)]
pub(super) fn rule_body_normalized_witness(
    i: RewriteIn,
    opener: Item,
    current: Item,
    line_entry: LineEntry,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (RuleWitnessExit, LineEntry) {
    match rule_body_normalized(i, opener, current, origin, line_entry, fence) {
        NormalizedRuleWitnessExit::Complete(line_entry) => (RuleWitnessExit::Complete, line_entry),
        NormalizedRuleWitnessExit::Returned(item, line_entry) => {
            (RuleWitnessExit::Returned(item), line_entry)
        }
        NormalizedRuleWitnessExit::Deferred(item, line_entry) => {
            (RuleWitnessExit::Deferred(item), line_entry)
        }
    }
}

fn rule_body_normalized(
    mut i: RewriteIn,
    opener: Item,
    current: Item,
    mut origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedRuleWitnessExit {
    debug_assert!(is_token(&opener, TokenKind::LBrace));
    i.state.start_node(SyntaxKind::RuleBody.into());
    emit_item_as(&mut i, opener, SyntaxKind::LBrace);

    let exit = rule_alternation(
        i.rb(),
        current,
        line_entry,
        RuleFrame::Body,
        &mut origin,
        fence,
    );
    let exit = match exit {
        SequenceExit::Stop(close, line_entry) if is_token(&close, TokenKind::RBrace) => {
            emit_item_as(&mut i, close, SyntaxKind::RBrace);
            NormalizedRuleWitnessExit::Complete(line_entry)
        }
        SequenceExit::Stop(pending, line_entry) => {
            emit_missing(&mut i);
            NormalizedRuleWitnessExit::Returned(pending, line_entry)
        }
        SequenceExit::Deferred(item, line_entry) => {
            NormalizedRuleWitnessExit::Deferred(item, line_entry)
        }
    };
    i.state.finish_node();
    exit
}

/// Scans one rule-local current Item. Physical newlines remain in its leading
/// trivia so the alternatives owner can consume one separator at a time.
pub(super) fn scan_rule_item_witness(i: LexIn) -> Option<Item> {
    current_item(i, 0, LineEntry::InLine, None, scan_rule_payload).map(|current| current.item)
}

#[cfg(test)]
pub(super) fn scan_rule_current_item_witness(
    i: LexIn,
    origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> CurrentItem {
    current_item(i, origin, line_entry, fence, scan_rule_payload)
        .expect("the Rule current-Item witness scanner is total")
}

#[cfg(test)]
pub(super) fn expression_list_handoff_witness(
    i: RewriteIn,
    current: Item,
    close: TokenKind,
    origin: usize,
) -> RuleWitnessExit {
    let mut origin = origin;
    match expression_list(i, current, close, &mut origin, LineEntry::InLine, None) {
        ExpressionListExit::Close(item, _) | ExpressionListExit::Returned(item, _) => {
            RuleWitnessExit::Returned(item)
        }
        ExpressionListExit::Deferred(item, _) => RuleWitnessExit::Deferred(item),
    }
}

/// Reads the sole successor after a contextual `rule` candidate. The result
/// is still one ordinary current Item: accepted trivia and quote-prefix
/// fragments stay attached to it, while a fence decision is its exact payload.
#[cfg(test)]
pub(super) fn scan_rule_introducer_successor_witness(
    i: LexIn,
    origin: usize,
    fence: &FenceBoundary,
) -> Item {
    current_item(i, origin, LineEntry::InLine, Some(fence), scan_rule_payload)
        .expect("the Rule successor current-Item scanner is total")
        .item
}

fn rule_alternation(
    mut i: RewriteIn,
    mut current: Item,
    mut line_entry: LineEntry,
    frame: RuleFrame,
    origin: &mut usize,
    fence: Option<&FenceBoundary>,
) -> SequenceExit {
    i.state.start_node(SyntaxKind::RuleAlternation.into());
    i.state.start_node(SyntaxKind::RuleSequence.into());
    loop {
        if current.payload_view().is_boundary() {
            i.state.finish_node();
            i.state.finish_node();
            return SequenceExit::Stop(current, line_entry);
        }

        while let Some(end_part) = current.leading_view().cut_after_first_ordinary_newline() {
            i.state.finish_node();
            current.emit_leading_prefix_with(&mut *i.state, end_part, |_, _| {});
            i.state.start_node(SyntaxKind::RuleSequence.into());
        }

        let exit = rule_sequence(i.rb(), current, line_entry, frame, origin, fence);

        match exit {
            SequenceExit::Deferred(item, line_entry) => {
                i.state.finish_node();
                i.state.finish_node();
                return SequenceExit::Deferred(item, line_entry);
            }
            SequenceExit::Stop(item, next_line_entry) if is_separator(&item, frame) => {
                i.state.finish_node();
                emit_separator(&mut i, item);
                i.state.start_node(SyntaxKind::RuleSequence.into());
                (current, line_entry) = next_rule_item(i.rb(), origin, next_line_entry, fence);
            }
            SequenceExit::Stop(item, next_line_entry)
                if item.leading_view().has_ordinary_newline() =>
            {
                current = item;
                line_entry = next_line_entry;
            }
            SequenceExit::Stop(item, line_entry) => {
                i.state.finish_node();
                i.state.finish_node();
                return SequenceExit::Stop(item, line_entry);
            }
        }
    }
}

pub(super) fn rule_literal_sequence_normalized(
    mut i: RewriteIn,
    origin: &mut usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> RuleLiteralSequenceExit {
    let (current, line_entry) = next_rule_item(i.rb(), origin, line_entry, fence);
    i.state.start_node(SyntaxKind::RuleSequence.into());
    let exit = rule_sequence(
        i.rb(),
        current,
        line_entry,
        RuleFrame::LiteralInterpolation,
        origin,
        fence,
    );
    i.state.finish_node();
    match exit {
        SequenceExit::Stop(item, line_entry) if is_token(&item, TokenKind::RBrace) => {
            RuleLiteralSequenceExit::Close(item, line_entry)
        }
        SequenceExit::Stop(item, line_entry) if is_outer_literal_quote(&item) => {
            RuleLiteralSequenceExit::OuterTerminator(item, line_entry)
        }
        SequenceExit::Stop(item, line_entry) => RuleLiteralSequenceExit::Boundary(item, line_entry),
        SequenceExit::Deferred(_, _) => {
            unreachable!("L7 RuleSequence children enter every direct literal owner")
        }
    }
}

fn rule_sequence(
    mut i: RewriteIn,
    mut current: Item,
    mut line_entry: LineEntry,
    frame: RuleFrame,
    origin: &mut usize,
    fence: Option<&FenceBoundary>,
) -> SequenceExit {
    loop {
        if !matches!(frame, RuleFrame::LiteralInterpolation)
            && !current.payload_view().is_boundary()
            && current.leading_view().has_ordinary_newline()
        {
            return SequenceExit::Stop(current, line_entry);
        }
        if is_rule_stop(&current, frame) {
            return SequenceExit::Stop(current, line_entry);
        }
        if is_rule_atom_start(&current) {
            match rule_item(i.rb(), current, line_entry, frame, origin, fence) {
                ItemExit::Continue(next, next_line_entry) => {
                    current = next;
                    line_entry = next_line_entry;
                }
                ItemExit::Deferred(item, line_entry) => {
                    return SequenceExit::Deferred(item, line_entry);
                }
            }
            continue;
        }

        emit_unexpected(&mut i, current);
        (current, line_entry) = next_rule_item(i.rb(), origin, line_entry, fence);
    }
}

fn rule_item(
    mut i: RewriteIn,
    current: Item,
    line_entry: LineEntry,
    frame: RuleFrame,
    origin: &mut usize,
    fence: Option<&FenceBoundary>,
) -> ItemExit {
    i.state.start_node(SyntaxKind::RuleItem.into());
    let (mut current, mut line_entry) = if is_token(&current, TokenKind::LParen) {
        emit_item_as(&mut i, current, SyntaxKind::LParen);
        let (nested_current, nested_line_entry) = next_rule_item(i.rb(), origin, line_entry, fence);
        let nested = rule_alternation(
            i.rb(),
            nested_current,
            nested_line_entry,
            RuleFrame::Parenthesis {
                outer_literal_quote: carries_outer_literal_quote(frame),
            },
            origin,
            fence,
        );
        match nested {
            SequenceExit::Stop(close, line_entry) if is_token(&close, TokenKind::RParen) => {
                emit_item_as(&mut i, close, SyntaxKind::RParen);
                next_rule_item(i.rb(), origin, line_entry, fence)
            }
            SequenceExit::Stop(pending, line_entry) => {
                emit_missing(&mut i);
                i.state.finish_node();
                return ItemExit::Continue(pending, line_entry);
            }
            SequenceExit::Deferred(item, line_entry) => {
                i.state.finish_node();
                return ItemExit::Deferred(item, line_entry);
            }
        }
    } else if let Some(mode) = string_mode_from_opener(&current) {
        let entry = suffix_marker(i.rb());
        let exit = string_literal_with_virtual_statements_normalized(
            i.rb(),
            current,
            mode,
            *origin,
            fence,
        );
        *origin = advanced_origin(*origin, entry, i.rb());
        match exit {
            NormalizedStringLiteralExit::Complete(line_entry) => {
                next_rule_item(i.rb(), origin, line_entry, fence)
            }
            NormalizedStringLiteralExit::Boundary(pending, line_entry) => {
                i.state.finish_node();
                return ItemExit::Continue(pending, line_entry);
            }
        }
    } else if is_token(&current, TokenKind::LBracket) {
        emit_item_as(&mut i, current, SyntaxKind::LBracket);
        let (first, first_line_entry) =
            first_list_item(i.rb(), TokenKind::RBracket, origin, line_entry, fence);
        match expression_list(
            i.rb(),
            first,
            TokenKind::RBracket,
            origin,
            first_line_entry,
            fence,
        ) {
            ExpressionListExit::Close(close, line_entry) => {
                emit_item_as(&mut i, close, SyntaxKind::RBracket);
                next_rule_item(i.rb(), origin, line_entry, fence)
            }
            ExpressionListExit::Returned(pending, line_entry) => {
                i.state.finish_node();
                return ItemExit::Continue(pending, line_entry);
            }
            ExpressionListExit::Deferred(item, line_entry) => {
                i.state.finish_node();
                return ItemExit::Deferred(item, line_entry);
            }
        }
    } else {
        emit_rule_atom(&mut i, current);
        next_rule_item(i.rb(), origin, line_entry, fence)
    };

    loop {
        if is_token(&current, TokenKind::Equals) {
            i.state.start_node(SyntaxKind::RuleCapture.into());
            emit_item_as(&mut i, current, SyntaxKind::Equals);
            let (right, right_line_entry) = next_rule_item(i.rb(), origin, line_entry, fence);
            match required_rule_item(i.rb(), right, right_line_entry, frame, origin, fence) {
                ItemExit::Continue(next, line_entry) => {
                    i.state.finish_node();
                    i.state.finish_node();
                    return ItemExit::Continue(next, line_entry);
                }
                ItemExit::Deferred(item, line_entry) => {
                    i.state.finish_node();
                    i.state.finish_node();
                    return ItemExit::Deferred(item, line_entry);
                }
            }
        }

        if !current.leading_view().is_grammar_empty() {
            i.state.finish_node();
            return ItemExit::Continue(current, line_entry);
        }

        if is_quantifier(&current) {
            i.state.start_node(SyntaxKind::RuleQuantifier.into());
            emit_item_as(&mut i, current, SyntaxKind::RuleQuantifierToken);
            i.state.finish_node();
            (current, line_entry) = next_rule_item(i.rb(), origin, line_entry, fence);
            continue;
        }

        if is_token(&current, TokenKind::Dot) || is_token(&current, TokenKind::PathSeparator) {
            (current, line_entry) =
                rule_named_postfix(i.rb(), current, line_entry, frame, origin, fence);
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
            let (first, first_line_entry) =
                first_list_item(i.rb(), close, origin, line_entry, fence);
            match expression_list(i.rb(), first, close, origin, first_line_entry, fence) {
                ExpressionListExit::Close(close, next_line_entry) => {
                    emit_item_as(&mut i, close, close_kind);
                    i.state.finish_node();
                    (current, line_entry) = next_rule_item(i.rb(), origin, next_line_entry, fence);
                    continue;
                }
                ExpressionListExit::Returned(pending, line_entry) => {
                    i.state.finish_node();
                    i.state.finish_node();
                    return ItemExit::Continue(pending, line_entry);
                }
                ExpressionListExit::Deferred(item, line_entry) => {
                    i.state.finish_node();
                    i.state.finish_node();
                    return ItemExit::Deferred(item, line_entry);
                }
            }
        }

        i.state.finish_node();
        return ItemExit::Continue(current, line_entry);
    }
}

fn required_rule_item(
    mut i: RewriteIn,
    mut current: Item,
    mut line_entry: LineEntry,
    frame: RuleFrame,
    origin: &mut usize,
    fence: Option<&FenceBoundary>,
) -> ItemExit {
    loop {
        if carries_outer_literal_quote(frame)
            && is_outer_literal_quote(&current)
            && is_rule_atom_start(&current)
        {
            return rule_item(i, current, line_entry, frame, origin, fence);
        }
        if is_rule_stop(&current, frame) {
            emit_missing(&mut i);
            return ItemExit::Continue(current, line_entry);
        }
        if is_rule_atom_start(&current) {
            return rule_item(i, current, line_entry, frame, origin, fence);
        }
        emit_unexpected(&mut i, current);
        (current, line_entry) = next_rule_item(i.rb(), origin, line_entry, fence);
    }
}

fn rule_named_postfix(
    mut i: RewriteIn,
    introducer: Item,
    line_entry: LineEntry,
    frame: RuleFrame,
    origin: &mut usize,
    fence: Option<&FenceBoundary>,
) -> (Item, LineEntry) {
    let (node, missing) = if is_token(&introducer, TokenKind::Dot) {
        (SyntaxKind::RuleField, SyntaxKind::Dot)
    } else {
        (SyntaxKind::RulePath, SyntaxKind::ColonColon)
    };
    i.state.start_node(node.into());
    emit_item_as(&mut i, introducer, missing);

    let (current, line_entry) = next_rule_item(i.rb(), origin, line_entry, fence);
    if is_rule_identifier(&current) && !is_stop_keyword(&current) {
        emit_item_as(&mut i, current, SyntaxKind::Identifier);
        let next = next_rule_item(i.rb(), origin, line_entry, fence);
        i.state.finish_node();
        return next;
    }

    if is_rule_stop(&current, frame) {
        emit_missing(&mut i);
        i.state.finish_node();
        return (current, line_entry);
    }

    emit_unexpected(&mut i, current);
    let next = next_rule_item(i.rb(), origin, line_entry, fence);
    i.state.finish_node();
    next
}

fn next_rule_item(
    mut i: RewriteIn,
    origin: &mut usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| current_item(lex, *origin, line_entry, fence, scan_rule_payload))
        .expect("the Rule current-Item scanner is total");
    *origin = advanced_origin(*origin, entry, i);
    (item, next_line_entry)
}

fn scan_rule_payload(
    mut i: LexIn,
    _leading: bool,
    _origin: usize,
    _fence: Option<&FenceBoundary>,
    _foreign: &mut Option<Vec<super::item::ForeignSplit>>,
) -> Option<AcceptedPayload> {
    let token = i.token(scan_rule_token)?;
    Some(AcceptedPayload {
        payload: CurrentPayload::Token(token),
        next_line_entry: LineEntry::InLine,
    })
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
        .or_else(|| i.token(scan_rule_equals))
        .or_else(|| i.token(scan_punctuation))
        .or_else(|| i.token(scan_operator_shaped_unknown))
        .or_else(|| i.token(scan_unknown))
}

fn scan_rule_equals(mut i: LexIn) -> Option<Token> {
    // A quote immediately after capture `=` is a syntactically required
    // nested StringLiteral opener, rather than part of one malformed operator.
    if !i.remainder().starts_with("=\"") {
        return i.token(scan_exact_equals);
    }
    let (_, text) = i
        .rb()
        .with_str(|mut equals| (equals.next()? == '=').then_some(()));
    Some(Token {
        kind: TokenKind::Equals,
        text: text.into(),
    })
}

fn scan_rule_fixed(mut i: LexIn) -> Option<Token> {
    let (kind, width) = if i.remainder().starts_with("..") {
        (TokenKind::DotDot, 2)
    } else if i.remainder().starts_with("*?") || i.remainder().starts_with("+?") {
        (TokenKind::Unknown, 2)
    } else {
        match i.remainder().chars().next()? {
            '|' => (TokenKind::Pipe, 1),
            '*' | '+' | '?' => (TokenKind::Unknown, 1),
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
    if item.payload_view().is_boundary() || item.payload_view().is_eof() {
        return true;
    }
    match frame {
        RuleFrame::Body => is_stop_keyword(item) || is_close(item) || is_separator(item, frame),
        RuleFrame::Parenthesis {
            outer_literal_quote,
        } => {
            is_stop_keyword(item)
                || is_close(item)
                || is_separator(item, frame)
                || outer_literal_quote && is_outer_literal_quote(item)
        }
        RuleFrame::LiteralInterpolation => {
            is_token(item, TokenKind::RBrace) || is_outer_literal_quote(item)
        }
    }
}

fn carries_outer_literal_quote(frame: RuleFrame) -> bool {
    matches!(
        frame,
        RuleFrame::LiteralInterpolation
            | RuleFrame::Parenthesis {
                outer_literal_quote: true
            }
    )
}

fn is_outer_literal_quote(item: &Item) -> bool {
    item.payload_view().spelling() == Some("\"")
}

fn is_close(item: &Item) -> bool {
    matches!(
        item.payload_view().token_kind(),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    )
}

fn is_separator(item: &Item, frame: RuleFrame) -> bool {
    is_token(item, TokenKind::Pipe)
        || matches!(frame, RuleFrame::Parenthesis { .. }) && is_token(item, TokenKind::Comma)
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
