//! Rule expressions and their shared Rule DSL interior.

use crate::ambient_claim::AmbientClaimContext;
#[cfg(test)]
use crate::ambient_claim::AmbientClaimView;
mod expression_list;

use reborrow_generic::Reborrow as _;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{
    recovery_record::{
        Delimiter, ExpectationSources, ExpectedSyntax, GrammarRole, LiteralExpected, LiteralRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    cst_output::{
        RecoveryDraft,
        emit::{emit_recovery_error_run, emit_recovery_missing, token_syntax_kind},
    },
    cursor::{LexIn, SyntaxIn},
    lexical::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, Token, TokenKind},
        lexer::{
            is_operator_shaped_unknown, scan_exact_equals, scan_integer,
            scan_operator_shaped_unknown, scan_punctuation, scan_unknown,
        },
        position::{advanced_origin, suffix_marker},
        yumark::FenceBoundary,
    },
    literal::{
        NormalizedStringLiteralExit, scan_string_opener_token,
        string_literal_with_virtual_statements_normalized, string_mode_from_opener,
    },
};

use crate::rule::expression_list::{
    ExpressionListExit, expression_list, first_item as first_list_item,
};
use std::{ops::Range, sync::Arc};

/// Maps one already-owned malformed Rule item to its exact diagnostic category.
///
/// Caller-owned closes and boundaries are filtered before this Rule-local
/// mapping. No source text is rescanned: `Unknown` uses only its owned spelling.
pub(super) fn rule_item_unexpected_category(item: &Item) -> UnexpectedCategory {
    let payload = item.payload_view();
    if payload.operator_use().is_some() {
        return UnexpectedCategory::OperatorLike;
    }
    match payload
        .token_kind()
        .expect("Rule unexpected evidence requires a lexical Item")
    {
        TokenKind::Identifier | TokenKind::SigilIdentifier | TokenKind::Forall => {
            UnexpectedCategory::Word
        }
        TokenKind::Integer => UnexpectedCategory::DecimalInteger,
        TokenKind::Operator | TokenKind::DotDot => UnexpectedCategory::OperatorLike,
        TokenKind::LParen => {
            UnexpectedCategory::Punctuation(PunctuationEvidence::Open(Delimiter::Parenthesis))
        }
        TokenKind::RParen => {
            UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis))
        }
        TokenKind::LBracket => {
            UnexpectedCategory::Punctuation(PunctuationEvidence::Open(Delimiter::Bracket))
        }
        TokenKind::RBracket => {
            UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Bracket))
        }
        TokenKind::LBrace => {
            UnexpectedCategory::Punctuation(PunctuationEvidence::Open(Delimiter::Brace))
        }
        TokenKind::RBrace => {
            UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Brace))
        }
        TokenKind::Comma => UnexpectedCategory::Punctuation(PunctuationEvidence::Comma),
        TokenKind::Semicolon => UnexpectedCategory::Punctuation(PunctuationEvidence::Semicolon),
        TokenKind::Dot => UnexpectedCategory::Punctuation(PunctuationEvidence::Dot),
        TokenKind::Arrow => UnexpectedCategory::Punctuation(PunctuationEvidence::Arrow),
        TokenKind::Colon | TokenKind::PolymorphicVariantColon | TokenKind::PatternSymbolColon => {
            UnexpectedCategory::Punctuation(PunctuationEvidence::Colon)
        }
        TokenKind::Equals => UnexpectedCategory::Punctuation(PunctuationEvidence::Equals),
        TokenKind::EffectRowApostrophe => {
            UnexpectedCategory::Punctuation(PunctuationEvidence::Apostrophe)
        }
        TokenKind::PathSeparator => {
            UnexpectedCategory::Punctuation(PunctuationEvidence::ColonColon)
        }
        TokenKind::Pipe => UnexpectedCategory::Punctuation(PunctuationEvidence::Pipe),
        TokenKind::Unknown if is_operator_shaped_unknown(item) => UnexpectedCategory::OperatorLike,
        TokenKind::Unknown => UnexpectedCategory::OtherCharacter,
    }
}

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
#[cfg(test)]
pub(super) enum RuleWitnessExit {
    Complete,
    Returned(Item),
    Deferred(Item),
}

enum NormalizedRuleBodyExit {
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

pub(crate) enum RuleExpressionExit {
    Complete(LineEntry),
    Boundary(Item, LineEntry),
}

/// Commits the contextual word and its already accepted brace successor.
pub(crate) fn rule_expression_normalized(
    mut i: SyntaxIn,
    keyword: Item,
    opener: Item,
    mut origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> RuleExpressionExit {
    i.state.start_node(SyntaxKind::RuleExpression.into());
    emit_item_as(&mut i, keyword, SyntaxKind::RuleKw);
    let (current, line_entry) = next_rule_item(i.rb(), &mut origin, line_entry, fence);
    let exit = rule_body_normalized(i.rb(), opener, current, origin, line_entry, fence, ambient);
    i.state.finish_node();
    match exit {
        NormalizedRuleBodyExit::Complete(line_entry) => RuleExpressionExit::Complete(line_entry),
        NormalizedRuleBodyExit::Returned(item, line_entry) => {
            RuleExpressionExit::Boundary(item, line_entry)
        }
        NormalizedRuleBodyExit::Deferred(item, line_entry) => {
            unreachable!(
                "complete Rule children enter every direct literal owner: {item:?}, {line_entry:?}"
            )
        }
    }
}

/// Builds one isolated RuleBody from an already accepted `{` and one current
/// Item. It does not recognize `rule` or enter production expression dispatch.
#[cfg(test)]
pub(super) fn rule_body_witness(
    i: SyntaxIn,
    opener: Item,
    current: Item,
    line_entry: LineEntry,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> RuleWitnessExit {
    match rule_body_normalized(
        i,
        opener,
        current,
        origin,
        line_entry,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
    ) {
        NormalizedRuleBodyExit::Complete(_) => RuleWitnessExit::Complete,
        NormalizedRuleBodyExit::Returned(item, _) => RuleWitnessExit::Returned(item),
        NormalizedRuleBodyExit::Deferred(item, _) => RuleWitnessExit::Deferred(item),
    }
}

#[cfg(test)]
pub(super) fn rule_body_normalized_witness(
    i: SyntaxIn,
    opener: Item,
    current: Item,
    line_entry: LineEntry,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (RuleWitnessExit, LineEntry) {
    match rule_body_normalized(
        i,
        opener,
        current,
        origin,
        line_entry,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
    ) {
        NormalizedRuleBodyExit::Complete(line_entry) => (RuleWitnessExit::Complete, line_entry),
        NormalizedRuleBodyExit::Returned(item, line_entry) => {
            (RuleWitnessExit::Returned(item), line_entry)
        }
        NormalizedRuleBodyExit::Deferred(item, line_entry) => {
            (RuleWitnessExit::Deferred(item), line_entry)
        }
    }
}

fn rule_body_normalized(
    mut i: SyntaxIn,
    opener: Item,
    current: Item,
    mut origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedRuleBodyExit {
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
        ambient,
    );
    let exit = match exit {
        SequenceExit::Stop(close, line_entry) if is_token(&close, TokenKind::RBrace) => {
            emit_item_as(&mut i, close, SyntaxKind::RBrace);
            NormalizedRuleBodyExit::Complete(line_entry)
        }
        SequenceExit::Stop(pending, line_entry) => {
            emit_rule_missing(
                i.rb(),
                LiteralRole::RuleBodyCloseBrace,
                rule_recovery_at(&pending, origin),
            );
            NormalizedRuleBodyExit::Returned(pending, line_entry)
        }
        SequenceExit::Deferred(item, line_entry) => {
            NormalizedRuleBodyExit::Deferred(item, line_entry)
        }
    };
    i.state.finish_node();
    exit
}

/// Scans one rule-local current Item. Physical newlines remain in its leading
/// trivia so the alternatives owner can consume one separator at a time.
#[cfg(test)]
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
    i: SyntaxIn,
    current: Item,
    close: TokenKind,
    origin: usize,
) -> RuleWitnessExit {
    let mut origin = origin;
    match expression_list(
        i,
        current,
        close,
        &mut origin,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
    ) {
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
    mut i: SyntaxIn,
    mut current: Item,
    mut line_entry: LineEntry,
    frame: RuleFrame,
    origin: &mut usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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

        let exit = rule_sequence(i.rb(), current, line_entry, frame, origin, fence, ambient);

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
    mut i: SyntaxIn,
    origin: &mut usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
        ambient,
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
    mut i: SyntaxIn,
    mut current: Item,
    mut line_entry: LineEntry,
    frame: RuleFrame,
    origin: &mut usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
            match rule_item(i.rb(), current, line_entry, frame, origin, fence, ambient) {
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

        emit_unexpected(i.rb(), current, *origin, LiteralRole::RuleUnexpectedItem);
        (current, line_entry) = next_rule_item(i.rb(), origin, line_entry, fence);
    }
}

fn rule_item(
    mut i: SyntaxIn,
    current: Item,
    line_entry: LineEntry,
    frame: RuleFrame,
    origin: &mut usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
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
            ambient,
        );
        match nested {
            SequenceExit::Stop(close, line_entry) if is_token(&close, TokenKind::RParen) => {
                emit_item_as(&mut i, close, SyntaxKind::RParen);
                next_rule_item(i.rb(), origin, line_entry, fence)
            }
            SequenceExit::Stop(pending, line_entry) => {
                emit_rule_missing(
                    i.rb(),
                    LiteralRole::RuleParenClose,
                    rule_recovery_at(&pending, *origin),
                );
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
            ambient,
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
            ambient,
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
            match required_rule_item(
                i.rb(),
                right,
                right_line_entry,
                frame,
                origin,
                fence,
                ambient,
            ) {
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
            match expression_list(
                i.rb(),
                first,
                close,
                origin,
                first_line_entry,
                fence,
                ambient,
            ) {
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
    mut i: SyntaxIn,
    mut current: Item,
    mut line_entry: LineEntry,
    frame: RuleFrame,
    origin: &mut usize,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> ItemExit {
    loop {
        if is_rule_newline_stop(&current, frame) {
            emit_rule_missing(
                i.rb(),
                LiteralRole::RuleCaptureRightItem,
                rule_recovery_at(&current, *origin),
            );
            return ItemExit::Continue(current, line_entry);
        }
        if carries_outer_literal_quote(frame)
            && is_outer_literal_quote(&current)
            && is_rule_atom_start(&current)
        {
            return rule_item(i, current, line_entry, frame, origin, fence, ambient);
        }
        if is_rule_stop(&current, frame) {
            emit_rule_missing(
                i.rb(),
                LiteralRole::RuleCaptureRightItem,
                rule_recovery_at(&current, *origin),
            );
            return ItemExit::Continue(current, line_entry);
        }
        if is_rule_atom_start(&current) {
            return rule_item(i, current, line_entry, frame, origin, fence, ambient);
        }
        emit_unexpected(i.rb(), current, *origin, LiteralRole::RuleUnexpectedItem);
        (current, line_entry) = next_rule_item(i.rb(), origin, line_entry, fence);
    }
}

fn rule_named_postfix(
    mut i: SyntaxIn,
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
    let role = if node == SyntaxKind::RuleField {
        LiteralRole::RuleFieldName
    } else {
        LiteralRole::RulePathName
    };
    if is_rule_newline_stop(&current, frame) || is_rule_stop(&current, frame) {
        emit_rule_missing(i.rb(), role, rule_recovery_at(&current, *origin));
        i.state.finish_node();
        return (current, line_entry);
    }
    if is_rule_identifier(&current) && !is_stop_keyword(&current) {
        emit_item_as(&mut i, current, SyntaxKind::Identifier);
        let next = next_rule_item(i.rb(), origin, line_entry, fence);
        i.state.finish_node();
        return next;
    }

    emit_unexpected(i.rb(), current, *origin, role);
    let next = next_rule_item(i.rb(), origin, line_entry, fence);
    i.state.finish_node();
    next
}

fn next_rule_item(
    mut i: SyntaxIn,
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
    _foreign: &mut Option<Vec<crate::lexical::item::ForeignSplit>>,
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

fn emit_rule_atom(i: &mut SyntaxIn, item: Item) {
    let kind = match item.payload_view().token_kind() {
        Some(TokenKind::Identifier) => SyntaxKind::Identifier,
        Some(TokenKind::SigilIdentifier) => SyntaxKind::SigilIdentifier,
        Some(TokenKind::Integer) => SyntaxKind::Integer,
        Some(TokenKind::DotDot) => SyntaxKind::DotDot,
        _ => unreachable!("a RuleItem starts with a RuleSequenceCore atom"),
    };
    emit_item_as(i, item, kind);
}

fn emit_separator(i: &mut SyntaxIn, item: Item) {
    let kind = if is_token(&item, TokenKind::Pipe) {
        SyntaxKind::Pipe
    } else if is_token(&item, TokenKind::Comma) {
        SyntaxKind::Comma
    } else {
        SyntaxKind::Newline
    };
    emit_item_as(i, item, kind);
}

fn emit_unexpected(i: SyntaxIn, item: Item, origin: usize, role: LiteralRole) {
    let category = rule_item_unexpected_category(&item);
    let kind = token_syntax_kind(
        item.payload_view()
            .token_kind()
            .expect("Rule Error owns a token"),
    );
    emit_recovery_error_run(
        i,
        |run| {
            let range = run.emit_item_as(item, origin, kind).recovery_range();
            run.append_unexpected(UnexpectedSyntax::Token { range, category });
        },
        |range, unexpected| rule_draft(role, RecoveryKind::Error, range, unexpected),
    );
}

pub(super) fn rule_recovery_at(item: &Item, origin: usize) -> usize {
    if item.payload_view().is_eof() {
        return origin;
    }
    item.payload_view().pending_boundary().map_or_else(
        || item.extent(origin).recovery_range().start,
        |boundary| boundary.coordinate(),
    )
}

pub(super) fn emit_rule_missing(i: SyntaxIn, role: LiteralRole, at: usize) {
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        rule_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn rule_draft(
    role: LiteralRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        LiteralRole::RuleBodyCloseBrace
        | LiteralRole::RuleLiteralInterpolationCloseBrace
        | LiteralRole::RuleLazyCaptureCloseBrace => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace))
        }
        LiteralRole::RuleParenClose => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis))
        }
        LiteralRole::RuleCaptureRightItem | LiteralRole::RuleUnexpectedItem => {
            ExpectedSyntax::Literal(LiteralExpected::RuleItem)
        }
        LiteralRole::RuleFieldName
        | LiteralRole::RulePathName
        | LiteralRole::RuleLazyCaptureName => ExpectedSyntax::Identifier,
        LiteralRole::RuleLiteralTerminator => {
            ExpectedSyntax::Literal(LiteralExpected::RuleLiteralTerminator)
        }
        _ => unreachable!("String recovery belongs to its own owner"),
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

fn emit_item_as(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
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

fn is_rule_newline_stop(item: &Item, frame: RuleFrame) -> bool {
    !matches!(frame, RuleFrame::LiteralInterpolation)
        && !item.payload_view().is_boundary()
        && item.leading_view().has_ordinary_newline()
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
