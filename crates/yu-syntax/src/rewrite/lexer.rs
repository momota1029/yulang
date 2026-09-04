//! Lexical item construction and ordinary trivia ownership for the rewrite.

use chasa_recover::{
    In,
    parser::{choice, token},
};
use reborrow_generic::short::Rb;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::scan::operator::OperatorSite;

use super::{
    LexIn, RewriteIn,
    item::{Item, LeadingTrivia, Payload, Token, TokenKind, Trivia, TriviaKind},
    operator::{
        STOP_RECORD_SPREAD, STOP_RECORD_SPREAD_AFTER_OPERATOR, lone_colon_after_trivia,
        newline_indentation_after_trivia, scan_dangling_operator, scan_operator,
    },
    state::Recover,
};

pub(super) fn tail_item_after_trivia(
    mut i: RewriteIn,
    leading: LeadingTrivia,
    site: OperatorSite,
    baseline: usize,
    stops: u8,
) -> Item {
    let has_leading_trivia = !leading.0.is_empty();
    let record_spread = stops & STOP_RECORD_SPREAD != 0;
    let marker_after_operator = stops & STOP_RECORD_SPREAD_AFTER_OPERATOR != 0;
    let payload = if record_spread && matches!(site, OperatorSite::Nud) {
        if let Some(marker) = i.token(scan_record_spread_marker) {
            Payload::Token(marker)
        } else {
            scan_tail_payload(i, site, has_leading_trivia, baseline, stops, false)
        }
    } else {
        scan_tail_payload(
            i,
            site,
            has_leading_trivia,
            baseline,
            stops,
            marker_after_operator || (record_spread && matches!(site, OperatorSite::Led)),
        )
    };
    Item { leading, payload }
}

/// Path segments have their own lexical vocabulary: sigil-prefixed words and
/// underscore-prefixed words are not ordinary expression primaries.
pub(super) fn path_segment_item_after_trivia(
    mut i: RewriteIn,
    leading: LeadingTrivia,
    baseline: usize,
    stops: u8,
) -> Item {
    if let Some(segment) = i.token(scan_path_segment) {
        return Item {
            leading,
            payload: Payload::Token(segment),
        };
    }
    tail_item_after_trivia(i, leading, OperatorSite::Led, baseline, stops)
}

fn scan_tail_payload(
    mut i: RewriteIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    baseline: usize,
    stops: u8,
    marker_after_operator: bool,
) -> Payload {
    if let Some(operator) =
        i.token(|lex| scan_operator(lex, site, has_leading_trivia, baseline, stops))
    {
        Payload::Operator(operator)
    } else if matches!(site, OperatorSite::Led)
        && let Some(operator) =
            i.token(|lex| scan_dangling_operator(lex, OperatorSite::Led, baseline, stops))
    {
        Payload::Operator(operator)
    } else if marker_after_operator {
        if let Some(marker) = i.token(scan_record_spread_marker) {
            Payload::Token(marker)
        } else {
            scan_token_payload(i)
        }
    } else {
        scan_token_payload(i)
    }
}

fn scan_token_payload(mut i: RewriteIn) -> Payload {
    i.map(
        choice((
            token(scan_identifier),
            token(scan_integer),
            token(scan_expression_colon),
            token(scan_punctuation),
            token(scan_unknown),
        )),
        Payload::Token,
    )
    .unwrap_or(Payload::Eof)
}

pub(super) fn scan_nud_item(mut i: LexIn, baseline: usize, stops: u8) -> Option<Item> {
    let leading = scan_trivia(i.rb());
    let has_leading_trivia = !leading.0.is_empty();
    let payload = if let Some(token) = i.token(scan_lparen) {
        Payload::Token(token)
    } else if let Some(token) = i.token(scan_lbrace) {
        Payload::Token(token)
    } else if let Some(operator) =
        i.token(|lex| scan_operator(lex, OperatorSite::Nud, has_leading_trivia, baseline, stops))
    {
        Payload::Operator(operator)
    } else if let Some(operator) =
        i.token(|lex| scan_dangling_operator(lex, OperatorSite::Nud, baseline, stops))
    {
        Payload::Operator(operator)
    } else if let Some(token) = i.token(scan_identifier) {
        Payload::Token(token)
    } else {
        Payload::Token(i.token(scan_integer)?)
    };
    Some(Item { leading, payload })
}

/// Source-only reservation evidence for the second half of an exact `with:`
/// introducer. It completes no logical item and leaves the cursor unchanged.
pub(super) fn with_colon_follower(i: LexIn) -> Option<bool> {
    Some(lone_colon_after_trivia(i.remainder()))
}

/// A dynamic table may recognize the `with` prefix before the word scanner's
/// optional `?` / `!` suffix. Contextual `with` accepts only the full word.
pub(super) fn with_word_suffix_follower(i: LexIn) -> Option<bool> {
    Some(!matches!(i.remainder().chars().next(), Some('?' | '!')))
}

/// Source-only layout evidence for a colon's mandatory RHS. The accepted
/// branch later completes the first logical Item itself.
pub(super) fn newline_indentation_follower(i: LexIn) -> Option<Option<usize>> {
    Some(newline_indentation_after_trivia(i.remainder()))
}

pub(super) fn scan_type_nud_item(mut i: LexIn) -> Option<Item> {
    let token = i.check(choice((
        token(scan_type_forall),
        token(scan_type_effect_row_apostrophe),
        token(scan_type_polymorphic_variant_colon),
        token(scan_path_segment),
        token(scan_integer),
        token(scan_lbracket),
        token(scan_lparen),
        token(scan_lbrace),
    )))?;
    Some(Item {
        leading: LeadingTrivia::default(),
        payload: Payload::Token(token),
    })
}

pub(super) fn type_nud_item_after_trivia<S>(
    mut i: In<'_, &str, &mut Recover<'_>, S>,
    leading: LeadingTrivia,
) -> Item
where
    S: Rb,
{
    if let Some(token) = i.token(scan_type_forall) {
        return Item {
            leading,
            payload: Payload::Token(token),
        };
    }
    type_item_after_trivia(i, leading)
}

pub(super) fn type_item_after_trivia<S>(
    i: In<'_, &str, &mut Recover<'_>, S>,
    leading: LeadingTrivia,
) -> Item
where
    S: Rb,
{
    let payload = i
        .map(
            choice((
                token(scan_type_effect_row_apostrophe),
                token(scan_type_polymorphic_variant_colon),
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
            )),
            Payload::Token,
        )
        .unwrap_or(Payload::Eof);
    Item { leading, payload }
}

/// Type's mandatory-primary recovery must hand an exact `=` to its caller,
/// while a longer operator-shaped spelling is one malformed primary.
fn scan_malformed_equals(i: LexIn) -> Option<Token> {
    i.remainder().starts_with('=').then_some(())?;
    scan_operator_shaped_unknown(i)
}

/// Complete a Pattern primary candidate.  Only a primary position recognizes
/// the adjacent `:identifier` Symbol spelling.
pub(super) fn pattern_nud_item_after_trivia<S>(
    mut i: In<'_, &str, &mut Recover<'_>, S>,
    leading: LeadingTrivia,
) -> Item
where
    S: Rb,
{
    let payload = i
        .map(
            choice((
                token(scan_pattern_symbol_colon),
                token(scan_pattern_tail_token),
            )),
            Payload::Token,
        )
        .unwrap_or(Payload::Eof);
    Item { leading, payload }
}

/// Complete an already-accepted Pattern's successor.  A colon here belongs to
/// the Pattern tail judge (or its caller), never to a fresh Symbol primary.
pub(super) fn pattern_item_after_trivia<S>(
    i: In<'_, &str, &mut Recover<'_>, S>,
    leading: LeadingTrivia,
) -> Item
where
    S: Rb,
{
    let payload = i
        .map(token(scan_pattern_tail_token), Payload::Token)
        .unwrap_or(Payload::Eof);
    Item { leading, payload }
}

fn scan_pattern_tail_token(mut i: LexIn) -> Option<Token> {
    i.check(choice((
        token(scan_pattern_colon),
        token(scan_path_segment),
        token(scan_integer),
        token(scan_record_spread_marker),
        token(scan_exact_equals),
        token(scan_pattern_pipe),
        choice((
            token(scan_pattern_malformed_fixed_operator),
            token(scan_punctuation),
            token(scan_unknown),
        )),
    )))
}

/// Keep a rejected exact record marker or field introducer as one malformed
/// item.  This comes after their exact scanners, so plain `.` remains a
/// punctuation token and exact `..` / `=` retain their normal owners.
fn scan_pattern_malformed_fixed_operator(i: LexIn) -> Option<Token> {
    (i.remainder().starts_with("..") || i.remainder().starts_with('=')).then_some(())?;
    scan_operator_shaped_unknown(i)
}

pub(super) fn scan_operator_shaped_unknown(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut operator| {
        scan_operator_shaped_character(operator.rb())?;
        while operator.token(scan_operator_shaped_character).is_some() {}
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Unknown,
        text: text.into(),
    })
}

pub(super) fn is_operator_shaped_unknown(item: &Item) -> bool {
    matches!(
        &item.payload,
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text,
        }) if text.chars().all(is_operator_shaped_character)
    )
}

pub(super) fn scan_trivia<S>(mut i: In<'_, &str, &mut Recover<'_>, S>) -> LeadingTrivia
where
    S: Rb,
{
    let mut parts = Vec::new();
    while let Some(part) = i.token(scan_trivia_part) {
        parts.push(part);
    }
    LeadingTrivia(parts.into_boxed_slice())
}

fn scan_trivia_part(mut i: LexIn) -> Option<Trivia> {
    i.check(choice((
        token(scan_horizontal_whitespace),
        token(scan_newline),
        token(scan_line_comment),
        token(scan_block_comment),
    )))
}

fn scan_horizontal_whitespace(mut i: LexIn) -> Option<Trivia> {
    let (accepted, text) = i.rb().with_str(|mut whitespace| {
        scan_horizontal_whitespace_unit(whitespace.rb())?;
        while whitespace.token(scan_horizontal_whitespace_unit).is_some() {}
        Some(())
    });
    accepted?;
    Some(Trivia {
        kind: TriviaKind::Whitespace,
        text: text.into(),
    })
}

fn scan_horizontal_whitespace_unit(mut i: LexIn) -> Option<()> {
    matches!(i.next()?, ' ' | '\t').then_some(())
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
    Some(Trivia {
        kind: TriviaKind::Newline,
        text: text.into(),
    })
}

fn scan_line_feed(mut i: LexIn) -> Option<()> {
    (i.next()? == '\n').then_some(())
}

fn scan_line_comment(mut i: LexIn) -> Option<Trivia> {
    let (accepted, text) = i.rb().with_str(|mut comment| {
        scan_pair(comment.rb(), '/', '/')?;
        while comment.token(scan_line_comment_character).is_some() {}
        Some(())
    });
    accepted?;
    Some(Trivia {
        kind: TriviaKind::LineComment,
        text: text.into(),
    })
}

fn scan_line_comment_character(mut i: LexIn) -> Option<()> {
    (!matches!(i.next()?, '\r' | '\n')).then_some(())
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
    Some(Trivia {
        kind: TriviaKind::BlockComment,
        text: text.into(),
    })
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

pub(super) fn scan_identifier(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut word| {
        if !identifier_starts(word.remainder()) {
            return None;
        }
        let _ = word.next()?;
        while word.token(scan_identifier_continue).is_some() {}
        let _ = word.token(scan_identifier_suffix);
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

pub(super) fn scan_path_segment(mut i: LexIn) -> Option<Token> {
    if let Some(mut word) = i.token(scan_identifier) {
        if word.text.starts_with('_') && &*word.text != "_" {
            word.kind = TokenKind::SigilIdentifier;
        }
        return Some(word);
    }

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

fn scan_identifier_continue(mut i: LexIn) -> Option<()> {
    is_xid_continue(i.next()?).then_some(())
}

fn scan_identifier_suffix(mut i: LexIn) -> Option<()> {
    matches!(i.next()?, '?' | '!').then_some(())
}

pub(super) fn scan_integer(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut number| {
        scan_integer_digit(number.rb())?;
        while number.token(scan_integer_digit).is_some() {}
        Some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Integer,
        text: text.into(),
    })
}

fn scan_integer_digit(mut i: LexIn) -> Option<()> {
    i.next()?.is_ascii_digit().then_some(())
}

pub(super) fn scan_punctuation(i: LexIn) -> Option<Token> {
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
    let remainder = i.remainder();
    (remainder.starts_with(':') && !remainder.starts_with("::")).then_some(())?;
    let (accepted, text) = i
        .rb()
        .with_str(|mut colon| (colon.next()? == ':').then_some(()));
    accepted?;
    Some(Token {
        kind: TokenKind::Colon,
        text: text.into(),
    })
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

fn scan_type_polymorphic_variant_colon(mut i: LexIn) -> Option<Token> {
    i.remainder().starts_with(":{").then_some(())?;
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
    let remainder = i.remainder();
    (remainder.starts_with(':') && !remainder.starts_with("::")).then_some(())?;
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
    let remainder = i.remainder();
    (remainder.starts_with(':') && !remainder.starts_with("::")).then_some(())?;
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

fn scan_pattern_pipe(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i
        .rb()
        .with_str(|mut pipe| (pipe.next()? == '|').then_some(()));
    accepted?;
    Some(Token {
        kind: TokenKind::Pipe,
        text: text.into(),
    })
}

/// Fixed `=` spellings accept only the maximal operator-shaped spelling `=`.
pub(super) fn scan_exact_equals(i: LexIn) -> Option<Token> {
    let (accepted, text) = i.with_str(|mut equals| {
        (equals.next()? == '=').then_some(())?;
        equals
            .token(scan_operator_shaped_character)
            .is_none()
            .then_some(())
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Equals,
        text: text.into(),
    })
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

fn scan_lparen(i: LexIn) -> Option<Token> {
    let token = scan_punctuation(i)?;
    (token.kind == TokenKind::LParen).then_some(token)
}

pub(super) fn scan_lbrace(i: LexIn) -> Option<Token> {
    let token = scan_punctuation(i)?;
    (token.kind == TokenKind::LBrace).then_some(token)
}

pub(super) fn scan_lbracket(i: LexIn) -> Option<Token> {
    let token = scan_punctuation(i)?;
    (token.kind == TokenKind::LBracket).then_some(token)
}

/// Captures the remainder of a bracketed malformed head only after its
/// matching close is known.  Trivia stays opaque so a bracket in a comment
/// cannot terminate the balanced range.
pub(super) fn scan_balanced_bracket_suffix(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut suffix| {
        let mut depth = 1usize;
        loop {
            if suffix.token(scan_trivia_part).is_some() {
                continue;
            }
            match suffix.next()? {
                '[' => depth += 1,
                ']' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(());
                    }
                }
                _ => {}
            }
        }
    });
    accepted?;
    Some(Token {
        kind: TokenKind::Unknown,
        text: text.into(),
    })
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

pub(super) fn scan_unknown(i: LexIn) -> Option<Token> {
    let (character, text) = i.with_str(|mut one| one.next());
    character?;
    Some(Token {
        kind: TokenKind::Unknown,
        text: text.into(),
    })
}
