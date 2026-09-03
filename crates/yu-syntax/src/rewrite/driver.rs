//! Source-free direct recursive-descent foundation for the isolated rewrite.

use chasa_recover::{
    In,
    parser::{choice, token},
};
use reborrow_generic::Reborrow as _;
use rowan::GreenNodeBuilder;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{
    operator::{BindingPower, OperatorFixity},
    scan::operator::{OperatorSite, is_call_or_path_sensitive, judge_operator},
    syntax_kind::SyntaxKind,
};

use super::{
    item::{
        Item, LeadingTrivia, OperatorToken, OperatorUse, Payload, Token, TokenKind, Trivia,
        TriviaKind,
    },
    state::Recover,
};

pub(super) type RewriteIn<'a, 'source, 'recover, 'operators, 'builder> = In<
    'a,
    &'source str,
    &'recover mut Recover<'operators>,
    &'builder mut GreenNodeBuilder<'static>,
>;

type LexIn<'a, 'source, 'recover, 'operators> =
    In<'a, &'source str, &'recover mut Recover<'operators>, ()>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum Either<L, R> {
    Left(L),
    Right(R),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct End {
    pub(super) item: Item,
}

/// `Ok(())` means an accepted child owner closed normally; its caller scans
/// the successor item only after closing that owner's Rowan node.
pub(super) type TailExit = Result<(), Either<Item, End>>;

const STOP_COMMA: u8 = 1 << 0;
const STOP_SEMICOLON: u8 = 1 << 1;
const STOP_RPAREN: u8 = 1 << 2;
const STOP_RBRACKET: u8 = 1 << 3;
const STOP_RBRACE: u8 = 1 << 4;

/// `None` occurs only before the lexical transaction has accepted a NUD.
pub(super) fn expr(mut i: RewriteIn) -> Option<TailExit> {
    expr_at(i.rb(), None, 0, 0, true)
}

fn expr_at(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> Option<TailExit> {
    let nud = i.token(|lex| scan_nud_item(lex, baseline, stops))?;
    Some(expr_from_nud(
        i, nud, threshold, baseline, stops, accepts_ml,
    ))
}

/// Parses an already-accepted NUD without scanning it again.
fn expr_from_nud(
    mut i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = append_nud(i.rb(), nud, threshold, baseline, stops, accepts_ml);
    i.state.finish_node();
    exit
}

/// Appends an accepted NUD to the active `OperatorChain` owner.
fn append_nud(
    mut i: RewriteIn,
    nud: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    match token_kind(&nud) {
        Some(TokenKind::Identifier) => {
            emit_identifier_core(&mut i, nud);
            scan_tail_after_accept(i.rb(), threshold, baseline, stops, accepts_ml)
        }
        Some(TokenKind::Integer) => {
            emit_integer_core(&mut i, nud);
            scan_tail_after_accept(i.rb(), threshold, baseline, stops, accepts_ml)
        }
        Some(TokenKind::LParen) => {
            parenthesized_nud(i.rb(), nud, threshold, baseline, stops, accepts_ml)
        }
        Some(TokenKind::Operator) => {
            operator_nud(i.rb(), nud, threshold, baseline, stops, accepts_ml)
        }
        _ => unreachable!("the NUD scanner accepts only normal core items and `(`"),
    }
}

fn expr_after_accept(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    if is_nud_item(&item) {
        append_nud(i, item, threshold, baseline, stops, accepts_ml)
    } else {
        handoff(item)
    }
}

fn scan_tail_after_accept(
    mut i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let next = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
    tail(i, next, threshold, baseline, stops, accepts_ml)
}

fn continue_completed_tail(
    i: RewriteIn,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
    exit: TailExit,
) -> TailExit {
    match exit {
        Ok(()) => scan_tail_after_accept(i, threshold, baseline, stops, accepts_ml),
        Err(Either::Left(item)) => tail(i, item, threshold, baseline, stops, accepts_ml),
        Err(Either::Right(end)) => Err(Either::Right(end)),
    }
}

/// Unaccepted items are returned unchanged and receive no builder effect.
pub(super) fn tail(
    mut i: RewriteIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    if item.leading.0.is_empty() {
        match token_kind(&item) {
            Some(TokenKind::LParen) => {
                return call_tail(i.rb(), item, threshold, baseline, stops, accepts_ml);
            }
            Some(TokenKind::LBracket) => {
                return index_tail(i.rb(), item, threshold, baseline, stops, accepts_ml);
            }
            _ => {}
        }
    }
    match token_kind(&item) {
        Some(TokenKind::Dot) => {
            return dot_tail(i.rb(), item, threshold, baseline, stops, accepts_ml);
        }
        Some(TokenKind::PathSeparator) => {
            return path_tail(i.rb(), item, threshold, baseline, stops, accepts_ml);
        }
        Some(TokenKind::Operator) if is_led_operator(&item) => {
            return operator_tail(i.rb(), item, threshold, baseline, stops, accepts_ml);
        }
        _ => {}
    }
    if accepts_ml && is_ml_argument(&item) {
        return ml_argument(i.rb(), item, threshold, baseline, stops);
    }
    handoff(item)
}

fn is_ml_argument(item: &Item) -> bool {
    is_nud_item(item)
        && !item.leading.0.is_empty()
        && item
            .leading
            .0
            .iter()
            .all(|part| part.kind == TriviaKind::Whitespace)
}

fn is_led_operator(item: &Item) -> bool {
    matches!(
        operator_use(item),
        Some(OperatorUse::Infix { .. } | OperatorUse::Suffix(_))
    )
}

fn ml_argument(
    mut i: RewriteIn,
    argument: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
) -> TailExit {
    i.state.start_node(SyntaxKind::MlArgument.into());
    let exit = expr_from_nud(i.rb(), argument, threshold, baseline, stops, false);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, true, exit)
}

fn operator_nud(
    mut i: RewriteIn,
    operator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    match operator_use(&operator) {
        Some(OperatorUse::Prefix(right)) => {
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::PrefixOperatorUse);
            let rhs = expr_after_accept(i.rb(), Some(&right), baseline, stops, accepts_ml);
            continue_completed_tail(i, threshold, baseline, stops, accepts_ml, rhs)
        }
        Some(OperatorUse::Nullfix) => {
            emit_operator_use(&mut i, operator, SyntaxKind::NullfixOperatorUse);
            scan_tail_after_accept(i, threshold, baseline, stops, accepts_ml)
        }
        _ => unreachable!("the NUD scanner accepts only prefix and nullfix operators"),
    }
}

fn operator_tail(
    mut i: RewriteIn,
    operator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    match operator_use(&operator) {
        Some(OperatorUse::Infix { left, right }) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return handoff(operator);
            }
            let right = right.clone();
            emit_operator_use(&mut i, operator, SyntaxKind::InfixOperatorUse);
            let rhs = expr_after_accept(i.rb(), Some(&right), baseline, stops, accepts_ml);
            continue_completed_tail(i, threshold, baseline, stops, accepts_ml, rhs)
        }
        Some(OperatorUse::Suffix(left)) => {
            if threshold.is_some_and(|minimum| left < minimum) {
                return handoff(operator);
            }
            emit_operator_use(&mut i, operator, SyntaxKind::SuffixOperatorUse);
            scan_tail_after_accept(i, threshold, baseline, stops, accepts_ml)
        }
        _ => unreachable!("the LED scanner accepts only infix and suffix operators"),
    }
}

fn parenthesized_nud(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedExpression.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RParen, None, baseline, accepts_ml);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, accepts_ml, exit)
}

fn delimited_items(
    mut i: RewriteIn,
    close: TokenKind,
    item_node: Option<SyntaxKind>,
    incoming_baseline: usize,
    accepts_ml: bool,
) -> TailExit {
    let stops = stops_for(close);
    let leading = scan_trivia(i.rb());
    let baseline = delimited_baseline(incoming_baseline, &leading);
    let mut item = tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops);
    loop {
        if token_kind(&item) == Some(close) {
            emit_token_item(&mut i, item);
            return Ok(());
        }

        if !is_nud_item(&item) {
            return handoff(item);
        }
        if let Some(kind) = item_node {
            i.state.start_node(kind.into());
        }
        let exit = expr_from_item(i.rb(), item, None, baseline, stops, accepts_ml);
        if item_node.is_some() {
            i.state.finish_node();
        }
        item = match exit {
            Err(Either::Left(next)) if is_separator(&next) => {
                emit_token_item(&mut i, next);
                let leading = scan_trivia(i.rb());
                tail_item_after_trivia(i.rb(), leading, OperatorSite::Nud, baseline, stops)
            }
            Err(Either::Left(next)) if token_kind(&next) == Some(close) => {
                emit_token_item(&mut i, next);
                return Ok(());
            }
            exit => return exit,
        };
    }
}

fn is_nud_item(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Identifier | TokenKind::Integer | TokenKind::LParen)
    ) || matches!(
        operator_use(item),
        Some(OperatorUse::Prefix(_) | OperatorUse::Nullfix)
    )
}

fn expr_from_item(
    i: RewriteIn,
    item: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    expr_from_nud(i, item, threshold, baseline, stops, accepts_ml)
}

fn call_tail(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::CallTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RParen, None, baseline, accepts_ml);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, accepts_ml, exit)
}

fn index_tail(
    mut i: RewriteIn,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::IndexTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RBracket,
        Some(SyntaxKind::IndexItem),
        baseline,
        accepts_ml,
    );
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, accepts_ml, exit)
}

fn dot_tail(
    mut i: RewriteIn,
    dot: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    let leading = scan_trivia(i.rb());
    let next = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
    if next.leading.0.is_empty() {
        match token_kind(&next) {
            Some(TokenKind::LParen) => {
                return projection_tuple_tail(i, dot, next, threshold, baseline, stops, accepts_ml);
            }
            Some(TokenKind::LBrace) => {
                return projection_record_tail(
                    i, dot, next, threshold, baseline, stops, accepts_ml,
                );
            }
            _ => {}
        }
    }
    field_tail(i, dot, next, threshold, baseline, stops, accepts_ml)
}

fn field_tail(
    mut i: RewriteIn,
    dot: Item,
    name: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::FieldTail.into());
    emit_token_item(&mut i, dot);
    if token_kind(&name) != Some(TokenKind::Identifier) || !name.leading.0.is_empty() {
        i.state.finish_node();
        return handoff(name);
    }
    emit_token_item(&mut i, name);
    i.state.finish_node();
    scan_tail_after_accept(i, threshold, baseline, stops, accepts_ml)
}

fn projection_tuple_tail(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionTupleTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RParen, None, baseline, accepts_ml);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, accepts_ml, exit)
}

fn projection_record_tail(
    mut i: RewriteIn,
    dot: Item,
    open: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionRecordTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RBrace, None, baseline, accepts_ml);
    i.state.finish_node();
    continue_completed_tail(i, threshold, baseline, stops, accepts_ml, exit)
}

fn path_tail(
    mut i: RewriteIn,
    separator: Item,
    threshold: Option<&BindingPower>,
    baseline: usize,
    stops: u8,
    accepts_ml: bool,
) -> TailExit {
    i.state.start_node(SyntaxKind::PathTail.into());
    emit_token_item(&mut i, separator);
    let leading = scan_trivia(i.rb());
    let segment = tail_item_after_trivia(i.rb(), leading, OperatorSite::Led, baseline, stops);
    if token_kind(&segment) != Some(TokenKind::Identifier) {
        i.state.finish_node();
        return handoff(segment);
    }
    emit_token_item(&mut i, segment);
    i.state.finish_node();
    scan_tail_after_accept(i, threshold, baseline, stops, accepts_ml)
}

fn is_separator(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Comma | TokenKind::Semicolon)
    )
}

fn handoff(item: Item) -> TailExit {
    match item.payload {
        Payload::Eof => Err(Either::Right(End { item })),
        Payload::Token(_) | Payload::Operator(_) => Err(Either::Left(item)),
    }
}

fn token_kind(item: &Item) -> Option<TokenKind> {
    match &item.payload {
        Payload::Token(token) => Some(token.kind),
        Payload::Operator(_) => Some(TokenKind::Operator),
        Payload::Eof => None,
    }
}

fn operator_use(item: &Item) -> Option<&OperatorUse> {
    let Payload::Operator(operator) = &item.payload else {
        return None;
    };
    Some(&operator.use_)
}

fn stops_for(close: TokenKind) -> u8 {
    let close = match close {
        TokenKind::RParen => STOP_RPAREN,
        TokenKind::RBracket => STOP_RBRACKET,
        TokenKind::RBrace => STOP_RBRACE,
        _ => unreachable!("only a matching close owns a delimited stop set"),
    };
    STOP_COMMA | STOP_SEMICOLON | close
}

fn active_stop(source: &str, stops: u8) -> bool {
    match source.chars().next() {
        Some(',') => stops & STOP_COMMA != 0,
        Some(';') => stops & STOP_SEMICOLON != 0,
        Some(')') => stops & STOP_RPAREN != 0,
        Some(']') => stops & STOP_RBRACKET != 0,
        Some('}') => stops & STOP_RBRACE != 0,
        _ => false,
    }
}

fn delimited_baseline(incoming: usize, leading: &LeadingTrivia) -> usize {
    let mut at_line_start = false;
    let mut indentation = 0usize;

    for part in &leading.0 {
        for character in part.text.chars() {
            match character {
                '\r' | '\n' => {
                    at_line_start = true;
                    indentation = 0;
                }
                ' ' | '\t' if at_line_start => indentation += 1,
                _ => at_line_start = false,
            }
        }
    }

    (at_line_start && indentation > incoming)
        .then_some(indentation)
        .unwrap_or(incoming)
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum RawTrailing {
    None,
    Space,
    Newline { indentation: usize },
}

fn raw_trivia_character(
    character: char,
    saw_newline: &mut bool,
    at_line_start: &mut bool,
    indentation: &mut usize,
) {
    match character {
        '\r' | '\n' => {
            *saw_newline = true;
            *at_line_start = true;
            *indentation = 0;
        }
        ' ' | '\t' if *at_line_start => *indentation += 1,
        _ => *at_line_start = false,
    }
}

fn raw_trivia_suffix(mut source: &str) -> (RawTrailing, &str) {
    let mut present = false;
    let mut saw_newline = false;
    let mut at_line_start = false;
    let mut indentation = 0usize;

    loop {
        let before = source;
        while let Some(character) = source.chars().next() {
            if !matches!(character, ' ' | '\t' | '\r' | '\n') {
                break;
            }
            present = true;
            raw_trivia_character(
                character,
                &mut saw_newline,
                &mut at_line_start,
                &mut indentation,
            );
            source = &source[character.len_utf8()..];
        }
        if source.starts_with("//") {
            present = true;
            source = &source[2..];
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            raw_trivia_character('/', &mut saw_newline, &mut at_line_start, &mut indentation);
            while let Some(character) = source.chars().next() {
                if matches!(character, '\r' | '\n') {
                    break;
                }
                raw_trivia_character(
                    character,
                    &mut saw_newline,
                    &mut at_line_start,
                    &mut indentation,
                );
                source = &source[character.len_utf8()..];
            }
            continue;
        }
        if source.starts_with("/*") {
            present = true;
            let comment = source;
            source = raw_block_comment_suffix(source);
            let consumed = comment.len() - source.len();
            for character in comment[..consumed].chars() {
                raw_trivia_character(
                    character,
                    &mut saw_newline,
                    &mut at_line_start,
                    &mut indentation,
                );
            }
            continue;
        }
        if source.len() == before.len() {
            let trailing = if !present {
                RawTrailing::None
            } else if saw_newline {
                RawTrailing::Newline { indentation }
            } else {
                RawTrailing::Space
            };
            return (trailing, source);
        }
    }
}

fn raw_block_comment_suffix(mut source: &str) -> &str {
    debug_assert!(source.starts_with("/*"));
    source = &source[2..];
    let mut depth = 1usize;
    while !source.is_empty() {
        if source.starts_with("/*") {
            depth += 1;
            source = &source[2..];
            continue;
        }
        if source.starts_with("*/") {
            depth -= 1;
            source = &source[2..];
            if depth == 0 {
                return source;
            }
            continue;
        }
        let character = source
            .chars()
            .next()
            .expect("a non-empty UTF-8 suffix has one character");
        source = &source[character.len_utf8()..];
    }
    source
}

fn tail_item_after_trivia(
    mut i: RewriteIn,
    leading: LeadingTrivia,
    site: OperatorSite,
    baseline: usize,
    stops: u8,
) -> Item {
    let has_leading_trivia = !leading.0.is_empty();
    let payload = if let Some(operator) =
        i.token(|lex| scan_operator(lex, site, has_leading_trivia, baseline, stops))
    {
        Payload::Operator(operator)
    } else {
        i.map(
            choice((
                token(scan_identifier),
                token(scan_integer),
                token(scan_punctuation),
                token(scan_unknown),
            )),
            Payload::Token,
        )
        .unwrap_or(Payload::Eof)
    };
    Item { leading, payload }
}

fn scan_nud_item(mut i: LexIn, baseline: usize, stops: u8) -> Option<Item> {
    let leading = scan_trivia_lex(i.rb());
    let has_leading_trivia = !leading.0.is_empty();
    let payload = if let Some(token) = i.token(scan_lparen) {
        Payload::Token(token)
    } else if let Some(operator) =
        i.token(|lex| scan_operator(lex, OperatorSite::Nud, has_leading_trivia, baseline, stops))
    {
        Payload::Operator(operator)
    } else if let Some(token) = i.token(scan_identifier) {
        Payload::Token(token)
    } else {
        Payload::Token(i.token(scan_integer)?)
    };
    Some(Item { leading, payload })
}

fn scan_trivia(mut i: RewriteIn) -> LeadingTrivia {
    let mut parts = Vec::new();
    while let Some(part) = i.token(scan_trivia_part) {
        parts.push(part);
    }
    LeadingTrivia(parts.into_boxed_slice())
}

fn scan_trivia_lex(mut i: LexIn) -> LeadingTrivia {
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

fn scan_identifier(mut i: LexIn) -> Option<Token> {
    let (accepted, text) = i.rb().with_str(|mut word| {
        let first = word.next()?;
        if first != '_' && !is_xid_start(first) {
            return None;
        }
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

fn scan_identifier_continue(mut i: LexIn) -> Option<()> {
    is_xid_continue(i.next()?).then_some(())
}

fn scan_identifier_suffix(mut i: LexIn) -> Option<()> {
    matches!(i.next()?, '?' | '!').then_some(())
}

fn scan_integer(mut i: LexIn) -> Option<Token> {
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

pub(super) fn scan_operator(
    mut i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    baseline: usize,
    stops: u8,
) -> Option<OperatorToken> {
    let table = i.recovery().operators();
    let source = i.remainder();
    let (use_, end) = table.longest_source_match_then(source, |last, entry, end| {
        operator_boundary(last, &source[end..])?;

        let (trailing, after_trivia) = raw_trivia_suffix(&source[end..]);
        let kinds = entry.fixities().kinds();
        if is_call_or_path_sensitive(kinds)
            && trailing == RawTrailing::None
            && matches!(after_trivia.chars().next(), Some('(' | ':'))
        {
            return None;
        }

        let post_whitespace = trailing != RawTrailing::None
            || after_trivia.is_empty()
            || active_stop(after_trivia, stops);
        let value_start = raw_value_start(table, trailing, after_trivia, baseline);
        let with_value = judge_operator(site, kinds, has_leading_trivia, post_whitespace, true);
        let without_value = judge_operator(site, kinds, has_leading_trivia, post_whitespace, false);
        let fixity = if is_call_or_path_sensitive(kinds) && post_whitespace && value_start {
            Some(OperatorFixity::Prefix)
        } else if with_value != without_value {
            if value_start {
                with_value
            } else {
                without_value
            }
        } else {
            with_value
        }?;
        selected_operator_use(entry.fixities(), fixity)
    })?;
    let character_count = source[..end].chars().count();
    let (accepted, text) = i.with_str(|mut operator| {
        for _ in 0..character_count {
            operator.next()?;
        }
        Some(())
    });
    accepted?;
    Some(OperatorToken {
        text: text.into(),
        use_,
    })
}

fn operator_boundary(last: char, following: &str) -> Option<()> {
    (!is_xid_continue(last)
        || following
            .chars()
            .next()
            .is_none_or(|character| !is_xid_continue(character)))
    .then_some(())
}

fn raw_value_start(
    table: &crate::operator::OperatorTable,
    trailing: RawTrailing,
    source: &str,
    baseline: usize,
) -> bool {
    if matches!(trailing, RawTrailing::Newline { indentation } if indentation <= baseline) {
        return false;
    }

    match source.chars().next() {
        Some('"' | '(' | '[' | '{' | '$' | '\\' | '%' | '_' | '\'') => true,
        Some(character)
            if is_xid_start(character) || character.is_ascii_digit() || character == '.' =>
        {
            true
        }
        _ => table.value_start_source_len(source).is_some(),
    }
}

fn selected_operator_use(
    fixities: &crate::operator::OperatorFixities,
    fixity: OperatorFixity,
) -> Option<OperatorUse> {
    match fixity {
        OperatorFixity::Prefix => Some(OperatorUse::Prefix(
            fixities.prefix()?.right_binding_power().clone(),
        )),
        OperatorFixity::Infix => {
            let infix = fixities.infix()?;
            Some(OperatorUse::Infix {
                left: infix.left_binding_power().clone(),
                right: infix.right_binding_power().clone(),
            })
        }
        OperatorFixity::Suffix => Some(OperatorUse::Suffix(
            fixities.suffix()?.left_binding_power().clone(),
        )),
        OperatorFixity::Nullfix => fixities.is_nullfix().then_some(OperatorUse::Nullfix),
    }
}

fn scan_punctuation(i: LexIn) -> Option<Token> {
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

fn scan_lparen(i: LexIn) -> Option<Token> {
    let token = scan_punctuation(i)?;
    (token.kind == TokenKind::LParen).then_some(token)
}

fn scan_dot(mut i: LexIn) -> Option<()> {
    (i.next()? == '.').then_some(())
}

fn scan_unknown(i: LexIn) -> Option<Token> {
    let (character, text) = i.with_str(|mut one| one.next());
    character?;
    Some(Token {
        kind: TokenKind::Unknown,
        text: text.into(),
    })
}

fn emit_identifier_core(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("a core scanner always returns a token")
    };
    debug_assert_eq!(token.kind, TokenKind::Identifier);
    i.state.start_node(SyntaxKind::IdentifierExpression.into());
    emit_trivia(i, &item.leading);
    i.state.token(SyntaxKind::Identifier.into(), &token.text);
    i.state.finish_node();
}

fn emit_integer_core(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("a core scanner always returns a token")
    };
    debug_assert_eq!(token.kind, TokenKind::Integer);
    i.state.start_node(SyntaxKind::IntegerLiteral.into());
    emit_trivia(i, &item.leading);
    i.state.token(SyntaxKind::Integer.into(), &token.text);
    i.state.finish_node();
}

fn emit_operator_use(i: &mut RewriteIn, item: Item, kind: SyntaxKind) {
    let Payload::Operator(operator) = item.payload else {
        unreachable!("an operator use always owns an operator token")
    };
    i.state.start_node(kind.into());
    emit_trivia(i, &item.leading);
    i.state.token(SyntaxKind::Operator.into(), &operator.text);
    i.state.finish_node();
}

fn emit_token_item(i: &mut RewriteIn, item: Item) {
    emit_trivia(i, &item.leading);
    match item.payload {
        Payload::Operator(operator) => {
            i.state.token(SyntaxKind::Operator.into(), &operator.text);
        }
        Payload::Token(token) => {
            let kind = match token.kind {
                TokenKind::Identifier => SyntaxKind::Identifier,
                TokenKind::Integer => SyntaxKind::Integer,
                TokenKind::Operator => unreachable!("operators have a selected dynamic role"),
                TokenKind::LParen => SyntaxKind::LParen,
                TokenKind::RParen => SyntaxKind::RParen,
                TokenKind::LBracket => SyntaxKind::LBracket,
                TokenKind::RBracket => SyntaxKind::RBracket,
                TokenKind::LBrace => SyntaxKind::LBrace,
                TokenKind::RBrace => SyntaxKind::RBrace,
                TokenKind::Comma => SyntaxKind::Comma,
                TokenKind::Semicolon => SyntaxKind::Semicolon,
                TokenKind::Dot => SyntaxKind::Dot,
                TokenKind::PathSeparator => SyntaxKind::ColonColon,
                TokenKind::Unknown => SyntaxKind::Unknown,
            };
            i.state.token(kind.into(), &token.text);
        }
        Payload::Eof => unreachable!("only a lexical item can be emitted"),
    }
}

/// The enclosing owner emits accepted EOF trivia after receiving `End`.
pub(super) fn emit_end(builder: &mut GreenNodeBuilder<'static>, end: &End) {
    emit_trivia_builder(builder, &end.item.leading);
}

fn emit_trivia(i: &mut RewriteIn, trivia: &LeadingTrivia) {
    emit_trivia_builder(&mut *i.state, trivia);
}

fn emit_trivia_builder(builder: &mut GreenNodeBuilder<'static>, trivia: &LeadingTrivia) {
    for part in &trivia.0 {
        let kind = match part.kind {
            TriviaKind::Whitespace => SyntaxKind::Whitespace,
            TriviaKind::Newline => SyntaxKind::Newline,
            TriviaKind::LineComment => SyntaxKind::LineComment,
            TriviaKind::BlockComment => SyntaxKind::BlockComment,
        };
        builder.token(kind.into(), &part.text);
    }
}
