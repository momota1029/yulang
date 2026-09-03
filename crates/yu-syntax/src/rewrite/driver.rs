//! Source-free direct recursive-descent foundation for the isolated rewrite.

use chasa_recover::{
    In,
    parser::{choice, token},
};
use reborrow_generic::Reborrow as _;
use rowan::GreenNodeBuilder;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::syntax_kind::SyntaxKind;

use super::{
    item::{Item, LeadingTrivia, Payload, Token, TokenKind, Trivia, TriviaKind},
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

/// `None` occurs only before the lexical transaction has accepted a NUD.
pub(super) fn expr(mut i: RewriteIn) -> Option<TailExit> {
    let nud = i.token(scan_nud_item)?;
    Some(expr_from_nud(i, nud, true))
}

/// Parses an already-accepted NUD without scanning it again.
fn expr_from_nud(mut i: RewriteIn, nud: Item, accepts_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::OperatorChain.into());
    let exit = match token_kind(&nud) {
        Some(TokenKind::Identifier) => {
            emit_core(&mut i, nud);
            scan_tail_after_accept(i.rb(), accepts_ml)
        }
        Some(TokenKind::LParen) => parenthesized_nud(i.rb(), nud, accepts_ml),
        _ => unreachable!("the NUD scanner accepts only identifier and `(`"),
    };
    i.state.finish_node();
    exit
}

fn scan_tail_after_accept(mut i: RewriteIn, accepts_ml: bool) -> TailExit {
    let next = tail_item(i.rb());
    tail(i.rb(), next, accepts_ml)
}

fn continue_completed_tail(i: RewriteIn, accepts_ml: bool, exit: TailExit) -> TailExit {
    match exit {
        Ok(()) => scan_tail_after_accept(i, accepts_ml),
        exit => exit,
    }
}

/// Unaccepted items are returned unchanged and receive no builder effect.
pub(super) fn tail(mut i: RewriteIn, item: Item, accepts_ml: bool) -> TailExit {
    if item.leading.0.is_empty() {
        match token_kind(&item) {
            Some(TokenKind::LParen) => return call_tail(i.rb(), item, accepts_ml),
            Some(TokenKind::LBracket) => return index_tail(i.rb(), item, accepts_ml),
            _ => {}
        }
    }
    match token_kind(&item) {
        Some(TokenKind::Dot) => return dot_tail(i.rb(), item, accepts_ml),
        Some(TokenKind::PathSeparator) => return path_tail(i.rb(), item, accepts_ml),
        _ => {}
    }
    if accepts_ml && is_ml_argument(&item) {
        return ml_argument(i.rb(), item);
    }
    handoff(item)
}

fn is_ml_argument(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
        && !item.leading.0.is_empty()
        && item
            .leading
            .0
            .iter()
            .all(|part| part.kind == TriviaKind::Whitespace)
}

fn ml_argument(mut i: RewriteIn, argument: Item) -> TailExit {
    i.state.start_node(SyntaxKind::MlArgument.into());
    let exit = expr_from_nud(i.rb(), argument, false);
    i.state.finish_node();
    match exit {
        Err(Either::Left(next)) => tail(i, next, true),
        exit => exit,
    }
}

fn parenthesized_nud(mut i: RewriteIn, open: Item, accepts_ml: bool) -> TailExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedExpression.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RParen, None, accepts_ml);
    i.state.finish_node();
    continue_completed_tail(i, accepts_ml, exit)
}

fn delimited_items(
    mut i: RewriteIn,
    close: TokenKind,
    item_node: Option<SyntaxKind>,
    accepts_ml: bool,
) -> TailExit {
    let mut item = tail_item(i.rb());
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
        let exit = expr_from_item(i.rb(), item, accepts_ml);
        if item_node.is_some() {
            i.state.finish_node();
        }
        item = match exit {
            Err(Either::Left(next)) if is_separator(&next) => {
                emit_token_item(&mut i, next);
                tail_item(i.rb())
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
        Some(TokenKind::Identifier | TokenKind::LParen)
    )
}

fn expr_from_item(i: RewriteIn, item: Item, accepts_ml: bool) -> TailExit {
    debug_assert!(is_nud_item(&item));
    expr_from_nud(i, item, accepts_ml)
}

fn call_tail(mut i: RewriteIn, open: Item, accepts_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::CallTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RParen, None, accepts_ml);
    i.state.finish_node();
    continue_completed_tail(i, accepts_ml, exit)
}

fn index_tail(mut i: RewriteIn, open: Item, accepts_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::IndexTail.into());
    emit_token_item(&mut i, open);
    let exit = delimited_items(
        i.rb(),
        TokenKind::RBracket,
        Some(SyntaxKind::IndexItem),
        accepts_ml,
    );
    i.state.finish_node();
    continue_completed_tail(i, accepts_ml, exit)
}

fn dot_tail(mut i: RewriteIn, dot: Item, accepts_ml: bool) -> TailExit {
    let next = tail_item(i.rb());
    if next.leading.0.is_empty() {
        match token_kind(&next) {
            Some(TokenKind::LParen) => return projection_tuple_tail(i, dot, next, accepts_ml),
            Some(TokenKind::LBrace) => return projection_record_tail(i, dot, next, accepts_ml),
            _ => {}
        }
    }
    field_tail(i, dot, next, accepts_ml)
}

fn field_tail(mut i: RewriteIn, dot: Item, name: Item, accepts_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::FieldTail.into());
    emit_token_item(&mut i, dot);
    if token_kind(&name) != Some(TokenKind::Identifier) || !name.leading.0.is_empty() {
        i.state.finish_node();
        return handoff(name);
    }
    emit_token_item(&mut i, name);
    i.state.finish_node();
    scan_tail_after_accept(i, accepts_ml)
}

fn projection_tuple_tail(mut i: RewriteIn, dot: Item, open: Item, accepts_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionTupleTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RParen, None, accepts_ml);
    i.state.finish_node();
    continue_completed_tail(i, accepts_ml, exit)
}

fn projection_record_tail(mut i: RewriteIn, dot: Item, open: Item, accepts_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::ProjectionRecordTail.into());
    emit_token_item(&mut i, dot);
    emit_token_item(&mut i, open);
    let exit = delimited_items(i.rb(), TokenKind::RBrace, None, accepts_ml);
    i.state.finish_node();
    continue_completed_tail(i, accepts_ml, exit)
}

fn path_tail(mut i: RewriteIn, separator: Item, accepts_ml: bool) -> TailExit {
    i.state.start_node(SyntaxKind::PathTail.into());
    emit_token_item(&mut i, separator);
    let segment = tail_item(i.rb());
    if token_kind(&segment) != Some(TokenKind::Identifier) {
        i.state.finish_node();
        return handoff(segment);
    }
    emit_token_item(&mut i, segment);
    i.state.finish_node();
    scan_tail_after_accept(i, accepts_ml)
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
        Payload::Token(_) => Err(Either::Left(item)),
    }
}

fn token_kind(item: &Item) -> Option<TokenKind> {
    match &item.payload {
        Payload::Token(token) => Some(token.kind),
        Payload::Eof => None,
    }
}

fn tail_item(mut i: RewriteIn) -> Item {
    let leading = scan_trivia(i.rb());
    let payload = i
        .map(
            choice((
                token(scan_identifier),
                token(scan_punctuation),
                token(scan_unknown),
            )),
            Payload::Token,
        )
        .unwrap_or(Payload::Eof);
    Item { leading, payload }
}

fn scan_nud_item(mut i: LexIn) -> Option<Item> {
    let leading = scan_trivia_lex(i.rb());
    let token = i.check(choice((token(scan_identifier), token(scan_lparen))))?;
    Some(Item {
        leading,
        payload: Payload::Token(token),
    })
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

fn emit_core(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("a core scanner always returns a token")
    };
    debug_assert_eq!(token.kind, TokenKind::Identifier);
    i.state.start_node(SyntaxKind::IdentifierExpression.into());
    emit_trivia(i, &item.leading);
    i.state.token(SyntaxKind::Identifier.into(), &token.text);
    i.state.finish_node();
}

fn emit_token_item(i: &mut RewriteIn, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("only a lexical item can be accepted")
    };
    emit_trivia(i, &item.leading);
    let kind = match token.kind {
        TokenKind::Identifier => SyntaxKind::Identifier,
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
