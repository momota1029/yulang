//! Source-free direct recursive-descent foundation for the isolated rewrite.

use chasa_recover::In;
use reborrow_generic::Reborrow as _;
use rowan::GreenNodeBuilder;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::{operator::OperatorTable, syntax_kind::SyntaxKind};

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

pub(super) type TailExit = Result<(), Either<Item, End>>;

/// No field of this result borrows the input source.
pub(super) struct ParseResult {
    pub(super) green: rowan::GreenNode,
    pub(super) exit: Option<TailExit>,
}

pub(super) fn parse(source: &str, operators: &OperatorTable) -> ParseResult {
    let mut input = source;
    let mut recover = Recover::new(operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = expr(In::new(&mut input, &mut recover, &mut builder));
    if let Some(Err(Either::Right(end))) = &exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    ParseResult {
        green: builder.finish(),
        exit,
    }
}

/// `None` occurs only before the lexical transaction has accepted a core.
pub(super) fn expr(mut i: RewriteIn<'_, '_, '_, '_, '_>) -> Option<TailExit> {
    let core = i.token(scan_core_item)?;
    i.state.start_node(SyntaxKind::OperatorChain.into());
    emit_core(&mut i, core);
    let next = tail_item(i.rb());
    let exit = tail(i.rb(), next);
    i.state.finish_node();
    Some(exit)
}

/// Non-boundary items are returned unchanged and receive no builder effect.
pub(super) fn tail(_: RewriteIn<'_, '_, '_, '_, '_>, item: Item) -> TailExit {
    match item.payload {
        Payload::Eof => Err(Either::Right(End { item })),
        Payload::Token(_) => Err(Either::Left(item)),
    }
}

fn tail_item(mut i: RewriteIn<'_, '_, '_, '_, '_>) -> Item {
    let leading = scan_trivia(i.rb());
    if let Some(token) = i.token(scan_identifier) {
        return Item {
            leading,
            payload: Payload::Token(token),
        };
    }
    if let Some(token) = i.token(scan_unknown) {
        return Item {
            leading,
            payload: Payload::Token(token),
        };
    }
    Item {
        leading,
        payload: Payload::Eof,
    }
}

fn scan_core_item(mut i: LexIn<'_, '_, '_, '_>) -> Option<Item> {
    let leading = scan_trivia_lex(i.rb());
    let token = scan_identifier(i.rb())?;
    Some(Item {
        leading,
        payload: Payload::Token(token),
    })
}

fn scan_trivia(mut i: RewriteIn<'_, '_, '_, '_, '_>) -> LeadingTrivia {
    let mut parts = Vec::new();
    while let Some(part) = i.token(scan_trivia_part) {
        parts.push(part);
    }
    LeadingTrivia(parts.into_boxed_slice())
}

fn scan_trivia_lex(mut i: LexIn<'_, '_, '_, '_>) -> LeadingTrivia {
    let mut parts = Vec::new();
    while let Some(part) = i.token(scan_trivia_part) {
        parts.push(part);
    }
    LeadingTrivia(parts.into_boxed_slice())
}

fn scan_trivia_part(mut i: LexIn<'_, '_, '_, '_>) -> Option<Trivia> {
    if let Some(part) = i.token(scan_horizontal_whitespace) {
        return Some(part);
    }
    if let Some(part) = i.token(scan_newline) {
        return Some(part);
    }
    if let Some(part) = i.token(scan_line_comment) {
        return Some(part);
    }
    i.token(scan_block_comment)
}

fn scan_horizontal_whitespace(mut i: LexIn<'_, '_, '_, '_>) -> Option<Trivia> {
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

fn scan_horizontal_whitespace_unit(mut i: LexIn<'_, '_, '_, '_>) -> Option<()> {
    matches!(i.next()?, ' ' | '\t').then_some(())
}

fn scan_newline(mut i: LexIn<'_, '_, '_, '_>) -> Option<Trivia> {
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

fn scan_line_feed(mut i: LexIn<'_, '_, '_, '_>) -> Option<()> {
    (i.next()? == '\n').then_some(())
}

fn scan_line_comment(mut i: LexIn<'_, '_, '_, '_>) -> Option<Trivia> {
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

fn scan_line_comment_character(mut i: LexIn<'_, '_, '_, '_>) -> Option<()> {
    (!matches!(i.next()?, '\r' | '\n')).then_some(())
}

fn scan_block_comment(mut i: LexIn<'_, '_, '_, '_>) -> Option<Trivia> {
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

fn scan_block_open(i: LexIn<'_, '_, '_, '_>) -> Option<()> {
    scan_pair(i, '/', '*')
}

fn scan_block_close(i: LexIn<'_, '_, '_, '_>) -> Option<()> {
    scan_pair(i, '*', '/')
}

fn scan_pair(mut i: LexIn<'_, '_, '_, '_>, first: char, second: char) -> Option<()> {
    (i.next()? == first).then_some(())?;
    (i.next()? == second).then_some(())
}

fn scan_identifier(mut i: LexIn<'_, '_, '_, '_>) -> Option<Token> {
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

fn scan_identifier_continue(mut i: LexIn<'_, '_, '_, '_>) -> Option<()> {
    is_xid_continue(i.next()?).then_some(())
}

fn scan_identifier_suffix(mut i: LexIn<'_, '_, '_, '_>) -> Option<()> {
    matches!(i.next()?, '?' | '!').then_some(())
}

fn scan_unknown(i: LexIn<'_, '_, '_, '_>) -> Option<Token> {
    let (character, text) = i.with_str(|mut one| one.next());
    character?;
    Some(Token {
        kind: TokenKind::Unknown,
        text: text.into(),
    })
}

fn emit_core(i: &mut RewriteIn<'_, '_, '_, '_, '_>, item: Item) {
    let Payload::Token(token) = item.payload else {
        unreachable!("a core scanner always returns a token")
    };
    debug_assert_eq!(token.kind, TokenKind::Identifier);
    i.state.start_node(SyntaxKind::IdentifierExpression.into());
    emit_trivia(i, &item.leading);
    i.state.token(SyntaxKind::Identifier.into(), &token.text);
    i.state.finish_node();
}

fn emit_end(builder: &mut GreenNodeBuilder<'static>, end: &End) {
    emit_trivia_builder(builder, &end.item.leading);
}

fn emit_trivia(i: &mut RewriteIn<'_, '_, '_, '_, '_>, trivia: &LeadingTrivia) {
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
