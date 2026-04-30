use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::emit_invalid;
use crate::sink::EventSink;
use crate::typ::parse::parse_type;

use super::block::{parse_brace_stmt_block, parse_decl_body_after_colon};
use super::common::scan_stmt_lex;

pub(super) fn parse_role_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::RoleDecl);
    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }
    i.env.state.sink.lex(&decl_kw);

    let result = match parse_type_with_stops(
        i.rb(),
        decl_kw.trailing_trivia_info(),
        &[
            SyntaxKind::Colon,
            SyntaxKind::BraceL,
            SyntaxKind::Semicolon,
            SyntaxKind::Comma,
            SyntaxKind::Via,
        ],
    )? {
        Either::Right(stop) => parse_role_body_from_stop(i.rb(), Some(stop)),
        Either::Left(info) => parse_role_body_from_info(i.rb(), info),
    }?;

    i.env.state.sink.finish();
    Some(result)
}

pub(super) fn parse_role_body_from_info<I: EventInput, S: EventSink>(
    i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    parse_role_like_body(i, leading_info)
}

pub(super) fn parse_role_body_from_stop<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: Option<Lex>,
) -> Option<Either<TriviaInfo, Lex>> {
    if let Some(stop) = stop {
        match stop.kind {
            SyntaxKind::Colon => {
                let base_indent = i.env.indent;
                i.env.state.sink.lex(&stop);
                return parse_decl_body_after_colon(
                    i.rb(),
                    stop.trailing_trivia_info(),
                    base_indent,
                );
            }
            SyntaxKind::BraceL => {
                let next = parse_brace_stmt_block(i.rb(), stop)?;
                return Some(Either::Left(next));
            }
            SyntaxKind::Semicolon => {
                i.env.state.sink.lex(&stop);
                return Some(Either::Left(stop.trailing_trivia_info()));
            }
            _ => {
                let next = stop.trailing_trivia_info();
                emit_invalid(i.rb(), stop);
                return Some(Either::Left(next));
            }
        }
    }
    parse_role_like_body(i, TriviaInfo::None)
}

pub(super) fn parse_role_like_body<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if i.env.inline
        && matches!(leading_info, TriviaInfo::Newline { indent, .. } if indent <= i.env.indent)
    {
        return Some(Either::Left(leading_info));
    }
    if i.env.inline && matches!(leading_info, TriviaInfo::None) {
        return Some(Either::Left(leading_info));
    }
    let Some(punct) = scan_stmt_lex(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };
    match punct.kind {
        SyntaxKind::Semicolon => {
            i.env.state.sink.lex(&punct);
            Some(Either::Left(punct.trailing_trivia_info()))
        }
        SyntaxKind::BraceL => {
            let next = parse_brace_stmt_block(i.rb(), punct)?;
            Some(Either::Left(next))
        }
        SyntaxKind::Colon => {
            let base_indent = i.env.indent;
            i.env.state.sink.lex(&punct);
            parse_decl_body_after_colon(i.rb(), punct.trailing_trivia_info(), base_indent)
        }
        _ => {
            let next = punct.trailing_trivia_info();
            emit_invalid(i.rb(), punct);
            Some(Either::Left(next))
        }
    }
}

pub(super) fn parse_type_with_stops<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
    stops: &[SyntaxKind],
) -> Option<Either<TriviaInfo, Lex>> {
    let old_stop = i.env.stop.clone();
    for kind in stops {
        i.env.stop.insert(*kind);
    }
    let parsed = parse_type(leading_info, i.rb());
    i.env.stop = old_stop;
    parsed
}
