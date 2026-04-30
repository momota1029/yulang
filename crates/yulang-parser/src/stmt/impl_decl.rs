use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::emit_invalid;
use crate::sink::EventSink;

use super::block::{parse_brace_stmt_block, parse_decl_body_after_colon};
use super::common::scan_stmt_lex;
use super::role_decl::{
    parse_role_body_from_info, parse_role_body_from_stop, parse_type_with_stops,
};

pub(super) fn parse_impl_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::ImplDecl);
    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }
    i.env.state.sink.lex(&decl_kw);

    let out = parse_impl_after_impl_kw(i.rb(), decl_kw.trailing_trivia_info())?;
    i.env.state.sink.finish();
    Some(out)
}

pub(super) fn parse_impl_after_impl_kw<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    mut leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    loop {
        let stop = match parse_type_with_stops(
            i.rb(),
            leading_info,
            &[
                SyntaxKind::Comma,
                SyntaxKind::Via,
                SyntaxKind::Colon,
                SyntaxKind::BraceL,
                SyntaxKind::Semicolon,
            ],
        )? {
            Either::Right(stop) => stop,
            Either::Left(info) => {
                return parse_role_body_from_info(i.rb(), info);
            }
        };

        match stop.kind {
            SyntaxKind::Comma => {
                i.env.state.sink.start(SyntaxKind::Separator);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
                leading_info = stop.trailing_trivia_info();
            }
            SyntaxKind::Via => {
                i.env.state.sink.lex(&stop);
                return parse_via_after_kw(i.rb(), stop.trailing_trivia_info());
            }
            _ => {
                return parse_role_body_from_stop(i.rb(), Some(stop));
            }
        }
    }
}

fn parse_via_after_kw<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let result = parse_type_with_stops(
        i.rb(),
        leading_info,
        &[SyntaxKind::Semicolon, SyntaxKind::Colon, SyntaxKind::BraceL],
    )?;
    match result {
        Either::Right(stop) => match stop.kind {
            SyntaxKind::Semicolon => {
                i.env.state.sink.lex(&stop);
                Some(Either::Left(stop.trailing_trivia_info()))
            }
            SyntaxKind::Colon => {
                let base_indent = i.env.indent;
                i.env.state.sink.lex(&stop);
                parse_decl_body_after_colon(i.rb(), stop.trailing_trivia_info(), base_indent)
            }
            SyntaxKind::BraceL => {
                let next = parse_brace_stmt_block(i.rb(), stop)?;
                Some(Either::Left(next))
            }
            _ => {
                let next = stop.trailing_trivia_info();
                emit_invalid(i.rb(), stop);
                Some(Either::Left(next))
            }
        },
        Either::Left(info) => parse_via_terminator(i, info),
    }
}

fn parse_via_terminator<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    if matches!(leading_info, TriviaInfo::Newline { .. } | TriviaInfo::None) {
        return Some(Either::Left(leading_info));
    }
    let Some(tok) = scan_stmt_lex(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };
    match tok.kind {
        SyntaxKind::Semicolon => {
            i.env.state.sink.lex(&tok);
            Some(Either::Left(tok.trailing_trivia_info()))
        }
        _ => {
            let next = tok.trailing_trivia_info();
            emit_invalid(i.rb(), tok);
            Some(Either::Left(next))
        }
    }
}
