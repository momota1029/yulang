use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::parse_expr;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::emit_invalid;
use crate::pat::parse::parse_pattern_from_nud;
use crate::pat::scan::scan_pat_nud;
use crate::sink::EventSink;

use super::block::parse_indent_stmt_block;
use super::common::{emit_missing_invalid, scan_stmt_lex};
use super::role_decl::parse_type_with_stops;

pub(super) fn parse_cast_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::CastDecl);
    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }
    i.env.state.sink.lex(&decl_kw);

    let out = parse_cast_after_kw(i.rb(), decl_kw.trailing_trivia_info())?;
    i.env.state.sink.finish();
    Some(out)
}

fn parse_cast_after_kw<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let Some(open) = scan_stmt_lex(leading_info, i.rb()) else {
        emit_missing_invalid(i.rb());
        return Some(Either::Left(leading_info));
    };
    if open.kind != SyntaxKind::ParenL {
        let next = open.trailing_trivia_info();
        emit_invalid(i.rb(), open);
        return Some(Either::Left(next));
    }
    i.env.state.sink.lex(&open);

    let mut j = i.rb();
    j.env.stop.insert(SyntaxKind::ParenR);
    let nud = scan_pat_nud(open.trailing_trivia_info(), j)?;
    let stop = match parse_pattern_from_nud(i.rb(), nud)? {
        Either::Right(stop) => stop,
        Either::Left(info) => {
            emit_missing_invalid(i.rb());
            return Some(Either::Left(info));
        }
    };
    if stop.kind != SyntaxKind::ParenR {
        let next = stop.trailing_trivia_info();
        emit_invalid(i.rb(), stop);
        return Some(Either::Left(next));
    }
    i.env.state.sink.lex(&stop);

    let Some(result_colon) = scan_stmt_lex(stop.trailing_trivia_info(), i.rb()) else {
        emit_missing_invalid(i.rb());
        return Some(Either::Left(stop.trailing_trivia_info()));
    };
    if result_colon.kind != SyntaxKind::Colon {
        let next = result_colon.trailing_trivia_info();
        emit_invalid(i.rb(), result_colon);
        return Some(Either::Left(next));
    }
    i.env.state.sink.start(SyntaxKind::TypeAnn);
    i.env.state.sink.lex(&result_colon);
    let target_stop = match parse_type_with_stops(
        i.rb(),
        result_colon.trailing_trivia_info(),
        &[SyntaxKind::Equal, SyntaxKind::Semicolon],
    )? {
        Either::Right(stop) => stop,
        Either::Left(info) => {
            emit_missing_invalid(i.rb());
            i.env.state.sink.finish();
            return Some(Either::Left(info));
        }
    };
    i.env.state.sink.finish(); // TypeAnn

    match target_stop.kind {
        SyntaxKind::Equal => parse_cast_body(i.rb(), target_stop),
        SyntaxKind::Semicolon => {
            i.env.state.sink.lex(&target_stop);
            Some(Either::Left(target_stop.trailing_trivia_info()))
        }
        _ => {
            let next = target_stop.trailing_trivia_info();
            emit_invalid(i.rb(), target_stop);
            Some(Either::Left(next))
        }
    }
}

fn parse_cast_body<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    equal: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.lex(&equal);
    i.env.state.sink.start(SyntaxKind::BindingBody);
    let out = match equal.trailing_trivia_info() {
        TriviaInfo::Newline { indent, .. } if indent > i.env.indent => {
            let next = parse_indent_stmt_block(i.rb(), indent, equal.trailing_trivia_info())?;
            Either::Left(next)
        }
        TriviaInfo::Newline { .. } => {
            emit_missing_invalid(i.rb());
            Either::Left(equal.trailing_trivia_info())
        }
        info => parse_expr(info, i.rb())?,
    };
    i.env.state.sink.finish();
    Some(out)
}
