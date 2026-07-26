use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::sink::EventSink;

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
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let stop = match parse_type_with_stops(
        i.rb(),
        leading_info,
        &[
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
        SyntaxKind::Via => reject_unimplemented_impl_via(i.rb(), stop),
        SyntaxKind::Colon if !matches!(stop.trailing_trivia_info(), TriviaInfo::Newline { .. }) => {
            parse_impl_description_after_colon(i.rb(), stop)
        }
        _ => parse_role_body_from_stop(i.rb(), Some(stop)),
    }
}

fn parse_impl_description_after_colon<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    colon: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::ImplDescription);
    i.env.state.sink.lex(&colon);
    let parsed = parse_type_with_stops(
        i.rb(),
        colon.trailing_trivia_info(),
        &[SyntaxKind::Semicolon, SyntaxKind::Colon, SyntaxKind::BraceL],
    )?;
    i.env.state.sink.finish();
    match parsed {
        Either::Right(stop) => parse_role_body_from_stop(i.rb(), Some(stop)),
        Either::Left(info) => parse_role_body_from_info(i.rb(), info),
    }
}

/// `impl Target via Source` has no lowering semantics. Keep its complete
/// source range in an invalid CST node so downstream syntax diagnostics can
/// report: "impl ... via ... is not implemented; use via only in a derives
/// clause".
fn reject_unimplemented_impl_via<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    via_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::InvalidToken);
    i.env.state.sink.lex(&via_kw);
    let result = parse_type_with_stops(
        i.rb(),
        via_kw.trailing_trivia_info(),
        &[SyntaxKind::Semicolon, SyntaxKind::Colon, SyntaxKind::BraceL],
    )?;
    i.env.state.sink.finish();
    match result {
        Either::Right(stop) => parse_role_body_from_stop(i, Some(stop)),
        Either::Left(info) => parse_role_body_from_info(i, info),
    }
}
