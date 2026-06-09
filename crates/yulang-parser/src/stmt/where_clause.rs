use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::{IndentListMachine, emit_invalid};
use crate::sink::EventSink;

use super::common::{emit_missing_invalid, peek_stmt_lex, scan_stmt_lex};
use super::role_decl::parse_type_with_stops;

pub(super) fn parse_where_clause<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    where_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::WhereClause);
    i.env.state.sink.lex(&where_kw);

    let leading_info = where_kw.trailing_trivia_info();
    if let Some(next) = peek_stmt_lex(leading_info, i.rb()) {
        if next.kind == SyntaxKind::Colon {
            let colon = scan_stmt_lex(leading_info, i.rb())?;
            i.env.state.sink.lex(&colon);
            let base_indent = i.env.indent;
            let next_info = parse_where_predicate_indent_block(
                i.rb(),
                colon.trailing_trivia_info(),
                base_indent,
            )?;
            i.env.state.sink.finish();
            return Some(Either::Left(next_info));
        }
    }

    let (next_info, stop) = parse_where_predicate_line(i.rb(), leading_info, true)?;
    i.env.state.sink.finish();
    match stop {
        Some(stop) => Some(Either::Right(stop)),
        None => Some(Either::Left(next_info)),
    }
}

fn parse_where_predicate_indent_block<I: EventInput, S: EventSink>(
    i: In<I, S>,
    leading_info: TriviaInfo,
    base_indent: usize,
) -> Option<TriviaInfo> {
    let mut machine = WherePredicateIndentMachine;
    machine.parse_indent_list(i, leading_info, base_indent)
}

struct WherePredicateIndentMachine;

impl<I: EventInput, S: EventSink> IndentListMachine<I, S> for WherePredicateIndentMachine {
    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        _block_indent: usize,
    ) -> Option<(TriviaInfo, Option<Lex>)> {
        parse_where_predicate_line(i, leading_info, false)
    }

    fn is_item_separator(&self, kind: SyntaxKind) -> bool {
        matches!(kind, SyntaxKind::Semicolon)
    }
}

fn parse_where_predicate_line<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
    allow_outer_stops: bool,
) -> Option<(TriviaInfo, Option<Lex>)> {
    let mut info = leading_info;
    loop {
        let (next_info, stop) = parse_where_predicate(i.rb(), info, allow_outer_stops)?;
        let Some(stop) = stop else {
            return Some((next_info, None));
        };

        match stop.kind {
            SyntaxKind::Comma => {
                i.env.state.sink.start(SyntaxKind::Separator);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
                info = stop.trailing_trivia_info();
            }
            SyntaxKind::Semicolon => {
                return Some((stop.trailing_trivia_info(), Some(stop)));
            }
            SyntaxKind::BraceR | SyntaxKind::ParenR | SyntaxKind::BracketR if allow_outer_stops => {
                return Some((stop.trailing_trivia_info(), Some(stop)));
            }
            _ => {
                let next = stop.trailing_trivia_info();
                emit_invalid(i.rb(), stop);
                return Some((next, None));
            }
        }
    }
}

fn parse_where_predicate<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
    allow_outer_stops: bool,
) -> Option<(TriviaInfo, Option<Lex>)> {
    i.env.state.sink.start(SyntaxKind::WherePredicate);

    let mut stops = predicate_stops(allow_outer_stops);
    stops.push(SyntaxKind::Colon);
    let lhs = parse_type_with_stops(i.rb(), leading_info, &stops);
    let info = match lhs {
        Some(Either::Left(next)) => {
            i.env.state.sink.finish();
            return Some((next, None));
        }
        Some(Either::Right(stop)) if stop.kind == SyntaxKind::Colon => {
            i.env.state.sink.lex(&stop);
            stop.trailing_trivia_info()
        }
        Some(Either::Right(stop)) if predicate_stop(stop.kind, allow_outer_stops) => {
            i.env.state.sink.finish();
            return Some((stop.trailing_trivia_info(), Some(stop)));
        }
        Some(Either::Right(stop)) => {
            let next = stop.trailing_trivia_info();
            emit_invalid(i.rb(), stop);
            i.env.state.sink.finish();
            return Some((next, None));
        }
        None => {
            emit_missing_invalid(i.rb());
            i.env.state.sink.finish();
            return Some((leading_info, None));
        }
    };

    let rhs = parse_type_with_stops(i.rb(), info, &predicate_stops(allow_outer_stops));
    match rhs {
        Some(Either::Left(next)) => {
            i.env.state.sink.finish();
            Some((next, None))
        }
        Some(Either::Right(stop)) if predicate_stop(stop.kind, allow_outer_stops) => {
            i.env.state.sink.finish();
            Some((stop.trailing_trivia_info(), Some(stop)))
        }
        Some(Either::Right(stop)) => {
            let next = stop.trailing_trivia_info();
            emit_invalid(i.rb(), stop);
            i.env.state.sink.finish();
            Some((next, None))
        }
        None => {
            emit_missing_invalid(i.rb());
            i.env.state.sink.finish();
            Some((info, None))
        }
    }
}

fn predicate_stops(allow_outer_stops: bool) -> Vec<SyntaxKind> {
    let mut stops = vec![SyntaxKind::Comma, SyntaxKind::Semicolon];
    if allow_outer_stops {
        stops.push(SyntaxKind::BraceR);
        stops.push(SyntaxKind::ParenR);
        stops.push(SyntaxKind::BracketR);
    }
    stops
}

fn predicate_stop(kind: SyntaxKind, allow_outer_stops: bool) -> bool {
    matches!(kind, SyntaxKind::Comma | SyntaxKind::Semicolon)
        || allow_outer_stops
            && matches!(
                kind,
                SyntaxKind::BraceR | SyntaxKind::ParenR | SyntaxKind::BracketR
            )
}
