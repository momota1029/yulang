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
            let next_info = parse_where_constraint_indent_block(
                i.rb(),
                colon.trailing_trivia_info(),
                base_indent,
            )?;
            i.env.state.sink.finish();
            return Some(Either::Left(next_info));
        }
    }

    let (next_info, stop) = parse_where_constraint_line(i.rb(), leading_info, true)?;
    i.env.state.sink.finish();
    match stop {
        Some(stop) => Some(Either::Right(stop)),
        None => Some(Either::Left(next_info)),
    }
}

fn parse_where_constraint_indent_block<I: EventInput, S: EventSink>(
    i: In<I, S>,
    leading_info: TriviaInfo,
    base_indent: usize,
) -> Option<TriviaInfo> {
    let mut machine = WhereConstraintIndentMachine;
    machine.parse_indent_list(i, leading_info, base_indent)
}

struct WhereConstraintIndentMachine;

impl<I: EventInput, S: EventSink> IndentListMachine<I, S> for WhereConstraintIndentMachine {
    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        _block_indent: usize,
    ) -> Option<(TriviaInfo, Option<Lex>)> {
        parse_where_constraint_line(i, leading_info, false)
    }

    fn is_item_separator(&self, kind: SyntaxKind) -> bool {
        matches!(kind, SyntaxKind::Semicolon)
    }
}

fn parse_where_constraint_line<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
    allow_outer_stops: bool,
) -> Option<(TriviaInfo, Option<Lex>)> {
    i.env.state.sink.start(SyntaxKind::WhereConstraint);

    let lhs = parse_type_with_stops(i.rb(), leading_info, &[SyntaxKind::Colon]);
    let mut info = match lhs {
        Some(Either::Right(stop)) if stop.kind == SyntaxKind::Colon => {
            i.env.state.sink.lex(&stop);
            stop.trailing_trivia_info()
        }
        Some(Either::Right(stop)) => {
            let next = stop.trailing_trivia_info();
            emit_invalid(i.rb(), stop);
            i.env.state.sink.finish();
            return Some((next, None));
        }
        Some(Either::Left(next)) => {
            emit_missing_invalid(i.rb());
            i.env.state.sink.finish();
            return Some((next, None));
        }
        None => {
            emit_missing_invalid(i.rb());
            i.env.state.sink.finish();
            return Some((leading_info, None));
        }
    };

    loop {
        let mut stops = vec![SyntaxKind::Comma, SyntaxKind::Semicolon];
        if allow_outer_stops {
            stops.push(SyntaxKind::BraceR);
            stops.push(SyntaxKind::ParenR);
            stops.push(SyntaxKind::BracketR);
        }
        let rhs = parse_type_with_stops(i.rb(), info, &stops);
        match rhs {
            Some(Either::Left(next)) => {
                i.env.state.sink.finish();
                return Some((next, None));
            }
            Some(Either::Right(stop)) => match stop.kind {
                SyntaxKind::Comma => {
                    i.env.state.sink.start(SyntaxKind::Separator);
                    i.env.state.sink.lex(&stop);
                    i.env.state.sink.finish();
                    info = stop.trailing_trivia_info();
                }
                SyntaxKind::Semicolon => {
                    let next = stop.trailing_trivia_info();
                    i.env.state.sink.finish();
                    return Some((next, Some(stop)));
                }
                SyntaxKind::BraceR | SyntaxKind::ParenR | SyntaxKind::BracketR
                    if allow_outer_stops =>
                {
                    let next = stop.trailing_trivia_info();
                    i.env.state.sink.finish();
                    return Some((next, Some(stop)));
                }
                _ => {
                    let next = stop.trailing_trivia_info();
                    emit_invalid(i.rb(), stop);
                    i.env.state.sink.finish();
                    return Some((next, None));
                }
            },
            None => {
                emit_missing_invalid(i.rb());
                i.env.state.sink.finish();
                return Some((info, None));
            }
        }
    }
}
