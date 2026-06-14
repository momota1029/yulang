use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::parse_expr_bp;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::emit_invalid;
use crate::pat::parse::parse_pattern_from_nud;
use crate::pat::scan::{PatNudTag, scan_pat_nud};
use crate::sink::EventSink;

use super::block::{parse_brace_stmt_block, parse_indent_stmt_block};
use super::common::{emit_missing_invalid, peek_stmt_lex, scan_stmt_lex};

pub(super) fn parse_for_stmt<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    for_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::ForStmt);
    i.env.state.sink.start(SyntaxKind::ForHeader);
    i.env.state.sink.lex(&for_kw);

    let pattern_leading = parse_for_label(i.rb(), for_kw.trailing_trivia_info())?;
    let in_kw = match parse_for_pattern(i.rb(), pattern_leading)? {
        Either::Right(stop) => stop,
        Either::Left(info) => {
            i.env.state.sink.finish();
            i.env.state.sink.finish();
            return Some(Either::Left(info));
        }
    };
    if in_kw.kind != SyntaxKind::In {
        emit_invalid(i.rb(), in_kw.clone());
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Right(in_kw));
    }
    i.env.state.sink.lex(&in_kw);

    let stop = match parse_for_iter_expr(i.rb(), in_kw.trailing_trivia_info())? {
        Either::Right(stop) => stop,
        Either::Left(info) => {
            emit_missing_invalid(i.rb());
            i.env.state.sink.finish();
            i.env.state.sink.finish();
            return Some(Either::Left(info));
        }
    };
    let result = match stop.kind {
        SyntaxKind::Colon => {
            i.env.state.sink.lex(&stop);
            i.env.state.sink.finish();
            i.env.state.sink.start(SyntaxKind::ForBody);
            i.env.state.line_indent = i.env.indent;
            let result = parse_for_colon_body(i.rb(), stop.trailing_trivia_info())?;
            i.env.state.sink.finish();
            result
        }
        SyntaxKind::BraceL => {
            i.env.state.sink.finish();
            i.env.state.sink.start(SyntaxKind::ForBody);
            let next = parse_brace_stmt_block(i.rb(), stop)?;
            i.env.state.sink.finish();
            Either::Left(next)
        }
        _ => {
            emit_invalid(i.rb(), stop.clone());
            i.env.state.sink.finish();
            Either::Right(stop)
        }
    };

    i.env.state.sink.finish();
    Some(result)
}

fn parse_for_label<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<TriviaInfo> {
    let label = peek_stmt_lex(leading_info, i.rb())?;
    if label.kind != SyntaxKind::SigilIdent || !label.text.starts_with('\'') {
        return Some(leading_info);
    }
    let next_info = label.trailing_trivia_info();
    let Some(next) = peek_stmt_lex(next_info, i.rb()) else {
        return Some(leading_info);
    };
    if next.kind == SyntaxKind::In {
        return Some(leading_info);
    }

    let label = scan_stmt_lex(leading_info, i.rb())?;
    i.env.state.sink.start(SyntaxKind::ForLabel);
    i.env.state.sink.lex(&label);
    i.env.state.sink.finish();
    Some(label.trailing_trivia_info())
}

fn parse_for_pattern<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let old_stop = i.env.stop.clone();
    i.env.stop.insert(SyntaxKind::In);
    let nud = match scan_pat_nud(leading_info, i.rb()) {
        Some(nud) => nud,
        None => {
            i.env.stop = old_stop;
            return None;
        }
    };
    let stop = match nud.tag {
        PatNudTag::Stop => nud.lex,
        _ => match parse_pattern_from_nud(i.rb(), nud)? {
            Either::Right(stop) => stop,
            Either::Left(info) => {
                i.env.stop = old_stop;
                return Some(Either::Left(info));
            }
        },
    };
    i.env.stop = old_stop;
    Some(Either::Right(stop))
}

fn parse_for_iter_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let old_stop = i.env.stop.clone();
    i.env.stop.insert(SyntaxKind::Colon);
    i.env.stop.insert(SyntaxKind::BraceL);
    let parsed = match parse_expr_bp(None, leading_info, i.rb()) {
        Some(parsed) => parsed,
        None => {
            i.env.stop = old_stop;
            return None;
        }
    };
    i.env.stop = old_stop;
    match parsed {
        Ok(result) => Some(result),
        Err(next_led) => Some(Either::Right(next_led.lex)),
    }
}

fn parse_for_colon_body<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let for_line_indent = i.env.indent;
    i.env.state.line_indent = for_line_indent;

    match leading_info {
        TriviaInfo::Newline { indent, .. } if indent > for_line_indent => {
            let next = parse_indent_stmt_block(i.rb(), indent, leading_info)?;
            Some(Either::Left(next))
        }
        TriviaInfo::Newline { .. } => {
            emit_missing_invalid(i.rb());
            Some(Either::Left(leading_info))
        }
        _ => match crate::expr::parse_expr(leading_info, i.rb()) {
            Some(parsed) => Some(parsed),
            None => {
                emit_missing_invalid(i.rb());
                Some(Either::Left(leading_info))
            }
        },
    }
}
