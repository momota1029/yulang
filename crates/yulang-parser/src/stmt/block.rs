use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::{StopListMachine, emit_invalid};
use crate::sink::EventSink;

use super::common::{emit_missing_invalid, peek_stmt_lex, scan_stmt_lex};

struct BraceStmtBlockMachine;

impl<I: EventInput, S: EventSink> StopListMachine<I, S> for BraceStmtBlockMachine {
    fn parse_item(
        &mut self,
        mut i: In<I, S>,
        leading_info: &mut TriviaInfo,
        _base_indent: usize,
    ) -> Option<Result<(), Either<TriviaInfo, Lex>>> {
        if let Some(next) = peek_stmt_lex(*leading_info, i.rb()) {
            if next.kind == SyntaxKind::BraceR {
                let close = scan_stmt_lex(*leading_info, i.rb())?;
                return Some(Err(Either::Right(close)));
            }
        } else {
            emit_missing_invalid(i.rb());
            return Some(Err(Either::Left(*leading_info)));
        }

        match super::parse_statement(*leading_info, i.rb())? {
            Either::Left(info) => {
                if matches!(info, TriviaInfo::Newline { .. }) {
                    i.env.state.sink.start(SyntaxKind::Separator);
                    i.env.state.sink.finish();
                }
                *leading_info = info;
                Some(Ok(()))
            }
            Either::Right(stop) if stop.kind == SyntaxKind::Semicolon => {
                i.env.state.sink.start(SyntaxKind::Separator);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
                *leading_info = stop.trailing_trivia_info();
                Some(Ok(()))
            }
            Either::Right(stop) if stop.kind == SyntaxKind::BraceR => {
                Some(Err(Either::Right(stop)))
            }
            Either::Right(stop) => {
                let next = stop.trailing_trivia_info();
                emit_invalid(i.rb(), stop);
                *leading_info = next;
                Some(Ok(()))
            }
        }
    }

    fn should_break(&mut self, _info: TriviaInfo, _base_indent: usize) -> bool {
        false
    }
}

pub(super) fn parse_decl_body_after_colon<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
    base_indent: usize,
) -> Option<Either<TriviaInfo, Lex>> {
    match leading_info {
        TriviaInfo::Newline { indent, .. } if indent > base_indent => {
            let next = parse_indent_stmt_block(i.rb(), indent, leading_info)?;
            Some(Either::Left(next))
        }
        TriviaInfo::Newline { .. } => {
            emit_missing_invalid(i.rb());
            Some(Either::Left(leading_info))
        }
        _ => match super::parse_statement(leading_info, i.rb())? {
            Either::Right(stop) if stop.kind == SyntaxKind::Semicolon => {
                i.env.state.sink.lex(&stop);
                Some(Either::Left(stop.trailing_trivia_info()))
            }
            other => Some(other),
        },
    }
}

pub(crate) fn parse_brace_stmt_block<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open_brace: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::BraceGroup);
    i.env.state.sink.lex(&open_brace);

    let mut machine = BraceStmtBlockMachine;
    let base_indent = i.env.indent;
    let out = machine.parse_stop_list(i.rb(), open_brace.trailing_trivia_info(), base_indent)?;
    match out {
        Either::Right(close) => {
            if close.kind == SyntaxKind::BraceR {
                i.env.state.sink.lex(&close);
                i.env.state.sink.finish();
                Some(close.trailing_trivia_info())
            } else {
                let next = close.trailing_trivia_info();
                emit_invalid(i.rb(), close);
                i.env.state.sink.finish();
                Some(next)
            }
        }
        Either::Left(info) => {
            i.env.state.sink.finish();
            Some(info)
        }
    }
}

pub(crate) fn parse_indent_stmt_block<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    block_indent: usize,
    mut leading_info: TriviaInfo,
) -> Option<TriviaInfo> {
    let old_indent = i.env.indent;
    let old_inline = i.env.inline;
    i.env.indent = block_indent;
    i.env.inline = false;
    i.env.state.sink.start(SyntaxKind::IndentBlock);

    loop {
        match leading_info {
            TriviaInfo::None => break,
            TriviaInfo::Newline { indent, .. } if indent < block_indent => break,
            _ => {}
        }

        match super::parse_statement(leading_info, i.rb())? {
            Either::Left(next) => leading_info = next,
            Either::Right(stop) if stop.kind == SyntaxKind::Semicolon => {
                i.env.state.sink.start(SyntaxKind::Separator);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
                leading_info = stop.trailing_trivia_info();
            }
            Either::Right(stop) => {
                emit_invalid(i.rb(), stop.clone());
                leading_info = stop.trailing_trivia_info();
            }
        }
    }

    i.env.state.sink.finish();
    i.env.indent = old_indent;
    i.env.inline = old_inline;
    Some(leading_info)
}
