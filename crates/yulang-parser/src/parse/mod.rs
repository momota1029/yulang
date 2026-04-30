use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::sink::EventSink;

pub trait DelimitedListMachine<I: EventInput, S: EventSink> {
    fn end_kind(&self) -> SyntaxKind;

    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        base_indent: usize,
    ) -> Option<Either<TriviaInfo, Lex>>;

    fn is_group_sep(&self, kind: SyntaxKind) -> bool;

    fn is_implicit_separator(&self, info: TriviaInfo, base_indent: usize) -> bool {
        matches!(info, TriviaInfo::Newline { indent,.. } if indent <= base_indent)
    }

    fn parse_delimited_list(&mut self, mut i: In<I, S>, open_lex: Lex) -> Option<TriviaInfo> {
        i.env.state.sink.lex(&open_lex);
        i.env.ml_arg = false;
        i.env.inline = false;
        let base_indent = i.env.indent;
        let mut leading_info = open_lex.trailing_trivia_info();

        loop {
            let parsed = self.parse_item(i.rb(), leading_info, base_indent)?;
            match parsed {
                Either::Left(info) => {
                    if self.is_implicit_separator(info, base_indent) {
                        i.env.state.sink.start(SyntaxKind::Separator);
                        i.env.state.sink.finish();
                        leading_info = info;
                    } else {
                        return Some(info);
                    }
                }
                Either::Right(stop) => {
                    let next_info = stop.trailing_trivia_info();
                    match stop.kind {
                        kind if kind == self.end_kind() => {
                            i.env.state.sink.lex(&stop);
                            return Some(next_info);
                        }
                        kind if self.is_group_sep(kind) => {
                            i.env.state.sink.start(SyntaxKind::Separator);
                            i.env.state.sink.lex(&stop);
                            i.env.state.sink.finish();
                            leading_info = next_info;
                        }
                        _ => {
                            i.env.state.sink.start(SyntaxKind::InvalidToken);
                            i.env.state.sink.lex(&stop);
                            i.env.state.sink.finish();
                            leading_info = next_info;
                        }
                    }
                }
            }
        }
    }
}

pub trait IndentListMachine<I: EventInput, S: EventSink> {
    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        block_indent: usize,
    ) -> Option<(TriviaInfo, Option<Lex>)>;

    fn is_item_separator(&self, kind: SyntaxKind) -> bool;

    fn parse_indent_list(
        &mut self,
        mut i: In<I, S>,
        leading_info: TriviaInfo,
        base_indent: usize,
    ) -> Option<TriviaInfo> {
        let TriviaInfo::Newline {
            indent: block_indent,
            ..
        } = leading_info
        else {
            i.env.state.sink.start(SyntaxKind::InvalidToken);
            i.env.state.sink.finish();
            return Some(leading_info);
        };
        if block_indent <= base_indent {
            i.env.state.sink.start(SyntaxKind::InvalidToken);
            i.env.state.sink.finish();
            return Some(leading_info);
        }

        let old_indent = i.env.indent;
        i.env.indent = block_indent;
        let mut info = leading_info;
        loop {
            match info {
                TriviaInfo::None => break,
                TriviaInfo::Newline { indent, .. } if indent < block_indent => break,
                _ => {}
            }

            let (next_info, stop) = self.parse_item(i.rb(), info, block_indent)?;
            info = next_info;
            if let Some(stop) = stop {
                let next = stop.trailing_trivia_info();
                if self.is_item_separator(stop.kind) {
                    i.env.state.sink.start(SyntaxKind::Separator);
                    i.env.state.sink.lex(&stop);
                    i.env.state.sink.finish();
                } else {
                    emit_invalid(i.rb(), stop);
                }
                info = next;
            }
        }
        i.env.indent = old_indent;
        Some(info)
    }
}

pub trait StopListMachine<I: EventInput, S: EventSink> {
    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: &mut TriviaInfo,
        base_indent: usize,
    ) -> Option<Result<(), Either<TriviaInfo, Lex>>>;

    fn should_break(&mut self, info: TriviaInfo, base_indent: usize) -> bool {
        matches!(info, TriviaInfo::None)
            || matches!(info, TriviaInfo::Newline { indent,.. } if indent < base_indent)
    }

    fn parse_stop_list(
        &mut self,
        mut i: In<I, S>,
        leading_info: TriviaInfo,
        base_indent: usize,
    ) -> Option<Either<TriviaInfo, Lex>> {
        let mut leading_info = leading_info;
        loop {
            if self.should_break(leading_info, base_indent) {
                return Some(Either::Left(leading_info));
            }
            let result = self.parse_item(i.rb(), &mut leading_info, base_indent)?;
            match result {
                Ok(()) => {}
                Err(done) => return Some(done),
            }
        }
    }
}

pub fn emit_invalid<I: EventInput, S: EventSink>(i: In<I, S>, lex: Lex) {
    i.env.state.sink.start(SyntaxKind::InvalidToken);
    i.env.state.sink.lex(&lex);
    i.env.state.sink.finish();
}
