use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::DelimitedListMachine;
use crate::sink::EventSink;

use super::parse_expr;
use super::scan::scan_expr_spread_dotdot;

pub(super) fn delimited<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    node_kind: SyntaxKind,
    end_kind: SyntaxKind,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(node_kind);
    let result = parse_group_body(
        i.rb(),
        end_kind,
        open_lex,
        node_kind == SyntaxKind::BraceGroup,
    )?;
    i.env.state.sink.finish();
    Some(result)
}

pub(super) fn parse_call_group<I: EventInput, S: EventSink>(
    i: In<I, S>,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    parse_group_body(i, SyntaxKind::ParenR, open_lex, false)
}

pub(super) fn parse_list_group<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::Bracket);
    let mut machine = ListExprMachine::new(SyntaxKind::BracketR);
    let result = machine.parse_delimited_list(i.rb(), open_lex)?;
    i.env.state.sink.finish();
    Some(result)
}

fn parse_group_body<I: EventInput, S: EventSink>(
    i: In<I, S>,
    end_kind: SyntaxKind,
    open_lex: Lex,
    allow_spread: bool,
) -> Option<TriviaInfo> {
    let mut machine = ExprListMachine::new(end_kind, allow_spread);
    machine.parse_delimited_list(i, open_lex)
}

struct ExprListMachine {
    end_kind: SyntaxKind,
    allow_spread: bool,
}

impl ExprListMachine {
    fn new(end_kind: SyntaxKind, allow_spread: bool) -> Self {
        Self {
            end_kind,
            allow_spread,
        }
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for ExprListMachine {
    fn end_kind(&self) -> SyntaxKind {
        self.end_kind
    }

    fn is_group_sep(&self, kind: SyntaxKind) -> bool {
        matches!(kind, SyntaxKind::Comma | SyntaxKind::Semicolon)
    }

    fn parse_item(
        &mut self,
        mut i: In<I, S>,
        leading_info: TriviaInfo,
        base_indent: usize,
    ) -> Option<Either<TriviaInfo, Lex>> {
        if self.allow_spread {
            if let Some(dotdot) = i.maybe_fn(|i| scan_expr_spread_dotdot(leading_info, i))? {
                i.env.state.sink.start(SyntaxKind::ExprSpread);
                i.env.state.sink.lex(&dotdot);
                let old_indent = i.env.indent;
                let old_stop = i.env.stop.clone();
                i.env.indent = base_indent;
                i.env.suspend_outer_block_stops_in_group();
                i.env.stop.insert(self.end_kind);
                i.env.stop.insert(SyntaxKind::Comma);
                i.env.stop.insert(SyntaxKind::Semicolon);
                let parsed = parse_expr(dotdot.trailing_trivia_info(), i.rb());
                i.env.stop = old_stop;
                i.env.indent = old_indent;
                i.env.state.sink.finish();
                return Some(parsed?);
            }
        }

        let old_indent = i.env.indent;
        let old_stop = i.env.stop.clone();
        i.env.indent = base_indent;
        i.env.suspend_outer_block_stops_in_group();
        i.env.stop.insert(self.end_kind);
        i.env.stop.insert(SyntaxKind::Comma);
        i.env.stop.insert(SyntaxKind::Semicolon);
        let parsed = parse_expr(leading_info, i.rb());
        i.env.stop = old_stop;
        i.env.indent = old_indent;
        parsed
    }
}

struct ListExprMachine {
    end_kind: SyntaxKind,
}

impl ListExprMachine {
    fn new(end_kind: SyntaxKind) -> Self {
        Self { end_kind }
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for ListExprMachine {
    fn end_kind(&self) -> SyntaxKind {
        self.end_kind
    }

    fn is_group_sep(&self, kind: SyntaxKind) -> bool {
        matches!(kind, SyntaxKind::Comma)
    }

    fn parse_item(
        &mut self,
        mut i: In<I, S>,
        leading_info: TriviaInfo,
        base_indent: usize,
    ) -> Option<Either<TriviaInfo, Lex>> {
        if let Some(dotdot) = i.maybe_fn(|i| scan_expr_spread_dotdot(leading_info, i))? {
            i.env.state.sink.start(SyntaxKind::ExprSpread);
            i.env.state.sink.lex(&dotdot);
            let old_indent = i.env.indent;
            let old_stop = i.env.stop.clone();
            i.env.indent = base_indent;
            i.env.suspend_outer_block_stops_in_group();
            i.env.stop.insert(self.end_kind);
            i.env.stop.insert(SyntaxKind::Comma);
            let parsed = parse_expr(dotdot.trailing_trivia_info(), i.rb());
            i.env.stop = old_stop;
            i.env.indent = old_indent;
            i.env.state.sink.finish();
            return Some(parsed?);
        }

        let old_indent = i.env.indent;
        let old_stop = i.env.stop.clone();
        i.env.indent = base_indent;
        i.env.suspend_outer_block_stops_in_group();
        i.env.stop.insert(self.end_kind);
        i.env.stop.insert(SyntaxKind::Comma);
        let parsed = parse_expr(leading_info, i.rb());
        i.env.stop = old_stop;
        i.env.indent = old_indent;
        parsed
    }
}
