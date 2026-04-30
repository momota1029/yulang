use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::{DelimitedListMachine, IndentListMachine, emit_invalid};
use crate::sink::EventSink;

use super::common::{peek_stmt_lex, scan_stmt_lex};
use super::role_decl::parse_type_with_stops;
use super::type_decl::{finish_with_or_stmt_stop, scan_decl_type_vars};

pub(super) fn parse_struct_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::StructDecl);
    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }
    i.env.state.sink.lex(&decl_kw);

    let mut leading_info = decl_kw.trailing_trivia_info();
    let Some(name) = scan_stmt_lex(leading_info, i.rb()) else {
        i.env.state.sink.finish();
        return Some(Either::Left(leading_info));
    };
    leading_info = name.trailing_trivia_info();
    if name.kind != SyntaxKind::Ident {
        emit_invalid(i.rb(), name);
        i.env.state.sink.finish();
        return Some(Either::Left(leading_info));
    }
    i.env.state.sink.lex(&name);

    let vars = scan_decl_type_vars(i.rb(), leading_info, false)?;
    leading_info = vars.leading_info;
    let with_kw = vars.with_kw;

    let mut body_parsed = false;
    if let Some(next) = peek_stmt_lex(leading_info, i.rb()) {
        match next.kind {
            SyntaxKind::BraceL => {
                let open = scan_stmt_lex(leading_info, i.rb())?;
                leading_info = parse_struct_named_fields_after_open(i.rb(), open)?;
                body_parsed = true;
            }
            SyntaxKind::ParenL => {
                let open = scan_stmt_lex(leading_info, i.rb())?;
                leading_info = parse_struct_tuple_fields_after_open(i.rb(), open)?;
                body_parsed = true;
            }
            SyntaxKind::Colon => {
                let colon = scan_stmt_lex(leading_info, i.rb())?;
                i.env.state.sink.lex(&colon);
                let base_indent = i.env.indent;
                leading_info = parse_struct_named_fields_indent_block(
                    i.rb(),
                    colon.trailing_trivia_info(),
                    base_indent,
                )?;
                body_parsed = true;
            }
            _ => {}
        }
    }

    if !body_parsed
        && matches!(leading_info, TriviaInfo::Newline { indent, .. } if indent > i.env.indent)
    {
        i.env.state.sink.start(SyntaxKind::InvalidToken);
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(leading_info));
    }

    let out = finish_with_or_stmt_stop(i.rb(), leading_info, with_kw)?;
    i.env.state.sink.finish();
    Some(out)
}

pub(super) fn parse_struct_named_fields_after_open<I: EventInput, S: EventSink>(
    i: In<I, S>,
    open: Lex,
) -> Option<TriviaInfo> {
    let mut machine = StructNamedFieldsBraceMachine;
    machine.parse_delimited_list(i, open)
}

pub(super) fn parse_struct_tuple_fields_after_open<I: EventInput, S: EventSink>(
    i: In<I, S>,
    open: Lex,
) -> Option<TriviaInfo> {
    let mut machine = StructTupleFieldsBraceMachine;
    machine.parse_delimited_list(i, open)
}

fn parse_struct_named_fields_indent_block<I: EventInput, S: EventSink>(
    i: In<I, S>,
    leading_info: TriviaInfo,
    base_indent: usize,
) -> Option<TriviaInfo> {
    let mut machine = StructNamedFieldsIndentMachine;
    machine.parse_indent_list(i, leading_info, base_indent)
}

fn parse_struct_named_field<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<(TriviaInfo, Option<Lex>)> {
    let Some(name) = scan_stmt_lex(leading_info, i.rb()) else {
        return Some((leading_info, None));
    };
    let info = name.trailing_trivia_info();
    i.env.state.sink.start(SyntaxKind::StructField);
    if name.kind != SyntaxKind::Ident {
        emit_invalid(i.rb(), name);
        i.env.state.sink.finish();
        return Some((info, None));
    }
    i.env.state.sink.lex(&name);

    if matches!(info, TriviaInfo::Newline { .. }) {
        i.env.state.sink.finish();
        return Some((info, None));
    }

    if let Some(next) = peek_stmt_lex(info, i.rb()) {
        if next.kind == SyntaxKind::Colon {
            let colon = scan_stmt_lex(info, i.rb())?;
            i.env.state.sink.lex(&colon);
            let parsed = parse_type_with_stops(
                i.rb(),
                colon.trailing_trivia_info(),
                &[SyntaxKind::Comma, SyntaxKind::BraceR],
            )?;
            i.env.state.sink.finish();
            return match parsed {
                Either::Left(next_info) => Some((next_info, None)),
                Either::Right(stop) => Some((stop.trailing_trivia_info(), Some(stop))),
            };
        }
    }
    i.env.state.sink.finish();
    Some((info, None))
}

struct StructNamedFieldsIndentMachine;

impl<I: EventInput, S: EventSink> IndentListMachine<I, S> for StructNamedFieldsIndentMachine {
    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        _block_indent: usize,
    ) -> Option<(TriviaInfo, Option<Lex>)> {
        parse_struct_named_field(i, leading_info)
    }

    fn is_item_separator(&self, kind: SyntaxKind) -> bool {
        matches!(kind, SyntaxKind::Comma)
    }
}

struct StructNamedFieldsBraceMachine;

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for StructNamedFieldsBraceMachine {
    fn end_kind(&self) -> SyntaxKind {
        SyntaxKind::BraceR
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
        let old_indent = i.env.indent;
        i.env.indent = base_indent;
        let (info, stop) = parse_struct_named_field(i.rb(), leading_info)?;
        i.env.indent = old_indent;
        if let Some(stop) = stop {
            return Some(Either::Right(stop));
        }
        if let Some(next) = peek_stmt_lex(info, i.rb()) {
            if matches!(next.kind, SyntaxKind::Comma | SyntaxKind::BraceR) {
                let stop = scan_stmt_lex(info, i.rb())?;
                return Some(Either::Right(stop));
            }
        }
        Some(Either::Left(info))
    }
}

struct StructTupleFieldsBraceMachine;

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for StructTupleFieldsBraceMachine {
    fn end_kind(&self) -> SyntaxKind {
        SyntaxKind::ParenR
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
        let old_indent = i.env.indent;
        i.env.indent = base_indent;
        i.env.state.sink.start(SyntaxKind::StructField);
        let parsed = parse_type_with_stops(
            i.rb(),
            leading_info,
            &[SyntaxKind::Comma, SyntaxKind::ParenR],
        )?;
        i.env.state.sink.finish();
        i.env.indent = old_indent;
        match parsed {
            Either::Right(stop) => Some(Either::Right(stop)),
            Either::Left(info) => {
                if let Some(next) = peek_stmt_lex(info, i.rb()) {
                    if matches!(next.kind, SyntaxKind::Comma | SyntaxKind::ParenR) {
                        let stop = scan_stmt_lex(info, i.rb())?;
                        return Some(Either::Right(stop));
                    }
                }
                Some(Either::Left(info))
            }
        }
    }
}
