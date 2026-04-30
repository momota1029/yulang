use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::{DelimitedListMachine, IndentListMachine, emit_invalid};
use crate::sink::EventSink;

use super::common::{peek_stmt_lex, scan_stmt_lex};
use super::role_decl::parse_type_with_stops;
use super::struct_decl::{
    parse_struct_named_fields_after_open, parse_struct_tuple_fields_after_open,
};
use super::type_decl::{finish_with_or_stmt_stop, scan_decl_type_vars};

pub(super) fn parse_enum_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::EnumDecl);
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
    let mut with_kw = vars.with_kw;

    let mut body_parsed = false;
    if let Some(next) = peek_stmt_lex(leading_info, i.rb()) {
        match next.kind {
            SyntaxKind::BraceL => {
                let open = scan_stmt_lex(leading_info, i.rb())?;
                leading_info = parse_enum_variants_after_open(i.rb(), open)?;
                body_parsed = true;
            }
            SyntaxKind::Colon => {
                let colon = scan_stmt_lex(leading_info, i.rb())?;
                i.env.state.sink.lex(&colon);
                let base_indent = i.env.indent;
                leading_info = parse_enum_variants_indent_block(
                    i.rb(),
                    colon.trailing_trivia_info(),
                    base_indent,
                )?;
                body_parsed = true;
            }
            SyntaxKind::Equal => {
                let eq = scan_stmt_lex(leading_info, i.rb())?;
                i.env.state.sink.lex(&eq);
                match parse_enum_variants_inline(i.rb(), eq.trailing_trivia_info())? {
                    Either::Left(info) => leading_info = info,
                    Either::Right(stop) if stop.kind == SyntaxKind::With => {
                        with_kw = Some(stop);
                    }
                    Either::Right(stop) => {
                        i.env.state.sink.finish();
                        return Some(Either::Right(stop));
                    }
                }
                body_parsed = true;
            }
            _ => {}
        }
    }

    if !body_parsed {
        if matches!(leading_info, TriviaInfo::Newline { indent, .. } if indent > i.env.indent) {
            i.env.state.sink.start(SyntaxKind::InvalidToken);
            i.env.state.sink.finish();
            i.env.state.sink.finish();
            return Some(Either::Left(leading_info));
        }
    }

    let out = finish_with_or_stmt_stop(i.rb(), leading_info, with_kw)?;
    i.env.state.sink.finish();
    Some(out)
}

fn parse_enum_variants_after_open<I: EventInput, S: EventSink>(
    i: In<I, S>,
    open: Lex,
) -> Option<TriviaInfo> {
    let mut machine = EnumVariantsBraceMachine;
    machine.parse_delimited_list(i, open)
}

fn parse_enum_variants_indent_block<I: EventInput, S: EventSink>(
    i: In<I, S>,
    leading_info: TriviaInfo,
    base_indent: usize,
) -> Option<TriviaInfo> {
    let mut machine = EnumVariantsIndentMachine;
    machine.parse_indent_list(i, leading_info, base_indent)
}

fn parse_enum_variants_inline<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    mut leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    loop {
        if matches!(leading_info, TriviaInfo::Newline { .. }) {
            return Some(Either::Left(leading_info));
        }
        let (info, stop) =
            parse_enum_variant(i.rb(), leading_info, &[SyntaxKind::Pipe, SyntaxKind::With])?;
        leading_info = info;
        if let Some(stop) = stop {
            if stop.kind != SyntaxKind::Pipe {
                return Some(Either::Right(stop));
            }
            i.env.state.sink.lex(&stop);
            leading_info = stop.trailing_trivia_info();
        } else {
            if matches!(leading_info, TriviaInfo::Newline { .. }) {
                return Some(Either::Left(leading_info));
            }
            let Some(next) = peek_stmt_lex(leading_info, i.rb()) else {
                return Some(Either::Left(leading_info));
            };
            if next.kind == SyntaxKind::Pipe {
                let pipe = scan_stmt_lex(leading_info, i.rb())?;
                i.env.state.sink.lex(&pipe);
                leading_info = pipe.trailing_trivia_info();
            } else {
                return Some(Either::Left(leading_info));
            }
        }
    }
}

fn parse_enum_variant<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
    type_stops: &[SyntaxKind],
) -> Option<(TriviaInfo, Option<Lex>)> {
    let Some(name) = scan_stmt_lex(leading_info, i.rb()) else {
        return Some((leading_info, None));
    };
    let mut info = name.trailing_trivia_info();
    i.env.state.sink.start(SyntaxKind::EnumVariant);
    if name.kind != SyntaxKind::Ident {
        emit_invalid(i.rb(), name);
        i.env.state.sink.finish();
        return Some((info, None));
    }
    i.env.state.sink.lex(&name);

    if !matches!(info, TriviaInfo::Newline { .. }) {
        if let Some(next) = peek_stmt_lex(info, i.rb()) {
            match next.kind {
                SyntaxKind::BraceL => {
                    let open = scan_stmt_lex(info, i.rb())?;
                    info = parse_struct_named_fields_after_open(i.rb(), open)?;
                }
                SyntaxKind::ParenL => {
                    let open = scan_stmt_lex(info, i.rb())?;
                    info = parse_struct_tuple_fields_after_open(i.rb(), open)?;
                }
                _ => {
                    let parsed = parse_type_with_stops(i.rb(), info, type_stops)?;
                    match parsed {
                        Either::Left(next_info) => info = next_info,
                        Either::Right(stop) => {
                            i.env.state.sink.finish();
                            return Some((stop.trailing_trivia_info(), Some(stop)));
                        }
                    }
                }
            }
        }
    }
    i.env.state.sink.finish();
    Some((info, None))
}

struct EnumVariantsBraceMachine;

struct EnumVariantsIndentMachine;

impl<I: EventInput, S: EventSink> IndentListMachine<I, S> for EnumVariantsIndentMachine {
    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        _block_indent: usize,
    ) -> Option<(TriviaInfo, Option<Lex>)> {
        parse_enum_variant(i, leading_info, &[SyntaxKind::Comma])
    }

    fn is_item_separator(&self, kind: SyntaxKind) -> bool {
        matches!(kind, SyntaxKind::Comma)
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for EnumVariantsBraceMachine {
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
        let (info, stop) = parse_enum_variant(
            i.rb(),
            leading_info,
            &[SyntaxKind::Comma, SyntaxKind::BraceR],
        )?;
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
