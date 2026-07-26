use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::emit_invalid;
use crate::sink::EventSink;

use super::block::{
    parse_brace_stmt_block, parse_companion_brace_stmt_block,
    parse_companion_decl_body_after_colon, parse_decl_body_after_colon,
};
use super::common::{peek_stmt_lex, scan_name_lex, scan_stmt_lex};
use super::impl_decl::parse_impl_after_impl_kw;
use super::role_decl::{parse_role_body_from_stop, parse_role_like_body, parse_type_with_stops};

pub(super) struct TypeVarsScan {
    pub leading_info: TriviaInfo,
    pub with_kw: Option<Lex>,
    pub impl_kw: Option<Lex>,
}

pub(super) fn parse_type_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::TypeDecl);
    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }
    i.env.state.sink.lex(&decl_kw);

    let mut leading_info = decl_kw.trailing_trivia_info();
    let Some(name) = scan_name_lex(leading_info, i.rb()) else {
        i.env.state.sink.finish();
        return Some(Either::Left(leading_info));
    };
    leading_info = name.trailing_trivia_info();
    i.env.state.sink.lex(&name);

    let mut vars = scan_decl_type_vars(i.rb(), leading_info, true)?;
    leading_info = vars.leading_info;

    let header_derives = if vars.impl_kw.is_none() && vars.with_kw.is_none() {
        parse_header_derives(
            i.rb(),
            leading_info,
            &[
                SyntaxKind::Impl,
                SyntaxKind::With,
                SyntaxKind::Equal,
                SyntaxKind::Colon,
                SyntaxKind::BraceL,
                SyntaxKind::Semicolon,
            ],
        )?
    } else {
        Either::Left(leading_info)
    };
    if let Either::Right(stop) = header_derives {
        let out = match stop.kind {
            SyntaxKind::Impl => {
                i.env.state.sink.lex(&stop);
                parse_impl_after_impl_kw(i.rb(), stop.trailing_trivia_info())?
            }
            SyntaxKind::With => {
                i.env.state.sink.lex(&stop);
                parse_with_block_after_kw(i.rb(), stop.trailing_trivia_info())?
            }
            SyntaxKind::Equal => {
                i.env.state.sink.lex(&stop);
                parse_type_rhs(i.rb(), stop.trailing_trivia_info())?
            }
            _ => parse_role_body_from_stop(i.rb(), Some(stop))?,
        };
        i.env.state.sink.finish();
        return Some(out);
    }

    if vars.impl_kw.is_none() && vars.with_kw.is_none() {
        if let Some(next) = peek_stmt_lex(leading_info, i.rb()) {
            if next.kind == SyntaxKind::Impl {
                vars.impl_kw = scan_stmt_lex(leading_info, i.rb());
            } else if next.kind == SyntaxKind::With {
                vars.with_kw = scan_stmt_lex(leading_info, i.rb());
            }
        }
    }

    if let Some(impl_kw) = vars.impl_kw {
        i.env.state.sink.lex(&impl_kw);
        let out = parse_impl_after_impl_kw(i.rb(), impl_kw.trailing_trivia_info())?;
        i.env.state.sink.finish();
        return Some(out);
    }

    if let Some(with_kw) = vars.with_kw {
        i.env.state.sink.lex(&with_kw);
        let out = parse_with_block_after_kw(i.rb(), with_kw.trailing_trivia_info())?;
        i.env.state.sink.finish();
        return Some(out);
    }

    if let Some(next) = peek_stmt_lex(leading_info, i.rb()) {
        if next.kind == SyntaxKind::Equal {
            let eq = scan_stmt_lex(leading_info, i.rb())?;
            i.env.state.sink.lex(&eq);
            let out = parse_type_rhs(i.rb(), eq.trailing_trivia_info())?;
            i.env.state.sink.finish();
            return Some(out);
        }
        if next.kind == SyntaxKind::With {
            let with_kw = scan_stmt_lex(leading_info, i.rb())?;
            i.env.state.sink.lex(&with_kw);
            let out = parse_with_block_after_kw(i.rb(), with_kw.trailing_trivia_info())?;
            i.env.state.sink.finish();
            return Some(out);
        }
    }

    i.env.inline = true;
    let out = parse_role_like_body(i.rb(), leading_info)?;
    i.env.state.sink.finish();
    Some(out)
}

fn parse_type_rhs<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let result = parse_type_with_stops(
        i.rb(),
        leading_info,
        &[
            SyntaxKind::With,
            SyntaxKind::Derives,
            SyntaxKind::Semicolon,
            SyntaxKind::Colon,
            SyntaxKind::BraceL,
            SyntaxKind::Comma,
            SyntaxKind::ParenR,
            SyntaxKind::BracketR,
            SyntaxKind::BraceR,
        ],
    )?;
    match result {
        Either::Left(info) => Some(Either::Left(info)),
        Either::Right(stop) => match stop.kind {
            SyntaxKind::Derives => {
                let mut derives_kw = stop;
                derives_kw.kind = SyntaxKind::Ident;
                match parse_derives_clauses(
                    i.rb(),
                    derives_kw,
                    &[
                        SyntaxKind::With,
                        SyntaxKind::Semicolon,
                        SyntaxKind::Colon,
                        SyntaxKind::BraceL,
                        SyntaxKind::Comma,
                        SyntaxKind::ParenR,
                        SyntaxKind::BracketR,
                        SyntaxKind::BraceR,
                    ],
                )? {
                    Either::Left(info) => Some(Either::Left(info)),
                    Either::Right(stop) => parse_type_rhs_stop(i, stop),
                }
            }
            _ => parse_type_rhs_stop(i, stop),
        },
    }
}

fn parse_type_rhs_stop<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    stop: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    match stop.kind {
        SyntaxKind::With => {
            i.env.state.sink.lex(&stop);
            parse_with_block_after_kw(i.rb(), stop.trailing_trivia_info())
        }
        SyntaxKind::Semicolon => {
            i.env.state.sink.lex(&stop);
            Some(Either::Left(stop.trailing_trivia_info()))
        }
        SyntaxKind::Colon => {
            let base_indent = i.env.indent;
            i.env.state.sink.lex(&stop);
            parse_decl_body_after_colon(i.rb(), stop.trailing_trivia_info(), base_indent)
        }
        SyntaxKind::BraceL => {
            let next = parse_brace_stmt_block(i.rb(), stop)?;
            Some(Either::Left(next))
        }
        SyntaxKind::Comma | SyntaxKind::ParenR | SyntaxKind::BracketR | SyntaxKind::BraceR => {
            Some(Either::Right(stop))
        }
        _ => {
            let next = stop.trailing_trivia_info();
            emit_invalid(i.rb(), stop);
            Some(Either::Left(next))
        }
    }
}

pub(super) fn scan_decl_type_vars<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    mut leading_info: TriviaInfo,
    allow_impl_kw: bool,
) -> Option<TypeVarsScan> {
    let mut out = TypeVarsScan {
        leading_info,
        with_kw: None,
        impl_kw: None,
    };
    i.env.state.sink.start(SyntaxKind::TypeVars);
    loop {
        if matches!(leading_info, TriviaInfo::Newline { .. } | TriviaInfo::None) {
            break;
        }
        let Some(next) = peek_stmt_lex(leading_info, i.rb()) else {
            break;
        };
        if is_derives_clause_start(&next) {
            break;
        }
        match next.kind {
            SyntaxKind::With => {
                out.with_kw = scan_stmt_lex(leading_info, i.rb());
                break;
            }
            SyntaxKind::Impl if allow_impl_kw => {
                out.impl_kw = scan_stmt_lex(leading_info, i.rb());
                break;
            }
            SyntaxKind::Ident | SyntaxKind::SigilIdent => {
                let tok = scan_stmt_lex(leading_info, i.rb())?;
                i.env.state.sink.lex(&tok);
                leading_info = tok.trailing_trivia_info();
                out.leading_info = leading_info;
            }
            _ => break,
        }
    }
    i.env.state.sink.finish();
    Some(out)
}

pub(super) fn parse_with_block_after_kw<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let Some(punct) = scan_stmt_lex(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };
    match punct.kind {
        SyntaxKind::BraceL => {
            let next = parse_companion_brace_stmt_block(i.rb(), punct)?;
            Some(Either::Left(next))
        }
        SyntaxKind::Colon => {
            let base_indent = i.env.indent;
            i.env.state.sink.lex(&punct);
            parse_companion_decl_body_after_colon(i.rb(), punct.trailing_trivia_info(), base_indent)
        }
        _ => {
            let next = punct.trailing_trivia_info();
            emit_invalid(i.rb(), punct);
            Some(Either::Left(next))
        }
    }
}

pub(super) fn finish_with_or_stmt_stop<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
    mut with_kw: Option<Lex>,
) -> Option<Either<TriviaInfo, Lex>> {
    let leading_info = match parse_header_derives(
        i.rb(),
        leading_info,
        &[
            SyntaxKind::With,
            SyntaxKind::Semicolon,
            SyntaxKind::Comma,
            SyntaxKind::ParenR,
            SyntaxKind::BracketR,
            SyntaxKind::BraceR,
        ],
    )? {
        Either::Left(info) => info,
        Either::Right(stop) if stop.kind == SyntaxKind::With => {
            let with_leading_info = stop.leading_trivia_info;
            with_kw = Some(stop);
            with_leading_info
        }
        Either::Right(stop) => return finish_with_or_stmt_stop_from_stop(i, stop),
    };
    if with_kw.is_none() {
        if let Some(next) = peek_stmt_lex(leading_info, i.rb()) {
            if next.kind == SyntaxKind::With {
                with_kw = scan_stmt_lex(leading_info, i.rb());
            }
        }
    }
    if let Some(with_kw) = with_kw {
        i.env.state.sink.lex(&with_kw);
        return parse_with_block_after_kw(i.rb(), with_kw.trailing_trivia_info());
    }

    let Some(next) = peek_stmt_lex(leading_info, i.rb()) else {
        return Some(Either::Left(leading_info));
    };
    match next.kind {
        SyntaxKind::Semicolon => {
            let semi = scan_stmt_lex(leading_info, i.rb())?;
            i.env.state.sink.lex(&semi);
            Some(Either::Left(semi.trailing_trivia_info()))
        }
        SyntaxKind::Comma | SyntaxKind::ParenR | SyntaxKind::BracketR | SyntaxKind::BraceR => {
            let stop = scan_stmt_lex(leading_info, i.rb())?;
            Some(Either::Right(stop))
        }
        _ => Some(Either::Left(leading_info)),
    }
}

fn finish_with_or_stmt_stop_from_stop<I: EventInput, S: EventSink>(
    i: In<I, S>,
    stop: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    match stop.kind {
        SyntaxKind::Semicolon => {
            i.env.state.sink.lex(&stop);
            Some(Either::Left(stop.trailing_trivia_info()))
        }
        SyntaxKind::Comma | SyntaxKind::ParenR | SyntaxKind::BracketR | SyntaxKind::BraceR => {
            Some(Either::Right(stop))
        }
        _ => Some(Either::Left(stop.trailing_trivia_info())),
    }
}

pub(super) fn is_derives_clause_start(lex: &Lex) -> bool {
    lex.kind == SyntaxKind::Ident && lex.text.as_ref() == "derives"
}

pub(super) fn parse_header_derives<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
    outer_stops: &[SyntaxKind],
) -> Option<Either<TriviaInfo, Lex>> {
    let Some(derives_kw) = peek_stmt_lex(leading_info, i.rb())
        .filter(is_derives_clause_start)
        .and_then(|_| scan_stmt_lex(leading_info, i.rb()))
    else {
        return Some(Either::Left(leading_info));
    };
    parse_derives_clauses(i, derives_kw, outer_stops)
}

pub(super) fn parse_derives_clauses<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    mut derives_kw: Lex,
    outer_stops: &[SyntaxKind],
) -> Option<Either<TriviaInfo, Lex>> {
    loop {
        let result = parse_derives_clause(i.rb(), derives_kw, outer_stops)?;
        match result {
            Either::Left(info) => return Some(Either::Left(info)),
            Either::Right(mut stop) if stop.kind == SyntaxKind::Derives => {
                stop.kind = SyntaxKind::Ident;
                derives_kw = stop;
            }
            Either::Right(stop) => return Some(Either::Right(stop)),
        }
    }
}

fn parse_derives_clause<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    derives_kw: Lex,
    outer_stops: &[SyntaxKind],
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::DerivesClause);
    i.env.state.sink.lex(&derives_kw);
    let mut leading_info = derives_kw.trailing_trivia_info();

    loop {
        let mut stops = Vec::with_capacity(outer_stops.len() + 3);
        stops.extend_from_slice(outer_stops);
        stops.extend([SyntaxKind::Comma, SyntaxKind::Via, SyntaxKind::Derives]);
        match parse_type_with_stops(i.rb(), leading_info, &stops)? {
            Either::Left(info) => {
                i.env.state.sink.finish();
                return Some(Either::Left(info));
            }
            Either::Right(stop) => match stop.kind {
                SyntaxKind::Comma => {
                    i.env.state.sink.lex(&stop);
                    leading_info = stop.trailing_trivia_info();
                }
                SyntaxKind::Via => {
                    i.env.state.sink.lex(&stop);
                    let target_info = stop.trailing_trivia_info();
                    let Some(target) = scan_stmt_lex(target_info, i.rb()) else {
                        i.env.state.sink.start(SyntaxKind::InvalidToken);
                        i.env.state.sink.finish();
                        i.env.state.sink.finish();
                        return Some(Either::Left(target_info));
                    };
                    if target.kind == SyntaxKind::Ident {
                        i.env.state.sink.lex(&target);
                    } else {
                        emit_invalid(i.rb(), target.clone());
                    }
                    let target_end = target.trailing_trivia_info();
                    let Some(next) = peek_stmt_lex(target_end, i.rb()) else {
                        i.env.state.sink.finish();
                        return Some(Either::Left(target_end));
                    };
                    if is_derives_clause_start(&next) {
                        let mut next = scan_stmt_lex(target_end, i.rb())?;
                        next.kind = SyntaxKind::Derives;
                        i.env.state.sink.finish();
                        return Some(Either::Right(next));
                    }
                    if outer_stops.contains(&next.kind) {
                        let next = scan_stmt_lex(target_end, i.rb())?;
                        i.env.state.sink.finish();
                        return Some(Either::Right(next));
                    }
                    i.env.state.sink.finish();
                    return Some(Either::Left(target_end));
                }
                _ => {
                    i.env.state.sink.finish();
                    return Some(Either::Right(stop));
                }
            },
        }
    }
}
