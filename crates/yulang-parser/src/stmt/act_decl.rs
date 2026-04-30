use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::emit_invalid;
use crate::sink::EventSink;

use super::common::{peek_stmt_lex, scan_stmt_lex};
use super::role_decl::{parse_role_like_body, parse_type_with_stops};
use super::type_decl::finish_with_or_stmt_stop;

pub(super) fn parse_act_decl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    decl_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::ActDecl);
    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }
    i.env.state.sink.lex(&decl_kw);

    let leading_info = parse_act_name(i.rb(), decl_kw.trailing_trivia_info())?;
    let tail = parse_act_tail(i.rb(), leading_info)?;
    let result = match tail {
        ActTail::BodyStart(Some(punct)) => parse_body_from_punct(i.rb(), punct)?,
        ActTail::BodyStart(None) => parse_role_like_body(i.rb(), leading_info)?,
        ActTail::Instantiation {
            leading_info,
            with_kw,
        } => finish_with_or_stmt_stop(i.rb(), leading_info, with_kw)?,
    };
    i.env.state.sink.finish();
    Some(result)
}

enum ActTail {
    BodyStart(Option<Lex>),
    Instantiation {
        leading_info: TriviaInfo,
        with_kw: Option<Lex>,
    },
}

fn parse_body_from_punct<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    punct: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    match punct.kind {
        SyntaxKind::Semicolon => {
            i.env.state.sink.lex(&punct);
            Some(Either::Left(punct.trailing_trivia_info()))
        }
        SyntaxKind::BraceL => {
            let next = super::block::parse_brace_stmt_block(i.rb(), punct)?;
            Some(Either::Left(next))
        }
        SyntaxKind::Colon => {
            let base_indent = i.env.indent;
            i.env.state.sink.lex(&punct);
            super::block::parse_decl_body_after_colon(
                i.rb(),
                punct.trailing_trivia_info(),
                base_indent,
            )
        }
        _ => {
            let next = punct.trailing_trivia_info();
            emit_invalid(i.rb(), punct);
            Some(Either::Left(next))
        }
    }
}

fn parse_act_tail<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    mut leading_info: TriviaInfo,
) -> Option<ActTail> {
    loop {
        if matches!(leading_info, TriviaInfo::Newline { .. } | TriviaInfo::None) {
            return Some(ActTail::BodyStart(None));
        }

        if let Some(next) = peek_stmt_lex(leading_info, i.rb()) {
            if matches!(
                next.kind,
                SyntaxKind::Colon | SyntaxKind::BraceL | SyntaxKind::Semicolon
            ) {
                return scan_stmt_lex(leading_info, i.rb())
                    .map(|punct| ActTail::BodyStart(Some(punct)));
            }
            if next.kind == SyntaxKind::Equal {
                let eq = scan_stmt_lex(leading_info, i.rb())?;
                i.env.state.sink.lex(&eq);
                let after_eq = eq.trailing_trivia_info();
                let after_source = match parse_type_with_stops(
                    i.rb(),
                    after_eq,
                    &[
                        SyntaxKind::With,
                        SyntaxKind::Colon,
                        SyntaxKind::BraceL,
                        SyntaxKind::Semicolon,
                    ],
                )? {
                    Either::Left(info) => info,
                    Either::Right(stop) => match stop.kind {
                        SyntaxKind::With => {
                            return Some(ActTail::Instantiation {
                                leading_info: stop.trailing_trivia_info(),
                                with_kw: Some(stop),
                            });
                        }
                        SyntaxKind::Colon | SyntaxKind::BraceL | SyntaxKind::Semicolon => {
                            return Some(ActTail::BodyStart(Some(stop)));
                        }
                        _ => {
                            emit_invalid(i.rb(), stop.clone());
                            stop.trailing_trivia_info()
                        }
                    },
                };
                return Some(ActTail::Instantiation {
                    leading_info: after_source,
                    with_kw: None,
                });
            }
            if next.kind == SyntaxKind::With {
                let with_kw = scan_stmt_lex(leading_info, i.rb())?;
                return Some(ActTail::Instantiation {
                    leading_info: with_kw.trailing_trivia_info(),
                    with_kw: Some(with_kw),
                });
            }
            if next.kind == SyntaxKind::ParenL {
                let open = scan_stmt_lex(leading_info, i.rb())?;
                leading_info = parse_type_params_after_open(i.rb(), open)?;
                continue;
            }
        }

        match parse_type_with_stops(
            i.rb(),
            leading_info,
            &[
                SyntaxKind::Equal,
                SyntaxKind::Colon,
                SyntaxKind::BraceL,
                SyntaxKind::Semicolon,
                SyntaxKind::Comma,
                SyntaxKind::ParenR,
            ],
        )? {
            Either::Left(info) => leading_info = info,
            Either::Right(stop) => match stop.kind {
                SyntaxKind::Colon | SyntaxKind::BraceL | SyntaxKind::Semicolon => {
                    return Some(ActTail::BodyStart(Some(stop)));
                }
                SyntaxKind::Equal => {
                    i.env.state.sink.lex(&stop);
                    let after_eq = stop.trailing_trivia_info();
                    let after_source = match parse_type_with_stops(
                        i.rb(),
                        after_eq,
                        &[
                            SyntaxKind::With,
                            SyntaxKind::Colon,
                            SyntaxKind::BraceL,
                            SyntaxKind::Semicolon,
                        ],
                    )? {
                        Either::Left(info) => info,
                        Either::Right(stop) => match stop.kind {
                            SyntaxKind::With => {
                                return Some(ActTail::Instantiation {
                                    leading_info: stop.trailing_trivia_info(),
                                    with_kw: Some(stop),
                                });
                            }
                            SyntaxKind::Colon | SyntaxKind::BraceL | SyntaxKind::Semicolon => {
                                return Some(ActTail::BodyStart(Some(stop)));
                            }
                            _ => {
                                emit_invalid(i.rb(), stop.clone());
                                stop.trailing_trivia_info()
                            }
                        },
                    };
                    return Some(ActTail::Instantiation {
                        leading_info: after_source,
                        with_kw: None,
                    });
                }
                SyntaxKind::With => {
                    return Some(ActTail::Instantiation {
                        leading_info: stop.trailing_trivia_info(),
                        with_kw: Some(stop),
                    });
                }
                SyntaxKind::Comma => {
                    i.env.state.sink.lex(&stop);
                    leading_info = stop.trailing_trivia_info();
                }
                SyntaxKind::ParenR => {
                    emit_invalid(i.rb(), stop.clone());
                    leading_info = stop.trailing_trivia_info();
                }
                _ => {
                    emit_invalid(i.rb(), stop.clone());
                    return Some(ActTail::BodyStart(None));
                }
            },
        }
    }
}

fn parse_act_name<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    mut leading_info: TriviaInfo,
) -> Option<TriviaInfo> {
    let first = scan_stmt_lex(leading_info, i.rb())?;
    if !matches!(first.kind, SyntaxKind::Ident | SyntaxKind::SigilIdent) {
        emit_invalid(i.rb(), first.clone());
        return Some(first.trailing_trivia_info());
    }
    i.env.state.sink.lex(&first);
    leading_info = first.trailing_trivia_info();

    loop {
        let Some(next) = peek_stmt_lex(leading_info, i.rb()) else {
            return Some(leading_info);
        };
        if next.kind != SyntaxKind::ColonColon {
            return Some(leading_info);
        }
        let sep = scan_stmt_lex(leading_info, i.rb())?;
        i.env.state.sink.lex(&sep);
        leading_info = sep.trailing_trivia_info();

        let seg = scan_stmt_lex(leading_info, i.rb())?;
        leading_info = seg.trailing_trivia_info();
        if !matches!(seg.kind, SyntaxKind::Ident | SyntaxKind::SigilIdent) {
            emit_invalid(i.rb(), seg);
            return Some(leading_info);
        }
        i.env.state.sink.lex(&seg);
    }
}

fn parse_type_params_after_open<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.lex(&open);
    let mut leading_info = open.trailing_trivia_info();
    loop {
        let Some(next) = peek_stmt_lex(leading_info, i.rb()) else {
            return Some(leading_info);
        };
        if next.kind == SyntaxKind::ParenR {
            let close = scan_stmt_lex(leading_info, i.rb())?;
            i.env.state.sink.lex(&close);
            return Some(close.trailing_trivia_info());
        }
        match parse_type_with_stops(
            i.rb(),
            leading_info,
            &[SyntaxKind::Comma, SyntaxKind::ParenR],
        )? {
            Either::Left(info) => {
                leading_info = info;
                let Some(tok) = peek_stmt_lex(leading_info, i.rb()) else {
                    return Some(leading_info);
                };
                if tok.kind == SyntaxKind::Comma {
                    let comma = scan_stmt_lex(leading_info, i.rb())?;
                    i.env.state.sink.lex(&comma);
                    leading_info = comma.trailing_trivia_info();
                }
            }
            Either::Right(stop) => match stop.kind {
                SyntaxKind::Comma => {
                    i.env.state.sink.lex(&stop);
                    leading_info = stop.trailing_trivia_info();
                }
                SyntaxKind::ParenR => {
                    i.env.state.sink.lex(&stop);
                    return Some(stop.trailing_trivia_info());
                }
                _ => {
                    emit_invalid(i.rb(), stop.clone());
                    return Some(stop.trailing_trivia_info());
                }
            },
        }
    }
}
