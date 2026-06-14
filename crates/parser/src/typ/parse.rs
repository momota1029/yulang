use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, Token, TriviaInfo};
use crate::parse::{DelimitedListMachine, emit_invalid};
use crate::sink::EventSink;
use crate::typ::scan::{TypLedTag, TypNudTag, scan_typ_led, scan_typ_nud};

pub fn parse_type<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Either<TriviaInfo, Lex>> {
    let nud = scan_typ_nud(leading_info, i.rb())?;
    parse_type_from_nud(i, nud)
}

fn parse_type_from_nud<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    nud: Token<TypNudTag>,
) -> Option<Either<TriviaInfo, Lex>> {
    let leading_info = match nud.tag {
        TypNudTag::Stop => return Some(Either::Right(nud.lex)),
        TypNudTag::Atom => {
            i.env.state.sink.start(SyntaxKind::TypeExpr);
            i.env.state.sink.lex(&nud.lex);
            nud.lex.trailing_trivia_info()
        }
        TypNudTag::Forall => {
            i.env.state.sink.start(SyntaxKind::TypeExpr);
            let result = parse_type_forall(i.rb(), nud.lex)?;
            i.env.state.sink.finish();
            return Some(result);
        }
        TypNudTag::OpenParen => {
            i.env.state.sink.start(SyntaxKind::TypeExpr);
            delimited(
                i.rb(),
                SyntaxKind::TypeParenGroup,
                SyntaxKind::ParenR,
                nud.lex,
            )?
        }
        TypNudTag::OpenBrace => {
            i.env.state.sink.start(SyntaxKind::TypeExpr);
            parse_type_record_group(i.rb(), nud.lex)?
        }
        TypNudTag::PolyVariantStart => {
            i.env.state.sink.start(SyntaxKind::TypeExpr);
            parse_type_poly_variant_group(i.rb(), nud.lex)?
        }
        TypNudTag::EffectRowStart => {
            i.env.state.sink.start(SyntaxKind::TypeExpr);
            i.env.state.sink.start(SyntaxKind::TypeEffectRow);
            i.env.state.sink.lex(&nud.lex); // '
            let bracket_leading = nud.lex.trailing_trivia_info();
            let bracket_nud = scan_typ_nud(bracket_leading, i.rb())?;
            let next_info = match bracket_nud.tag {
                TypNudTag::OpenBracket => delimited(
                    i.rb(),
                    SyntaxKind::TypeRow,
                    SyntaxKind::BracketR,
                    bracket_nud.lex,
                )?,
                _ => {
                    emit_invalid(i.rb(), bracket_nud.lex.clone());
                    bracket_nud.lex.trailing_trivia_info()
                }
            };
            i.env.state.sink.finish(); // TypeEffectRow
            next_info
        }
        TypNudTag::OpenBracket => {
            i.env.state.sink.start(SyntaxKind::TypeExpr);
            let leading_info =
                delimited(i.rb(), SyntaxKind::TypeRow, SyntaxKind::BracketR, nud.lex)?;
            let nud = scan_typ_nud(leading_info, i.rb())?;
            match nud.tag {
                TypNudTag::Stop => {
                    i.env.state.sink.finish();
                    return Some(Either::Right(nud.lex));
                }
                TypNudTag::Atom => {
                    i.env.state.sink.lex(&nud.lex);
                    nud.lex.trailing_trivia_info()
                }
                TypNudTag::OpenParen => delimited(
                    i.rb(),
                    SyntaxKind::TypeParenGroup,
                    SyntaxKind::ParenR,
                    nud.lex,
                )?,
                TypNudTag::OpenBracket => {
                    i.env.state.sink.start(SyntaxKind::InvalidToken);
                    let leading_info =
                        delimited(i.rb(), SyntaxKind::TypeRow, SyntaxKind::BracketR, nud.lex)?;
                    i.env.state.sink.finish();
                    leading_info
                }
                TypNudTag::OpenBrace => parse_type_record_group(i.rb(), nud.lex)?,
                TypNudTag::PolyVariantStart => parse_type_poly_variant_group(i.rb(), nud.lex)?,
                TypNudTag::Forall => {
                    let result = parse_type_forall(i.rb(), nud.lex)?;
                    i.env.state.sink.finish();
                    return Some(result);
                }
                TypNudTag::EffectRowStart => {
                    i.env.state.sink.start(SyntaxKind::TypeEffectRow);
                    i.env.state.sink.lex(&nud.lex);
                    let bracket_leading = nud.lex.trailing_trivia_info();
                    let bracket_nud = scan_typ_nud(bracket_leading, i.rb())?;
                    let next_info = match bracket_nud.tag {
                        TypNudTag::OpenBracket => delimited(
                            i.rb(),
                            SyntaxKind::TypeRow,
                            SyntaxKind::BracketR,
                            bracket_nud.lex,
                        )?,
                        _ => {
                            emit_invalid(i.rb(), bracket_nud.lex.clone());
                            bracket_nud.lex.trailing_trivia_info()
                        }
                    };
                    i.env.state.sink.finish(); // TypeEffectRow
                    next_info
                }
            }
        }
    };
    let result = parse_tail(leading_info, i.rb())?;
    i.env.state.sink.finish();
    Some(result)
}

fn parse_type_forall<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    for_lex: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::TypeForall);
    i.env.state.sink.lex(&for_lex);
    let mut leading = for_lex.trailing_trivia_info();

    loop {
        let head = scan_typ_nud(leading, i.rb())?;
        match head.tag {
            TypNudTag::Atom if head.lex.kind == SyntaxKind::SigilIdent => {
                i.env.state.sink.lex(&head.lex);
                leading = head.lex.trailing_trivia_info();
            }
            _ => {
                emit_invalid(i.rb(), head.lex.clone());
                i.env.state.sink.finish();
                return Some(Either::Left(head.lex.trailing_trivia_info()));
            }
        }

        let sep = scan_typ_nud(leading, i.rb())?;
        if sep.lex.kind == SyntaxKind::Colon {
            i.env.state.sink.lex(&sep.lex);
            let rhs_leading = sep.lex.trailing_trivia_info();
            let rhs_nud = scan_typ_nud(rhs_leading, i.rb())?;
            let parsed = parse_type_from_nud(i.rb(), rhs_nud)?;
            i.env.state.sink.finish();
            return Some(parsed);
        }
        leading = sep.lex.trailing_trivia_info();
        if !matches!(sep.tag, TypNudTag::Atom) || sep.lex.kind != SyntaxKind::SigilIdent {
            emit_invalid(i.rb(), sep.lex.clone());
            i.env.state.sink.finish();
            return Some(Either::Left(sep.lex.trailing_trivia_info()));
        }
        i.env.state.sink.lex(&sep.lex);
    }
}

fn parse_tail<I: EventInput, S: EventSink>(
    mut leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Either<TriviaInfo, Lex>> {
    loop {
        if i.env.ml_arg && leading_info != TriviaInfo::None
            || i.env.inline && matches!(leading_info, TriviaInfo::Newline { .. })
            || matches!(leading_info, TriviaInfo::Newline { .. })
                && i.env.state.line_indent <= i.env.indent
        {
            return Some(Either::Left(leading_info));
        }
        let Some(led) = i.maybe_fn(|i| scan_typ_led(leading_info, i))? else {
            return Some(Either::Left(leading_info));
        };
        match led.tag {
            TypLedTag::Stop => return Some(Either::Right(led.lex)),
            TypLedTag::Arrow => {
                i.env.state.sink.start(SyntaxKind::TypeArrow);
                i.env.state.sink.lex(&led.lex);
                let rhs_leading_info = led.lex.trailing_trivia_info();
                let rhs_nud = scan_typ_nud(rhs_leading_info, i.rb())?;
                let rhs_stop = parse_type_from_nud(i.rb(), rhs_nud)?;
                i.env.state.sink.finish();
                return Some(rhs_stop);
            }
            TypLedTag::PathSep => {
                i.env.state.sink.start(SyntaxKind::PathSep);
                i.env.state.sink.lex(&led.lex);
                let rhs_leading_info = led.lex.trailing_trivia_info();
                let next_nud = scan_typ_nud(rhs_leading_info, i.rb())?;
                leading_info = match next_nud.tag {
                    TypNudTag::Stop => {
                        i.env.state.sink.start(SyntaxKind::InvalidToken);
                        i.env.state.sink.lex(&next_nud.lex);
                        i.env.state.sink.finish();
                        next_nud.lex.trailing_trivia_info()
                    }
                    TypNudTag::Atom => {
                        i.env.state.sink.lex(&next_nud.lex);
                        next_nud.lex.trailing_trivia_info()
                    }
                    TypNudTag::OpenParen => delimited(
                        i.rb(),
                        SyntaxKind::TypeParenGroup,
                        SyntaxKind::ParenR,
                        next_nud.lex,
                    )?,
                    TypNudTag::OpenBracket => {
                        i.env.state.sink.start(SyntaxKind::InvalidToken);
                        let leading_info = delimited(
                            i.rb(),
                            SyntaxKind::TypeRow,
                            SyntaxKind::BracketR,
                            next_nud.lex,
                        )?;
                        i.env.state.sink.finish();
                        leading_info
                    }
                    TypNudTag::OpenBrace => parse_type_record_group(i.rb(), next_nud.lex)?,
                    TypNudTag::PolyVariantStart => {
                        parse_type_poly_variant_group(i.rb(), next_nud.lex)?
                    }
                    TypNudTag::Forall => {
                        let result = parse_type_forall(i.rb(), next_nud.lex)?;
                        i.env.state.sink.finish();
                        return Some(result);
                    }
                    TypNudTag::EffectRowStart => {
                        emit_invalid(i.rb(), next_nud.lex.clone());
                        next_nud.lex.trailing_trivia_info()
                    }
                };
                i.env.state.sink.finish();
            }
            TypLedTag::CallStart => {
                i.env.state.sink.start(SyntaxKind::TypeCall);
                let next_info = parse_call_group(i.rb(), led.lex)?;
                i.env.state.sink.finish();
                leading_info = next_info;
            }
            TypLedTag::BracketStart => {
                i.env.state.sink.start(SyntaxKind::TypeArrow);
                let row_next_info =
                    delimited(i.rb(), SyntaxKind::TypeRow, SyntaxKind::BracketR, led.lex)?;
                let Some(after_row) = scan_typ_led(row_next_info, i.rb()) else {
                    i.env.state.sink.finish();
                    return Some(Either::Left(row_next_info));
                };
                match after_row.tag {
                    TypLedTag::Arrow => {
                        i.env.state.sink.lex(&after_row.lex);
                        let rhs_leading_info = after_row.lex.trailing_trivia_info();
                        let rhs_nud = scan_typ_nud(rhs_leading_info, i.rb())?;
                        let rhs_stop = parse_type_from_nud(i.rb(), rhs_nud)?;
                        i.env.state.sink.finish();
                        return Some(rhs_stop);
                    }
                    TypLedTag::Stop => {
                        let stop = after_row.lex;
                        emit_invalid(i.rb(), stop.clone());
                        i.env.state.sink.finish();
                        return Some(Either::Right(stop));
                    }
                    _ => {
                        leading_info = after_row.lex.trailing_trivia_info();
                        emit_invalid(i.rb(), after_row.lex);
                        i.env.state.sink.finish();
                    }
                }
            }
            TypLedTag::MlNud(nud_tag) => {
                let nud = Token {
                    lex: led.lex,
                    tag: nud_tag,
                };
                i.env.state.sink.start(SyntaxKind::TypeApply);
                let mut j = i.rb();
                j.env.ml_arg = true;
                match parse_type_from_nud(j, nud)? {
                    Either::Left(trivia_info) => {
                        leading_info = trivia_info;
                        i.env.state.sink.finish();
                    }
                    Either::Right(stop) => {
                        i.env.state.sink.finish();
                        return Some(Either::Right(stop));
                    }
                }
            }
        }
    }
}

fn delimited<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    node_kind: SyntaxKind,
    end_kind: SyntaxKind,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(node_kind);
    let result = parse_group_body(i.rb(), end_kind, open_lex)?;
    i.env.state.sink.finish();
    Some(result)
}

fn parse_call_group<I: EventInput, S: EventSink>(i: In<I, S>, open_lex: Lex) -> Option<TriviaInfo> {
    parse_group_body(i, SyntaxKind::ParenR, open_lex)
}

fn parse_group_body<I: EventInput, S: EventSink>(
    i: In<I, S>,
    end_kind: SyntaxKind,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    let mut machine = TypeExprListMachine::new(end_kind);
    machine.parse_delimited_list(i, open_lex)
}

fn parse_type_record_group<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::TypeRecord);
    let mut machine = TypeRecordFieldMachine::new(SyntaxKind::BraceR);
    let info = machine.parse_delimited_list(i.rb(), open_lex)?;
    i.env.state.sink.finish();
    Some(info)
}

fn parse_type_poly_variant_group<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    colon_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::TypePolyVariant);
    i.env.state.sink.lex(&colon_lex);
    let brace_nud = scan_typ_nud(colon_lex.trailing_trivia_info(), i.rb())?;
    let info = match brace_nud.tag {
        TypNudTag::OpenBrace => {
            let mut machine = TypePolyVariantMachine::new(SyntaxKind::BraceR);
            machine.parse_delimited_list(i.rb(), brace_nud.lex)?
        }
        _ => {
            emit_invalid(i.rb(), brace_nud.lex.clone());
            brace_nud.lex.trailing_trivia_info()
        }
    };
    i.env.state.sink.finish();
    Some(info)
}

struct TypeExprListMachine {
    end_kind: SyntaxKind,
}

impl TypeExprListMachine {
    fn new(end_kind: SyntaxKind) -> Self {
        Self { end_kind }
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for TypeExprListMachine {
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
        let old_indent = i.env.indent;
        i.env.indent = base_indent;
        let parsed = parse_type(leading_info, i.rb());
        i.env.indent = old_indent;
        parsed
    }
}

struct TypeRecordFieldMachine {
    end_kind: SyntaxKind,
}

impl TypeRecordFieldMachine {
    fn new(end_kind: SyntaxKind) -> Self {
        Self { end_kind }
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for TypeRecordFieldMachine {
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
        let head = scan_typ_nud(leading_info, i.rb())?;
        if matches!(head.tag, TypNudTag::Stop) {
            return Some(Either::Right(head.lex));
        }

        i.env.state.sink.start(SyntaxKind::TypeField);
        if !matches!(head.tag, TypNudTag::Atom) || head.lex.kind != SyntaxKind::Ident {
            emit_invalid(i.rb(), head.lex);
            i.env.state.sink.finish();
            return Some(Either::Left(leading_info));
        }

        i.env.state.sink.lex(&head.lex);
        let after_name = head.lex.trailing_trivia_info();
        let sep = scan_typ_nud(after_name, i.rb())?;
        if sep.lex.kind != SyntaxKind::Colon {
            emit_invalid(i.rb(), sep.lex.clone());
            i.env.state.sink.finish();
            return Some(Either::Right(sep.lex));
        }

        i.env.state.sink.lex(&sep.lex);
        let rhs_leading = sep.lex.trailing_trivia_info();
        let rhs_nud = scan_typ_nud(rhs_leading, i.rb())?;
        if matches!(rhs_nud.tag, TypNudTag::Stop) {
            emit_invalid(i.rb(), rhs_nud.lex.clone());
            i.env.state.sink.finish();
            return Some(Either::Right(rhs_nud.lex));
        }

        let old_indent = i.env.indent;
        i.env.indent = base_indent;
        let parsed = parse_type_from_nud(i.rb(), rhs_nud)?;
        i.env.indent = old_indent;
        i.env.state.sink.finish();
        Some(parsed)
    }
}

struct TypePolyVariantMachine {
    end_kind: SyntaxKind,
}

impl TypePolyVariantMachine {
    fn new(end_kind: SyntaxKind) -> Self {
        Self { end_kind }
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for TypePolyVariantMachine {
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
        let head = scan_typ_nud(leading_info, i.rb())?;
        if matches!(head.tag, TypNudTag::Stop) {
            return Some(Either::Right(head.lex));
        }

        i.env.state.sink.start(SyntaxKind::TypePolyVariantItem);
        if !matches!(head.tag, TypNudTag::Atom) || head.lex.kind != SyntaxKind::Ident {
            emit_invalid(i.rb(), head.lex);
            i.env.state.sink.finish();
            return Some(Either::Left(leading_info));
        }

        i.env.state.sink.lex(&head.lex);
        let mut leading_info = head.lex.trailing_trivia_info();
        loop {
            if matches!(leading_info, TriviaInfo::Newline { .. }) {
                i.env.state.sink.finish();
                return Some(Either::Left(leading_info));
            }
            let next_nud = scan_typ_nud(leading_info, i.rb())?;
            if matches!(next_nud.tag, TypNudTag::Stop) {
                i.env.state.sink.finish();
                return Some(Either::Right(next_nud.lex));
            }

            let old_indent = i.env.indent;
            let old_ml_arg = i.env.ml_arg;
            i.env.indent = base_indent;
            i.env.ml_arg = true;
            let parsed = parse_type_from_nud(i.rb(), next_nud)?;
            i.env.indent = old_indent;
            i.env.ml_arg = old_ml_arg;
            match parsed {
                Either::Left(next_leading) => leading_info = next_leading,
                Either::Right(stop) => {
                    i.env.state.sink.finish();
                    return Some(Either::Right(stop));
                }
            }
        }
    }
}
