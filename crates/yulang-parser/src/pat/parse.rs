use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::parse_expr;
use crate::expr::rule::{parse_rule_expr, parse_rule_lit};
use crate::lex::{Lex, SyntaxKind, Token, TriviaInfo};
use crate::parse::{DelimitedListMachine, emit_invalid};
use crate::pat::scan::{PatLedTag, PatNudTag, scan_pat_led, scan_pat_nud};
use crate::sink::EventSink;
use crate::string::parse::parse_string_lit;
use crate::typ::parse::parse_type;

pub fn parse_pattern<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    i: In<I, S>,
) -> Option<Either<TriviaInfo, Lex>> {
    Some(parse_pattern_bp(Prec::Lowest, leading_info, i)?.unwrap())
}

fn parse_pattern_bp<I: EventInput, S: EventSink>(
    min_prec: Prec,
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<PatLedTag>>> {
    let nud = scan_pat_nud(leading_info, i.rb())?;
    parse_pattern_from_nud_bp(min_prec, i, nud)
}

pub fn parse_pattern_from_nud<I: EventInput, S: EventSink>(
    i: In<I, S>,
    nud: Token<PatNudTag>,
) -> Option<Either<TriviaInfo, Lex>> {
    Some(parse_pattern_from_nud_bp(Prec::Lowest, i, nud)?.unwrap())
}

fn parse_pattern_from_nud_bp<I: EventInput, S: EventSink>(
    min_prec: Prec,
    mut i: In<I, S>,
    nud: Token<PatNudTag>,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<PatLedTag>>> {
    let leading_info = match nud.tag {
        PatNudTag::Stop => return Some(Ok(Either::Right(nud.lex))),
        PatNudTag::Atom => {
            i.env.state.sink.start(SyntaxKind::Pattern);
            i.env.state.sink.lex(&nud.lex);
            nud.lex.trailing_trivia_info()
        }
        PatNudTag::PolyVariantStart => {
            i.env.state.sink.start(SyntaxKind::Pattern);
            i.env.state.sink.lex(&nud.lex);
            let rhs = scan_pat_nud(nud.lex.trailing_trivia_info(), i.rb())?;
            match rhs.tag {
                PatNudTag::Atom if rhs.lex.kind == SyntaxKind::Ident => {
                    i.env.state.sink.lex(&rhs.lex);
                    rhs.lex.trailing_trivia_info()
                }
                _ => {
                    emit_invalid(i.rb(), rhs.lex.clone());
                    rhs.lex.trailing_trivia_info()
                }
            }
        }
        PatNudTag::StringStart => {
            i.env.state.sink.start(SyntaxKind::Pattern);
            if nud.lex.text.len() == 1 {
                parse_rule_lit(i.rb(), nud.lex)?
            } else {
                parse_string_lit(i.rb(), nud.lex)?
            }
        }
        PatNudTag::Rule => {
            i.env.state.sink.start(SyntaxKind::Pattern);
            let after = parse_rule_expr(i.rb(), nud.lex)?;
            i.env.state.sink.finish();
            return Some(Ok(Either::Left(after)));
        }
        PatNudTag::OpenParen => {
            i.env.state.sink.start(SyntaxKind::Pattern);
            delimited(
                i.rb(),
                SyntaxKind::PatParenGroup,
                SyntaxKind::ParenR,
                nud.lex,
            )?
        }
        PatNudTag::OpenBracket => {
            i.env.state.sink.start(SyntaxKind::Pattern);
            parse_pat_list_group(i.rb(), nud.lex)?
        }
        PatNudTag::OpenBrace => {
            i.env.state.sink.start(SyntaxKind::Pattern);
            parse_pat_record_group(i.rb(), nud.lex)?
        }
    };
    let result = parse_tail_bp(min_prec, leading_info, i.rb())?;
    i.env.state.sink.finish();
    Some(result)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Prec {
    Lowest = 0,
    Or = 1,
    As = 2,
    TypeAnn = 3,
}

fn parse_tail_bp<I: EventInput, S: EventSink>(
    min_prec: Prec,
    mut leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<PatLedTag>>> {
    let mut prev_led = None;
    loop {
        if i.env.ml_arg && leading_info != TriviaInfo::None
            || i.env.inline && matches!(leading_info, TriviaInfo::Newline { .. })
            || matches!(leading_info, TriviaInfo::Newline { .. })
                && i.env.state.line_indent <= i.env.indent
        {
            return Some(Ok(Either::Left(leading_info)));
        }
        let Some(led) = prev_led
            .take()
            .map(Some)
            .or_else(|| i.maybe_fn(|i| scan_pat_led(leading_info, i)))?
        else {
            return Some(Ok(Either::Left(leading_info)));
        };
        match led.tag {
            PatLedTag::Stop => return Some(Ok(Either::Right(led.lex))),
            PatLedTag::DotField => {
                i.env.state.sink.start(SyntaxKind::Field);
                i.env.state.sink.lex(&led.lex);
                i.env.state.sink.finish();
                leading_info = led.lex.trailing_trivia_info();
            }
            PatLedTag::PathSep => {
                i.env.state.sink.start(SyntaxKind::PathSep);
                i.env.state.sink.lex(&led.lex);
                let rhs_leading = led.lex.trailing_trivia_info();
                let rhs = scan_pat_nud(rhs_leading, i.rb())?;
                leading_info =
                    if matches!(rhs.tag, PatNudTag::Atom) && rhs.lex.kind == SyntaxKind::Ident {
                        i.env.state.sink.lex(&rhs.lex);
                        rhs.lex.trailing_trivia_info()
                    } else {
                        emit_invalid(i.rb(), rhs.lex.clone());
                        rhs.lex.trailing_trivia_info()
                    };
                i.env.state.sink.finish();
            }
            PatLedTag::KwAs if min_prec <= Prec::As => {
                i.env.state.sink.start(SyntaxKind::PatAs);
                i.env.state.sink.lex(&led.lex);
                let rhs_leading = led.lex.trailing_trivia_info();
                let rhs = scan_pat_nud(rhs_leading, i.rb())?;
                match rhs.tag {
                    PatNudTag::Stop => {
                        i.env.state.sink.finish();
                        return Some(Ok(Either::Right(rhs.lex)));
                    }
                    PatNudTag::Atom if rhs.lex.kind == SyntaxKind::Ident => {
                        i.env.state.sink.lex(&rhs.lex);
                        i.env.state.sink.finish();
                        leading_info = rhs.lex.trailing_trivia_info();
                    }
                    _ => {
                        emit_invalid(i.rb(), rhs.lex.clone());
                        i.env.state.sink.finish();
                        leading_info = rhs.lex.trailing_trivia_info();
                    }
                }
            }
            PatLedTag::Colon if min_prec <= Prec::TypeAnn => {
                i.env.state.sink.start(SyntaxKind::TypeAnn);
                i.env.state.sink.lex(&led.lex);
                let rhs_leading = led.lex.trailing_trivia_info();
                match parse_type(rhs_leading, i.rb())? {
                    Either::Left(info) => {
                        leading_info = info;
                        i.env.state.sink.finish();
                    }
                    Either::Right(stop) => {
                        i.env.state.sink.finish();
                        return Some(Ok(Either::Right(stop)));
                    }
                }
            }
            PatLedTag::Pipe if min_prec <= Prec::Or => {
                i.env.state.sink.start(SyntaxKind::PatOr);
                i.env.state.sink.lex(&led.lex);
                match parse_pattern_bp(Prec::Or, led.lex.trailing_trivia_info(), i.rb())? {
                    Ok(Either::Left(next_info)) => {
                        leading_info = next_info;
                        i.env.state.sink.finish();
                    }
                    Ok(Either::Right(stop)) => {
                        i.env.state.sink.finish();
                        i.env.state.sink.finish();
                        return Some(Ok(Either::Right(stop)));
                    }
                    Err(led) => {
                        prev_led = Some(led);
                        i.env.state.sink.finish();
                    }
                }
            }
            PatLedTag::CallStart => {
                i.env.state.sink.start(SyntaxKind::ApplyC);
                let next_info = parse_call_group(i.rb(), led.lex)?;
                i.env.state.sink.finish();
                leading_info = next_info;
            }
            PatLedTag::MlNud(nud_tag) => {
                i.env.state.sink.start(SyntaxKind::ApplyML);
                let nud = Token {
                    lex: led.lex,
                    tag: nud_tag,
                };
                let mut j = i.rb();
                j.env.ml_arg = true;
                match parse_pattern_from_nud_bp(min_prec, j, nud)? {
                    Ok(Either::Left(info)) => {
                        leading_info = info;
                        i.env.state.sink.finish();
                    }
                    Ok(Either::Right(stop)) => {
                        i.env.state.sink.finish();
                        return Some(Ok(Either::Right(stop)));
                    }
                    Err(token) => prev_led = Some(token),
                }
            }
            PatLedTag::Invalid => {
                emit_invalid(i.rb(), led.lex);
            }
            _ => {
                i.env.state.sink.finish();
                return Some(Err(led));
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
    let mut machine = PatExprListMachine::new(end_kind);
    machine.parse_delimited_list(i, open_lex)
}

fn parse_pat_record_group<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::PatRecord);
    let mut machine = PatRecordFieldMachine::new(SyntaxKind::BraceR);
    let info = machine.parse_delimited_list(i.rb(), open_lex)?;
    i.env.state.sink.finish();
    Some(info)
}

fn parse_pat_list_group<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::PatList);
    let mut machine = PatListItemMachine::new(SyntaxKind::BracketR);
    let info = machine.parse_delimited_list(i.rb(), open_lex)?;
    i.env.state.sink.finish();
    Some(info)
}

struct PatExprListMachine {
    end_kind: SyntaxKind,
}

impl PatExprListMachine {
    fn new(end_kind: SyntaxKind) -> Self {
        Self { end_kind }
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for PatExprListMachine {
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
        let old_indent = i.env.indent;
        let old_stop = i.env.stop.clone();
        i.env.indent = base_indent;
        i.env.stop.insert(self.end_kind);
        i.env.stop.insert(SyntaxKind::Comma);
        let parsed = parse_pattern(leading_info, i.rb());
        i.env.stop = old_stop;
        i.env.indent = old_indent;
        parsed
    }
}

struct PatListItemMachine {
    end_kind: SyntaxKind,
}

impl PatListItemMachine {
    fn new(end_kind: SyntaxKind) -> Self {
        Self { end_kind }
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for PatListItemMachine {
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
        let head = scan_pat_nud(leading_info, i.rb())?;
        if head.lex.kind == SyntaxKind::DotDot {
            i.env.state.sink.start(SyntaxKind::PatSpread);
            i.env.state.sink.lex(&head.lex);
            let old_indent = i.env.indent;
            let old_stop = i.env.stop.clone();
            i.env.indent = base_indent;
            i.env.stop.insert(self.end_kind);
            i.env.stop.insert(SyntaxKind::Comma);
            let parsed = parse_pattern(head.lex.trailing_trivia_info(), i.rb());
            i.env.stop = old_stop;
            i.env.indent = old_indent;
            i.env.state.sink.finish();
            return Some(parsed?);
        }
        if matches!(head.tag, PatNudTag::Stop) {
            return Some(Either::Right(head.lex));
        }

        let old_indent = i.env.indent;
        let old_stop = i.env.stop.clone();
        i.env.indent = base_indent;
        i.env.stop.insert(self.end_kind);
        i.env.stop.insert(SyntaxKind::Comma);
        let parsed = parse_pattern_from_nud(i.rb(), head);
        i.env.stop = old_stop;
        i.env.indent = old_indent;
        parsed
    }
}

struct PatRecordFieldMachine {
    end_kind: SyntaxKind,
}

impl PatRecordFieldMachine {
    fn new(end_kind: SyntaxKind) -> Self {
        Self { end_kind }
    }
}

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for PatRecordFieldMachine {
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
        let head = scan_pat_nud(leading_info, i.rb())?;
        if head.lex.kind == SyntaxKind::DotDot {
            i.env.state.sink.start(SyntaxKind::PatSpread);
            i.env.state.sink.lex(&head.lex);
            let old_indent = i.env.indent;
            let old_stop = i.env.stop.clone();
            i.env.indent = base_indent;
            i.env.stop.insert(self.end_kind);
            i.env.stop.insert(SyntaxKind::Comma);
            let parsed = parse_pattern(head.lex.trailing_trivia_info(), i.rb());
            i.env.stop = old_stop;
            i.env.indent = old_indent;
            i.env.state.sink.finish();
            return Some(parsed?);
        }
        if matches!(head.tag, PatNudTag::Stop) {
            return Some(Either::Right(head.lex));
        }

        i.env.state.sink.start(SyntaxKind::PatField);
        if !matches!(head.tag, PatNudTag::Atom) || head.lex.kind != SyntaxKind::Ident {
            emit_invalid(i.rb(), head.lex);
            i.env.state.sink.finish();
            return Some(Either::Left(leading_info));
        }

        i.env.state.sink.lex(&head.lex);
        let after_name = head.lex.trailing_trivia_info();
        if matches!(after_name, TriviaInfo::Newline { .. }) {
            i.env.state.sink.finish();
            return Some(Either::Left(after_name));
        }

        let sep = scan_pat_nud(after_name, i.rb())?;
        if sep.lex.kind != SyntaxKind::Colon && sep.lex.kind != SyntaxKind::Equal {
            if !matches!(sep.tag, PatNudTag::Stop) {
                emit_invalid(i.rb(), sep.lex.clone());
            }
            i.env.state.sink.finish();
            return Some(Either::Right(sep.lex));
        }

        i.env.state.sink.lex(&sep.lex);
        let old_indent = i.env.indent;
        let old_stop = i.env.stop.clone();
        i.env.indent = base_indent;
        i.env.stop.insert(self.end_kind);
        i.env.stop.insert(SyntaxKind::Comma);
        if sep.lex.kind == SyntaxKind::Colon {
            i.env.stop.insert(SyntaxKind::Equal);
        }
        let parsed = if sep.lex.kind == SyntaxKind::Equal {
            parse_expr(sep.lex.trailing_trivia_info(), i.rb())
        } else {
            let parsed = parse_pattern(sep.lex.trailing_trivia_info(), i.rb())?;
            if let Either::Right(eq) = &parsed {
                if eq.kind == SyntaxKind::Equal {
                    i.env.state.sink.lex(eq);
                    parse_expr(eq.trailing_trivia_info(), i.rb())
                } else {
                    Some(Either::Right(eq.clone()))
                }
            } else {
                Some(parsed)
            }
        };
        i.env.stop = old_stop;
        i.env.indent = old_indent;
        i.env.state.sink.finish();
        Some(parsed?)
    }
}
