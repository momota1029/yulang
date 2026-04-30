use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::scan::{ExprLedTag, ExprNudTag, scan_expr_led, scan_expr_nud};
use crate::lex::{Lex, SyntaxKind, Token, TriviaInfo};
use crate::op::BpVec;
use crate::parse::emit_invalid;
use crate::sink::EventSink;
use crate::stmt::{parse_indent_stmt_block, parse_statement};
use crate::typ::parse::parse_type;

use super::control::parse_inline_or_indent;
use super::core::{parse_expr_bp, parse_expr_from_nud};
use super::group::{delimited, parse_call_group};

pub(super) fn parse_tail_bp<I: EventInput, S: EventSink>(
    min_bp: Option<&BpVec>,
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    if i.env.ml_arg && leading_info != TriviaInfo::None
        || matches!(leading_info, TriviaInfo::Newline { .. })
    {
        return Some(Ok(Either::Left(leading_info)));
    }
    let Some(led) = i.maybe_fn(|i| scan_expr_led(leading_info, i))? else {
        return Some(Ok(Either::Left(leading_info)));
    };
    pratt_tail_bp(min_bp, led, i)
}
pub(super) fn pratt_tail_bp<I: EventInput, S: EventSink>(
    min_bp: Option<&BpVec>,
    led: Token<ExprLedTag>,
    mut i: In<I, S>,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    match &led.tag {
        ExprLedTag::Stop => return Some(Ok(Either::Right(led.lex))),
        ExprLedTag::Field => {
            i.env.state.sink.start(SyntaxKind::Field);
            i.env.state.sink.lex(&led.lex);
            i.env.state.sink.finish();
            parse_tail_bp(min_bp, led.lex.trailing_trivia_info(), i)
        }
        ExprLedTag::PathSep => {
            i.env.state.sink.start(SyntaxKind::PathSep);
            i.env.state.sink.lex(&led.lex);
            let rhs_nud = scan_expr_nud(led.lex.trailing_trivia_info(), i.rb())?;
            if is_path_segment(&rhs_nud) {
                i.env.state.sink.lex(&rhs_nud.lex);
            } else {
                emit_invalid(i.rb(), rhs_nud.lex.clone());
            };
            i.env.state.sink.finish();
            parse_tail_bp(min_bp, rhs_nud.lex.trailing_trivia_info(), i)
        }
        ExprLedTag::CallStart => {
            i.env.state.sink.start(SyntaxKind::ApplyC);
            let next_info = parse_call_group(i.rb(), led.lex)?;
            i.env.state.sink.finish();
            parse_tail_bp(min_bp, next_info, i)
        }
        ExprLedTag::IndexStart => {
            i.env.state.sink.start(SyntaxKind::Index);
            let next_info = delimited(i.rb(), SyntaxKind::Bracket, SyntaxKind::BracketR, led.lex)?;
            i.env.state.sink.finish();
            parse_tail_bp(min_bp, next_info, i)
        }
        ExprLedTag::Colon => {
            if min_bp.is_some() || i.env.ml_arg {
                return Some(Err(led));
            }
            i.env.state.sink.start(SyntaxKind::ApplyColon);
            i.env.state.sink.lex(&led.lex);
            i.env.state.line_indent = i.env.indent;
            let mut rhs = i.rb();
            rhs.env.ml_arg = false;
            match parse_inline_or_indent(rhs, led.lex.trailing_trivia_info())? {
                Either::Left(next_info) => {
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Left(next_info)));
                }
                Either::Right(stop) => {
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Right(stop)));
                }
            }
        }
        ExprLedTag::Assign => {
            if min_bp.is_some() || i.env.ml_arg {
                return Some(Err(led));
            }
            i.env.state.sink.start(SyntaxKind::Assign);
            i.env.state.sink.lex(&led.lex);
            i.env.state.line_indent = i.env.indent;
            let mut rhs = i.rb();
            rhs.env.ml_arg = false;
            match parse_inline_or_indent(rhs, led.lex.trailing_trivia_info())? {
                Either::Left(next_info) => {
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Left(next_info)));
                }
                Either::Right(stop) => {
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Right(stop)));
                }
            }
        }
        ExprLedTag::With => {
            if min_bp.is_some() || i.env.ml_arg {
                return Some(Err(led));
            }
            i.env.state.sink.start(SyntaxKind::WithBlock);
            i.env.state.sink.lex(&led.lex);
            let Some(colon) = scan_expr_led(led.lex.trailing_trivia_info(), i.rb()) else {
                i.env.state.sink.finish();
                return Some(Ok(Either::Left(led.lex.trailing_trivia_info())));
            };
            if !matches!(colon.tag, ExprLedTag::Colon) {
                let next = colon.lex.trailing_trivia_info();
                emit_invalid(i.rb(), colon.lex);
                i.env.state.sink.finish();
                return Some(Ok(Either::Left(next)));
            }
            i.env.state.sink.lex(&colon.lex);
            let base_indent = i.env.indent;
            match colon.lex.trailing_trivia_info() {
                TriviaInfo::Newline { indent, .. } if indent > base_indent => {
                    let next =
                        parse_indent_stmt_block(i.rb(), indent, colon.lex.trailing_trivia_info())?;
                    i.env.state.sink.finish();
                    Some(Ok(Either::Left(next)))
                }
                TriviaInfo::Newline { .. } => {
                    emit_missing_invalid(i.rb());
                    i.env.state.sink.finish();
                    Some(Ok(Either::Left(colon.lex.trailing_trivia_info())))
                }
                info => {
                    let result = match parse_statement(info, i.rb())? {
                        Either::Right(stop) if stop.kind == SyntaxKind::Semicolon => {
                            i.env.state.sink.lex(&stop);
                            Either::Left(stop.trailing_trivia_info())
                        }
                        other => other,
                    };
                    i.env.state.sink.finish();
                    Some(Ok(result))
                }
            }
        }
        ExprLedTag::As => {
            if min_bp.is_some() || i.env.ml_arg {
                return Some(Err(led));
            }
            i.env.state.sink.start(SyntaxKind::TypeAnn);
            i.env.state.sink.lex(&led.lex);
            let rhs_leading = led.lex.trailing_trivia_info();
            match parse_type(rhs_leading, i.rb())? {
                Either::Left(next_info) => {
                    i.env.state.sink.finish();
                    parse_tail_bp(min_bp, next_info, i)
                }
                Either::Right(stop) => {
                    i.env.state.sink.finish();
                    Some(Ok(Either::Right(stop)))
                }
            }
        }
        ExprLedTag::Infix(lbp, rbp) => {
            if let Some(min) = min_bp {
                if lbp < min {
                    return Some(Err(led));
                }
            }
            i.env.state.sink.start(SyntaxKind::InfixNode);
            i.env.state.sink.lex(&led.lex);
            match parse_expr_bp(Some(&rbp), led.lex.trailing_trivia_info(), i.rb())? {
                Ok(Either::Left(next_info)) => {
                    i.env.state.sink.finish();
                    parse_tail_bp(min_bp, next_info, i)
                }
                Ok(Either::Right(stop)) => {
                    i.env.state.sink.finish();
                    Some(Ok(Either::Right(stop)))
                }
                Err(next_led) => {
                    i.env.state.sink.finish();
                    pratt_tail_bp(min_bp, next_led, i)
                }
            }
        }
        ExprLedTag::Pipe => {
            let lbp = pipeline_lbp();
            if let Some(min) = min_bp {
                if &lbp < min {
                    return Some(Err(led));
                }
            }
            let rbp = pipeline_rbp();
            i.env.state.sink.start(SyntaxKind::PipeNode);
            i.env.state.sink.lex(&led.lex);
            match parse_expr_bp(Some(&rbp), led.lex.trailing_trivia_info(), i.rb())? {
                Ok(Either::Left(next_info)) => {
                    i.env.state.sink.finish();
                    parse_tail_bp(min_bp, next_info, i)
                }
                Ok(Either::Right(stop)) => {
                    i.env.state.sink.finish();
                    Some(Ok(Either::Right(stop)))
                }
                Err(next_led) => {
                    i.env.state.sink.finish();
                    pratt_tail_bp(min_bp, next_led, i)
                }
            }
        }
        ExprLedTag::Suffix(lbp) => {
            if let Some(min) = min_bp {
                if lbp < min {
                    return Some(Err(led));
                }
            }
            i.env.state.sink.start(SyntaxKind::SuffixNode);
            i.env.state.sink.lex(&led.lex);
            i.env.state.sink.finish();
            parse_tail_bp(min_bp, led.lex.trailing_trivia_info(), i)
        }
        ExprLedTag::MlNud(nud_tag) => {
            i.env.state.sink.start(SyntaxKind::ApplyML);
            let nud = Token {
                lex: led.lex,
                tag: nud_tag.clone(),
            };
            let mut j = i.rb();
            j.env.ml_arg = true;
            match parse_expr_from_nud(min_bp, j, nud)? {
                Ok(Either::Left(next_info)) => {
                    i.env.state.sink.finish();
                    parse_tail_bp(min_bp, next_info, i)
                }
                Ok(Either::Right(stop)) => {
                    i.env.state.sink.finish();
                    Some(Ok(Either::Right(stop)))
                }
                Err(next_led) => {
                    i.env.state.sink.finish();
                    pratt_tail_bp(min_bp, next_led, i)
                }
            }
        }
    }
}

fn emit_missing_invalid<I: EventInput, S: EventSink>(i: In<I, S>) {
    i.env.state.sink.start(SyntaxKind::InvalidToken);
    i.env.state.sink.finish();
}

fn is_path_segment(token: &Token<ExprNudTag>) -> bool {
    matches!(
        token.lex.kind,
        SyntaxKind::Ident
            | SyntaxKind::SigilIdent
            | SyntaxKind::Prefix
            | SyntaxKind::Infix
            | SyntaxKind::Suffix
            | SyntaxKind::Nullfix
    )
}

fn pipeline_lbp() -> BpVec {
    BpVec::new(vec![5])
}

fn pipeline_rbp() -> BpVec {
    BpVec::new(vec![5, 1])
}
