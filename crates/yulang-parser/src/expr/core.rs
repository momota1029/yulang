use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::scan::{ExprLedTag, ExprNudTag, scan_expr_nud};
use crate::lex::{Lex, SyntaxKind, Token, TriviaInfo};
use crate::op::BpVec;
use crate::sink::EventSink;

use super::control::{parse_case_expr, parse_catch_expr, parse_if_expr, parse_lambda_expr};
use super::group::{delimited, parse_list_group};
use super::mark::parse_quoted_mark_expr;
use super::rule::{parse_rule_expr, parse_rule_lit};
use super::string::parse_string_lit;
use super::tail::{parse_tail_bp, pratt_tail_bp};

pub fn parse_expr<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    i: In<I, S>,
) -> Option<Either<TriviaInfo, Lex>> {
    match parse_expr_bp(None, leading_info, i)? {
        Ok(result) => Some(result),
        Err(led) => Some(Either::Right(led.lex)),
    }
}

pub(crate) fn parse_expr_bp<I: EventInput, S: EventSink>(
    min_bp: Option<&BpVec>,
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    let nud = scan_expr_nud(leading_info, i.rb())?;
    parse_expr_from_nud(min_bp, i, nud)
}

pub(super) fn parse_expr_from_nud<I: EventInput, S: EventSink>(
    min_bp: Option<&BpVec>,
    mut i: In<I, S>,
    nud: Token<ExprNudTag>,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    let leading_info = match nud.tag {
        ExprNudTag::Stop => return Some(Ok(Either::Right(nud.lex))),
        ExprNudTag::Atom => {
            i.env.state.sink.start(SyntaxKind::Expr);
            match nud.lex.kind {
                SyntaxKind::If => {
                    let result = parse_if_expr(i.rb(), nud.lex)?;
                    i.env.state.sink.finish();
                    return Some(result);
                }
                SyntaxKind::Case => {
                    let result = parse_case_expr(i.rb(), nud.lex)?;
                    i.env.state.sink.finish();
                    return Some(result);
                }
                SyntaxKind::Catch => {
                    let result = parse_catch_expr(i.rb(), nud.lex)?;
                    i.env.state.sink.finish();
                    return Some(result);
                }
                SyntaxKind::Rule => {
                    let after = parse_rule_expr(i.rb(), nud.lex)?;
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Left(after)));
                }
                _ => {
                    i.env.state.sink.lex(&nud.lex);
                    nud.lex.trailing_trivia_info()
                }
            }
        }
        ExprNudTag::Nullfix => {
            i.env.state.sink.start(SyntaxKind::Expr);
            i.env.state.sink.lex(&nud.lex);
            nud.lex.trailing_trivia_info()
        }
        ExprNudTag::StringStart => {
            i.env.state.sink.start(SyntaxKind::Expr);
            let after = parse_string_lit(i.rb(), nud.lex)?;
            after
        }
        ExprNudTag::RuleLitStart => {
            i.env.state.sink.start(SyntaxKind::Expr);
            let after = parse_rule_lit(i.rb(), nud.lex)?;
            after
        }
        ExprNudTag::OpenParen => {
            i.env.state.sink.start(SyntaxKind::Expr);
            delimited(i.rb(), SyntaxKind::Paren, SyntaxKind::ParenR, nud.lex)?
        }
        ExprNudTag::OpenBracket => {
            i.env.state.sink.start(SyntaxKind::Expr);
            parse_list_group(i.rb(), nud.lex)?
        }
        ExprNudTag::OpenBrace => {
            i.env.state.sink.start(SyntaxKind::Expr);
            let mut j = i.rb();
            j.env.ml_arg = false;
            crate::stmt::parse_brace_stmt_block(j, nud.lex)?
        }
        ExprNudTag::Backslash => {
            i.env.state.sink.start(SyntaxKind::Expr);
            let result = parse_lambda_expr(i.rb(), nud.lex)?;
            i.env.state.sink.finish();
            return Some(result);
        }
        ExprNudTag::Apostrophe => {
            i.env.state.sink.start(SyntaxKind::Expr);
            let result = parse_quoted_mark_expr(i.rb(), nud.lex)?;
            i.env.state.sink.finish();
            return Some(Ok(result));
        }
        ExprNudTag::Prefix(bp) => {
            i.env.state.sink.start(SyntaxKind::Expr);
            i.env.state.sink.start(SyntaxKind::PrefixNode);
            i.env.state.sink.lex(&nud.lex);
            let rhs_nud = scan_expr_nud(nud.lex.trailing_trivia_info(), i.rb())?;
            let result = parse_expr_from_nud(Some(&bp), i.rb(), rhs_nud)?;
            match result {
                Ok(Either::Left(info)) => {
                    i.env.state.sink.finish();
                    info
                }
                Ok(Either::Right(stop)) => {
                    i.env.state.sink.finish();
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Right(stop)));
                }
                Err(next_led) => {
                    // right-hand side parse stopped early due to lower-precedence led;
                    // close PrefixNode and continue outer Expr's tail loop with next_led
                    i.env.state.sink.finish();
                    let result = pratt_tail_bp(min_bp, next_led, i.rb())?;
                    i.env.state.sink.finish();
                    return Some(result);
                }
            }
        }
    };
    let result = parse_tail_bp(min_bp, leading_info, i.rb())?;
    i.env.state.sink.finish();
    Some(result)
}
