use chasa::Back as _;
use chasa::prelude::eoi;
use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::scan::{ExprLedTag, ExprNudTag, scan_expr_led, scan_expr_nud};
use crate::lex::{Lex, SyntaxKind, Token, TriviaInfo};
use crate::parse::{IndentListMachine, emit_invalid};
use crate::pat::parse::{parse_pattern, parse_pattern_from_nud};
use crate::pat::scan::scan_pat_nud;
use crate::scan::scan_dot_field;
use crate::sink::EventSink;

use super::core::{parse_expr_bp, parse_expr_from_nud};
use super::group::delimited;
use super::parse_expr;
use super::tail::pratt_tail_bp;
use crate::stmt::{parse_indent_stmt_block, peek_stmt_lex, scan_stmt_lex};

pub(super) fn parse_inline_or_indent<I: EventInput, S: EventSink>(
    i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let line_indent = i.env.state.line_indent;
    match leading_info {
        TriviaInfo::Newline { indent, .. } if indent > line_indent => {
            let next = parse_indent_stmt_block(i, indent, leading_info)?;
            Some(Either::Left(next))
        }
        TriviaInfo::Newline { .. } => Some(Either::Left(leading_info)),
        _ => parse_expr(leading_info, i),
    }
}

pub(super) fn parse_lambda_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    backslash: Lex,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    if let Some(kw) = parse_case_like_lambda_keyword(i.rb(), &backslash) {
        let config = match kw.kind {
            SyntaxKind::Case => case_config(SyntaxKind::CaseLambdaExpr),
            SyntaxKind::Catch => catch_config(SyntaxKind::CatchLambdaExpr),
            _ => unreachable!("case-like lambda keyword"),
        };
        return parse_case_like_lambda_expr(i, backslash, kw, &config);
    }

    if let Some(kw) = parse_sub_lambda_keyword(i.rb(), &backslash) {
        return parse_sub_lambda_expr(i, backslash, kw);
    }

    if i.lookahead(scan_dot_field).is_some() {
        let led = scan_expr_led(backslash.trailing_trivia_info(), i.rb())?;
        i.env.state.sink.start(SyntaxKind::MethodLambdaExpr);
        i.env.state.sink.lex(&backslash);
        let result = pratt_tail_bp(None, led, i.rb())?;
        i.env.state.sink.finish();
        return Some(result);
    }

    if let Some(label) = parse_recursive_lambda_label(i.rb(), &backslash) {
        i.env.state.sink.start(SyntaxKind::RecursiveLambdaExpr);
        i.env.state.sink.lex(&backslash);
        i.env.state.sink.lex(&label);
        return parse_lambda_after_intro(i.rb(), label.trailing_trivia_info());
    }

    i.env.state.sink.start(SyntaxKind::LambdaExpr);
    i.env.state.sink.lex(&backslash);
    parse_lambda_after_intro(i, backslash.trailing_trivia_info())
}

pub(super) fn parse_sub_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    sub_lex: Lex,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    i.env.state.sink.start(SyntaxKind::SubExpr);
    i.env.state.sink.lex(&sub_lex);

    let leading = parse_sub_label(i.rb(), sub_lex.trailing_trivia_info());
    let nud = scan_expr_nud(leading, i.rb())?;
    let result = match nud.tag {
        ExprNudTag::Stop if nud.lex.kind == SyntaxKind::Colon => {
            i.env.state.sink.lex(&nud.lex);
            i.env.state.line_indent = i.env.indent;
            let body = parse_inline_or_indent(i.rb(), nud.lex.trailing_trivia_info())?;
            i.env.state.sink.finish();
            Ok(body)
        }
        _ => {
            emit_invalid(i.rb(), nud.lex.clone());
            i.env.state.sink.finish();
            Ok(Either::Right(nud.lex))
        }
    };
    Some(result)
}

pub(super) fn is_sub_expr_intro<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading: TriviaInfo,
) -> bool {
    let checkpoint = i.checkpoint();
    let result = (|| {
        let first = peek_stmt_lex(leading, i.rb())?;
        if first.kind == SyntaxKind::Colon {
            return Some(true);
        }
        if first.kind != SyntaxKind::SigilIdent || !first.text.starts_with('\'') {
            return Some(false);
        }
        scan_stmt_lex(leading, i.rb())?;
        let next = peek_stmt_lex(first.trailing_trivia_info(), i.rb())?;
        Some(next.kind == SyntaxKind::Colon)
    })()
    .unwrap_or(false);
    i.rollback(checkpoint);
    result
}

fn parse_case_like_lambda_keyword<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    backslash: &Lex,
) -> Option<Lex> {
    if backslash.trailing_trivia_info() != TriviaInfo::None {
        return None;
    }
    let kw = peek_stmt_lex(TriviaInfo::None, i.rb())?;
    if !matches!(kw.kind, SyntaxKind::Case | SyntaxKind::Catch) {
        return None;
    }
    scan_stmt_lex(TriviaInfo::None, i)
}

fn parse_sub_lambda_keyword<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    backslash: &Lex,
) -> Option<Lex> {
    if backslash.trailing_trivia_info() != TriviaInfo::None {
        return None;
    }
    let kw = peek_stmt_lex(TriviaInfo::None, i.rb())?;
    if kw.kind != SyntaxKind::Ident || kw.text.as_ref() != "sub" {
        return None;
    }
    let mut kw = scan_stmt_lex(TriviaInfo::None, i)?;
    kw.kind = SyntaxKind::Sub;
    Some(kw)
}

fn parse_sub_lambda_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    backslash: Lex,
    sub_lex: Lex,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    i.env.state.sink.start(SyntaxKind::SubLambdaExpr);
    i.env.state.sink.lex(&backslash);
    i.env.state.sink.lex(&sub_lex);
    let leading = parse_sub_label(i.rb(), sub_lex.trailing_trivia_info());
    parse_lambda_after_intro(i, leading)
}

fn parse_recursive_lambda_label<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    backslash: &Lex,
) -> Option<Lex> {
    if backslash.trailing_trivia_info() != TriviaInfo::None {
        return None;
    }
    let label = peek_stmt_lex(TriviaInfo::None, i.rb())?;
    if label.kind != SyntaxKind::SigilIdent || !label.text.starts_with('\'') {
        return None;
    }
    scan_stmt_lex(TriviaInfo::None, i)
}

fn parse_sub_label<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading: TriviaInfo,
) -> TriviaInfo {
    let Some(label) = peek_stmt_lex(leading, i.rb()) else {
        return leading;
    };
    if label.kind != SyntaxKind::SigilIdent || !label.text.starts_with('\'') {
        return leading;
    }
    let Some(label) = scan_stmt_lex(leading, i.rb()) else {
        return leading;
    };
    i.env.state.sink.start(SyntaxKind::SubLabel);
    i.env.state.sink.lex(&label);
    i.env.state.sink.finish();
    label.trailing_trivia_info()
}

fn parse_lambda_after_intro<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    mut leading: TriviaInfo,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    loop {
        if let Some(parsed) = parse_lambda_my_binder(i.rb(), leading)? {
            match parsed {
                Either::Left(info) => {
                    leading = info;
                    continue;
                }
                Either::Right(stop) if stop.kind == SyntaxKind::Arrow => {
                    i.env.state.sink.lex(&stop);
                    i.env.state.line_indent = i.env.indent;
                    let mut body_in = i.rb();
                    body_in.env.ml_arg = false;
                    let body = parse_inline_or_indent(body_in, stop.trailing_trivia_info())?;
                    i.env.state.sink.finish();
                    return Some(Ok(body));
                }
                Either::Right(stop) => {
                    emit_invalid(i.rb(), stop.clone());
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Right(stop)));
                }
            }
        }

        let old_stop = i.env.stop.clone();
        i.env.stop.insert(SyntaxKind::Arrow);
        let nud = scan_pat_nud(leading, i.rb())?;
        let parsed = match nud.tag {
            crate::pat::scan::PatNudTag::Stop if nud.lex.kind == SyntaxKind::Arrow => {
                i.env.state.sink.lex(&nud.lex);
                i.env.state.line_indent = i.env.indent;
                i.env.stop = old_stop;
                let mut body_in = i.rb();
                body_in.env.ml_arg = false;
                let body = parse_inline_or_indent(body_in, nud.lex.trailing_trivia_info())?;
                i.env.state.sink.finish();
                return Some(Ok(body));
            }
            crate::pat::scan::PatNudTag::Stop => {
                i.env.stop = old_stop;
                emit_invalid(i.rb(), nud.lex.clone());
                i.env.state.sink.finish();
                return Some(Ok(Either::Right(nud.lex)));
            }
            _ => {
                let mut j = i.rb();
                j.env.ml_arg = true;
                parse_pattern_from_nud(j, nud)?
            }
        };
        i.env.stop = old_stop;
        match parsed {
            Either::Left(info) => {
                leading = info;
            }
            Either::Right(stop) if stop.kind == SyntaxKind::Arrow => {
                i.env.state.sink.lex(&stop);
                i.env.state.line_indent = i.env.indent;
                let mut body_in = i.rb();
                body_in.env.ml_arg = false;
                let body = parse_inline_or_indent(body_in, stop.trailing_trivia_info())?;
                i.env.state.sink.finish();
                return Some(Ok(body));
            }
            Either::Right(stop) => {
                emit_invalid(i.rb(), stop.clone());
                i.env.state.sink.finish();
                return Some(Ok(Either::Right(stop)));
            }
        }
    }
}

fn parse_lambda_my_binder<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading: TriviaInfo,
) -> Option<Option<Either<TriviaInfo, Lex>>> {
    if !looks_like_lambda_my_binder(i.rb(), leading) {
        return Some(None);
    }

    let my = scan_stmt_lex(leading, i.rb())?;
    i.env.state.sink.lex(&my);
    let mut next_leading = my.trailing_trivia_info();

    loop {
        let old_stop = i.env.stop.clone();
        i.env.stop.insert(SyntaxKind::Arrow);
        i.env.stop.insert(SyntaxKind::Comma);
        let nud = scan_pat_nud(next_leading, i.rb())?;
        let is_ref_pattern = lambda_my_binder_nud_is_ref(&nud);
        let parsed = if is_ref_pattern {
            let mut pattern_in = i.rb();
            pattern_in.env.ml_arg = true;
            parse_pattern_from_nud(pattern_in, nud)?
        } else {
            emit_invalid(i.rb(), nud.lex.clone());
            Either::Left(nud.lex.trailing_trivia_info())
        };
        i.env.stop = old_stop;

        match parsed {
            Either::Left(info) => return Some(Some(Either::Left(info))),
            Either::Right(stop) if stop.kind == SyntaxKind::Comma => {
                i.env.state.sink.lex(&stop);
                next_leading = stop.trailing_trivia_info();
            }
            Either::Right(stop) => return Some(Some(Either::Right(stop))),
        }
    }
}

fn looks_like_lambda_my_binder<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading: TriviaInfo,
) -> bool {
    let checkpoint = i.checkpoint();
    let result = (|| {
        let my = peek_stmt_lex(leading, i.rb())?;
        if my.kind != SyntaxKind::My {
            return Some(false);
        }
        let my = scan_stmt_lex(leading, i.rb())?;
        let nud = scan_pat_nud(my.trailing_trivia_info(), i.rb())?;
        Some(lambda_my_binder_nud_is_ref(&nud))
    })()
    .unwrap_or(false);
    i.rollback(checkpoint);
    result
}

fn lambda_my_binder_nud_is_ref(nud: &Token<crate::pat::scan::PatNudTag>) -> bool {
    matches!(nud.tag, crate::pat::scan::PatNudTag::Atom)
        && nud.lex.kind == SyntaxKind::SigilIdent
        && nud.lex.text.starts_with('&')
        && nud.lex.text.len() > 1
}

pub(super) fn parse_if_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    if_lex: Lex,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    i.env.state.sink.start(SyntaxKind::IfExpr);
    let base_indent = i.env.indent;
    let mut arm_result = parse_if_arm(i.rb(), if_lex)?;

    loop {
        match arm_result {
            Either::Right(stop) if stop.kind == SyntaxKind::Elsif => {
                arm_result = parse_if_arm(i.rb(), stop)?;
            }
            Either::Right(stop) if stop.kind == SyntaxKind::Else => {
                let result = parse_else_arm(i.rb(), stop)?;
                i.env.state.sink.finish();
                return Some(Ok(result));
            }
            Either::Right(stop) => {
                i.env.state.sink.finish();
                return Some(Ok(Either::Right(stop)));
            }
            Either::Left(info) => {
                let can_continue = matches!(info, TriviaInfo::Space)
                    || matches!(info, TriviaInfo::Newline { indent,.. } if indent >= base_indent);
                if !can_continue {
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Left(info)));
                }
                if matches!(info, TriviaInfo::Newline { .. })
                    && !peek_stmt_lex(info, i.rb()).is_some_and(|next| {
                        matches!(next.kind, SyntaxKind::Elsif | SyntaxKind::Else)
                    })
                {
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Left(info)));
                }
                let Some(next_led) = i.maybe_fn(|i| scan_expr_led(info, i))? else {
                    i.env.state.sink.finish();
                    return Some(Ok(Either::Left(info)));
                };
                match next_led.tag {
                    ExprLedTag::Stop if next_led.lex.kind == SyntaxKind::Elsif => {
                        arm_result = parse_if_arm(i.rb(), next_led.lex)?;
                    }
                    ExprLedTag::Stop if next_led.lex.kind == SyntaxKind::Else => {
                        let result = parse_else_arm(i.rb(), next_led.lex)?;
                        i.env.state.sink.finish();
                        return Some(Ok(result));
                    }
                    _ => {
                        i.env.state.sink.finish();
                        return Some(Err(next_led));
                    }
                }
            }
        }
    }
}

fn parse_if_arm<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::IfArm);
    i.env.state.sink.lex(&kw);

    i.env.state.sink.start(SyntaxKind::Cond);
    let mut cond_in = i.rb();
    cond_in.env.stop.insert(SyntaxKind::Colon);
    cond_in.env.stop.insert(SyntaxKind::BraceL);
    let cond = parse_expr_bp(None, kw.trailing_trivia_info(), cond_in)?;
    let stop = match cond {
        Ok(Either::Right(stop)) => stop,
        Ok(Either::Left(info)) => {
            i.env.state.sink.finish();
            i.env.state.sink.finish();
            return Some(Either::Left(info));
        }
        Err(next_led) => {
            let stop = next_led.lex;
            i.env.state.sink.finish();
            i.env.state.sink.finish();
            return Some(Either::Right(stop));
        }
    };
    i.env.state.sink.finish();

    let result = match stop.kind {
        SyntaxKind::Colon => {
            i.env.state.sink.lex(&stop);
            i.env.state.line_indent = i.env.indent;
            parse_inline_or_indent(i.rb(), stop.trailing_trivia_info())?
        }
        SyntaxKind::BraceL => {
            delimited(i.rb(), SyntaxKind::BraceGroup, SyntaxKind::BraceR, stop).map(Either::Left)?
        }
        _ => {
            emit_invalid(i.rb(), stop.clone());
            Either::Right(stop)
        }
    };

    i.env.state.sink.finish();
    Some(result)
}

fn parse_else_arm<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    else_lex: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::ElseArm);
    i.env.state.sink.lex(&else_lex);
    let nud = scan_expr_nud(else_lex.trailing_trivia_info(), i.rb())?;
    let result = match nud.tag {
        ExprNudTag::Stop if nud.lex.kind == SyntaxKind::Colon => {
            i.env.state.sink.lex(&nud.lex);
            i.env.state.line_indent = i.env.indent;
            parse_inline_or_indent(i.rb(), nud.lex.trailing_trivia_info())?
        }
        ExprNudTag::OpenBrace => {
            delimited(i.rb(), SyntaxKind::BraceGroup, SyntaxKind::BraceR, nud.lex)
                .map(Either::Left)?
        }
        _ => match parse_expr_from_nud(None, i.rb(), nud)? {
            Ok(either) => either,
            Err(next_led) => Either::Right(next_led.lex),
        },
    };
    i.env.state.sink.finish();
    Some(result)
}

// ---- case / catch 式 ----

struct CaseLikeConfig {
    expr_node: SyntaxKind,
    block_node: SyntaxKind,
    arm_node: SyntaxKind,
    guard_node: SyntaxKind,
    allow_handler_name: bool,
    allow_inline_list: bool,
    allow_brace_block: bool,
}

pub(super) fn parse_case_expr<I: EventInput, S: EventSink>(
    i: In<I, S>,
    case_lex: Lex,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    let config = case_config(SyntaxKind::CaseExpr);
    parse_case_like_expr(i, case_lex, &config)
}

pub(super) fn parse_catch_expr<I: EventInput, S: EventSink>(
    i: In<I, S>,
    catch_lex: Lex,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    let config = catch_config(SyntaxKind::CatchExpr);
    parse_case_like_expr(i, catch_lex, &config)
}

fn case_config(expr_node: SyntaxKind) -> CaseLikeConfig {
    CaseLikeConfig {
        expr_node,
        block_node: SyntaxKind::CaseBlock,
        arm_node: SyntaxKind::CaseArm,
        guard_node: SyntaxKind::CaseGuard,
        allow_handler_name: false,
        allow_inline_list: true,
        allow_brace_block: false,
    }
}

fn catch_config(expr_node: SyntaxKind) -> CaseLikeConfig {
    CaseLikeConfig {
        expr_node,
        block_node: SyntaxKind::CatchBlock,
        arm_node: SyntaxKind::CatchArm,
        guard_node: SyntaxKind::CatchGuard,
        allow_handler_name: true,
        allow_inline_list: false,
        allow_brace_block: true,
    }
}

fn parse_case_like_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    kw: Lex,
    config: &CaseLikeConfig,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    i.env.state.sink.start(config.expr_node);
    i.env.state.sink.lex(&kw);

    let base_indent = i.env.indent;
    let target_leading = parse_case_like_label(i.rb(), kw.trailing_trivia_info());

    // target expression (the scrutinee)
    let old_stop = i.env.stop.clone();
    i.env.stop.insert(SyntaxKind::Colon);
    if config.allow_brace_block {
        i.env.stop.insert(SyntaxKind::BraceL);
    }
    let target = parse_expr(target_leading, i.rb());
    i.env.stop = old_stop;

    let stop_lex = match target? {
        Either::Right(stop) => stop,
        Either::Left(info) => {
            i.env.state.sink.finish();
            return Some(Ok(Either::Left(info)));
        }
    };

    let result = match stop_lex.kind {
        SyntaxKind::Colon => {
            i.env.state.sink.start(config.block_node);
            i.env.state.sink.lex(&stop_lex);
            let after_colon = stop_lex.trailing_trivia_info();
            let block_result =
                parse_case_block_after_colon(i.rb(), after_colon, base_indent, config)?;
            i.env.state.sink.finish();
            block_result
        }
        SyntaxKind::BraceL => {
            i.env.state.sink.start(config.block_node);
            let after_brace = parse_case_brace_block(i.rb(), stop_lex, config)?;
            i.env.state.sink.finish();
            Either::Left(after_brace)
        }
        _ => {
            emit_invalid(i.rb(), stop_lex.clone());
            Either::Right(stop_lex)
        }
    };

    i.env.state.sink.finish();
    Some(Ok(result))
}

fn parse_case_like_label<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading: TriviaInfo,
) -> TriviaInfo {
    let Some(label) = peek_stmt_lex(leading, i.rb()) else {
        return leading;
    };
    if label.kind != SyntaxKind::SigilIdent || !label.text.starts_with('\'') {
        return leading;
    }
    let Some(label) = scan_stmt_lex(leading, i.rb()) else {
        return leading;
    };
    i.env.state.sink.lex(&label);
    label.trailing_trivia_info()
}

fn parse_case_like_lambda_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    backslash: Lex,
    kw: Lex,
    config: &CaseLikeConfig,
) -> Option<Result<Either<TriviaInfo, Lex>, Token<ExprLedTag>>> {
    i.env.state.sink.start(config.expr_node);
    i.env.state.sink.lex(&backslash);
    i.env.state.sink.lex(&kw);

    let base_indent = i.env.indent;
    let leading = parse_case_like_label(i.rb(), kw.trailing_trivia_info());
    let nud = scan_expr_nud(leading, i.rb())?;
    let result = match nud.tag {
        ExprNudTag::Stop if nud.lex.kind == SyntaxKind::Colon => {
            i.env.state.sink.start(config.block_node);
            i.env.state.sink.lex(&nud.lex);
            let after_colon = nud.lex.trailing_trivia_info();
            let block_result =
                parse_case_block_after_colon(i.rb(), after_colon, base_indent, config)?;
            i.env.state.sink.finish();
            block_result
        }
        ExprNudTag::OpenBrace if config.allow_brace_block => {
            i.env.state.sink.start(config.block_node);
            let after_brace = parse_case_brace_block(i.rb(), nud.lex, config)?;
            i.env.state.sink.finish();
            Either::Left(after_brace)
        }
        _ => {
            emit_invalid(i.rb(), nud.lex.clone());
            Either::Right(nud.lex)
        }
    };

    i.env.state.sink.finish();
    Some(Ok(result))
}

fn parse_case_block_after_colon<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    after_colon: TriviaInfo,
    base_indent: usize,
    config: &CaseLikeConfig,
) -> Option<Either<TriviaInfo, Lex>> {
    match after_colon {
        TriviaInfo::Newline { indent, .. } if indent > base_indent => {
            // インデントブロック
            let mut machine = ArmIndentMachine { config };
            let info = machine.parse_indent_list(i.rb(), after_colon, base_indent)?;
            Some(Either::Left(info))
        }
        TriviaInfo::Newline { .. } => {
            // 空のインデントブロック
            Some(Either::Left(after_colon))
        }
        _ if config.allow_inline_list => {
            // インライン arm リスト (case のみ)
            let mut leading = after_colon;
            loop {
                let arm_result = parse_arm(i.rb(), leading, config)?;
                match arm_result {
                    Either::Right(stop) if stop.kind == SyntaxKind::Comma => {
                        i.env.state.sink.start(SyntaxKind::Separator);
                        i.env.state.sink.lex(&stop);
                        i.env.state.sink.finish();
                        let next = stop.trailing_trivia_info();
                        if matches!(next, TriviaInfo::Newline { .. }) {
                            return Some(Either::Left(next));
                        }
                        leading = next;
                    }
                    other => return Some(other),
                }
            }
        }
        _ => {
            // catch のインライン: 1 arm のみ
            parse_arm(i.rb(), after_colon, config)
        }
    }
}

fn parse_case_brace_block<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open_lex: Lex,
    config: &CaseLikeConfig,
) -> Option<TriviaInfo> {
    i.env.state.sink.lex(&open_lex);
    i.env.ml_arg = false;
    i.env.inline = false;
    let base_indent = i.env.indent;
    let mut leading = open_lex.trailing_trivia_info();

    loop {
        match leading {
            TriviaInfo::Newline { indent, .. } if indent <= base_indent => {
                // 空アイテム時に閉じ括弧を探す
                let Some(nud) = scan_expr_nud(leading, i.rb()) else {
                    return Some(leading);
                };
                if nud.lex.kind == SyntaxKind::BraceR {
                    i.env.state.sink.lex(&nud.lex);
                    return Some(nud.lex.trailing_trivia_info());
                }
                emit_invalid(i.rb(), nud.lex.clone());
                leading = nud.lex.trailing_trivia_info();
            }
            _ => {}
        }

        let Some(arm_result) = parse_arm(i.rb(), leading, config) else {
            return Some(leading);
        };
        match arm_result {
            Either::Right(stop) if stop.kind == SyntaxKind::BraceR => {
                i.env.state.sink.lex(&stop);
                return Some(stop.trailing_trivia_info());
            }
            Either::Right(stop) if stop.kind == SyntaxKind::Comma => {
                i.env.state.sink.start(SyntaxKind::Separator);
                i.env.state.sink.lex(&stop);
                i.env.state.sink.finish();
                leading = stop.trailing_trivia_info();
            }
            Either::Right(stop) => {
                emit_invalid(i.rb(), stop.clone());
                leading = stop.trailing_trivia_info();
            }
            Either::Left(info) => {
                if matches!(info, TriviaInfo::None) && i.maybe(eoi).is_some() {
                    return Some(info);
                }
                leading = info;
            }
        }
    }
}

struct ArmIndentMachine<'c> {
    config: &'c CaseLikeConfig,
}

impl<'c, I: EventInput, S: EventSink> IndentListMachine<I, S> for ArmIndentMachine<'c> {
    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        _block_indent: usize,
    ) -> Option<(TriviaInfo, Option<Lex>)> {
        match parse_arm(i, leading_info, self.config)? {
            Either::Left(info) => Some((info, None)),
            Either::Right(stop) => {
                let next = stop.trailing_trivia_info();
                Some((next, Some(stop)))
            }
        }
    }

    fn is_item_separator(&self, kind: SyntaxKind) -> bool {
        matches!(kind, SyntaxKind::Comma)
    }
}

/// arm のパース: `<pat> ((if|where) <guard>)? -> <body>`
/// catch の場合、pat の後に `, <name>` がありえる
fn parse_arm<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
    config: &CaseLikeConfig,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(config.arm_node);

    // パターンをパース (Arrow と guard keyword を stop に追加)
    let old_stop = i.env.stop.clone();
    i.env.stop.insert(SyntaxKind::Arrow);
    i.env.stop.insert(SyntaxKind::If);
    i.env.stop.insert(SyntaxKind::Where);
    if config.allow_handler_name {
        i.env.stop.insert(SyntaxKind::Comma);
    }
    let pat_result = match parse_pattern(leading_info, i.rb()) {
        Some(result) => result,
        None => {
            i.env.state.sink.finish();
            return Some(Either::Left(leading_info));
        }
    };
    i.env.stop = old_stop;

    let pat_stop = match pat_result {
        Either::Left(info) => {
            // パターンが trivia で終わった = 入力終端
            i.env.state.sink.finish();
            return Some(Either::Left(info));
        }
        Either::Right(stop) => stop,
    };

    // catch: `, name` のオプションハンドラー名
    let next_stop = if config.allow_handler_name && pat_stop.kind == SyntaxKind::Comma {
        i.env.state.sink.lex(&pat_stop);
        // ハンドラー名 (識別子) をパース
        let old_stop = i.env.stop.clone();
        i.env.stop.insert(SyntaxKind::Arrow);
        i.env.stop.insert(SyntaxKind::If);
        i.env.stop.insert(SyntaxKind::Where);
        let name_result = parse_pattern(pat_stop.trailing_trivia_info(), i.rb());
        i.env.stop = old_stop;
        let Some(name_result) = name_result else {
            i.env.state.sink.finish();
            return Some(Either::Left(pat_stop.trailing_trivia_info()));
        };
        match name_result {
            Either::Left(info) => {
                i.env.state.sink.finish();
                return Some(Either::Left(info));
            }
            Either::Right(stop) => stop,
        }
    } else {
        pat_stop
    };

    // guard: `(if|where) <expr> ->` のオプションガード
    let arrow_lex = if matches!(next_stop.kind, SyntaxKind::If | SyntaxKind::Where) {
        i.env.state.sink.start(config.guard_node);
        i.env.state.sink.lex(&next_stop);

        let old_stop = i.env.stop.clone();
        i.env.stop.insert(SyntaxKind::Arrow);
        let guard_result = parse_expr(next_stop.trailing_trivia_info(), i.rb());
        i.env.stop = old_stop;

        let guard_result = match guard_result {
            Some(result) => result,
            None => {
                i.env.state.sink.finish();
                i.env.state.sink.finish();
                return Some(Either::Left(next_stop.trailing_trivia_info()));
            }
        };
        let guard_stop = match guard_result {
            Either::Left(info) => {
                i.env.state.sink.finish();
                i.env.state.sink.finish();
                return Some(Either::Left(info));
            }
            Either::Right(stop) => stop,
        };
        i.env.state.sink.finish();

        if guard_stop.kind != SyntaxKind::Arrow {
            emit_invalid(i.rb(), guard_stop.clone());
            i.env.state.sink.finish();
            return Some(Either::Right(guard_stop));
        }
        guard_stop
    } else if next_stop.kind == SyntaxKind::Arrow {
        next_stop
    } else {
        // 予期しない stop
        i.env.state.sink.finish();
        return Some(Either::Right(next_stop));
    };

    // `->` とボディ
    i.env.state.sink.lex(&arrow_lex);
    i.env.state.line_indent = i.env.indent;
    let body = match parse_inline_or_indent(i.rb(), arrow_lex.trailing_trivia_info()) {
        Some(body) => body,
        None => {
            i.env.state.sink.finish();
            return Some(Either::Left(arrow_lex.trailing_trivia_info()));
        }
    };

    // arm 末尾の `;` は separator として消費
    let result = match body {
        Either::Right(stop) if stop.kind == SyntaxKind::Semicolon => {
            i.env.state.sink.lex(&stop);
            Either::Left(stop.trailing_trivia_info())
        }
        other => other,
    };

    i.env.state.sink.finish();
    Some(result)
}
