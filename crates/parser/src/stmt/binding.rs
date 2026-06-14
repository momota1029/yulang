use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::parse_expr;
use crate::lex::{Lex, SyntaxKind, Token, TriviaInfo};
use crate::parse::emit_invalid;
use crate::pat::parse::parse_pattern_from_nud;
use crate::pat::scan::{PatNudTag, scan_pat_nud};
use crate::sink::EventSink;

use super::block::parse_indent_stmt_block;
use super::common::emit_missing_invalid;

pub(super) fn parse_binding_stmt<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    head_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    let after_head = head_kw.trailing_trivia_info();
    let mut j = i.rb();
    j.env.stop.insert(SyntaxKind::Equal);
    let nud = scan_pat_nud(after_head, j);

    let Some(nud) = nud else {
        i.env.state.sink.start(SyntaxKind::Binding);
        i.env.state.sink.start(SyntaxKind::BindingHeader);
        i.env.state.sink.lex(&head_kw);
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(after_head));
    };

    parse_binding_from_nud_inner(i, head_kw, nud)
}

/// `scan_pat_nud` 済みの nud を受け取って Binding をパースする。
/// `parse_visibility_stmt` から vis_kw に続くトークンが確認済みの場合に使う。
pub(super) fn parse_binding_stmt_from_nud<I: EventInput, S: EventSink>(
    i: In<I, S>,
    head_kw: Lex,
    nud: Token<PatNudTag>,
) -> Option<Either<TriviaInfo, Lex>> {
    parse_binding_from_nud_inner(i, head_kw, nud)
}

fn parse_binding_from_nud_inner<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    head_kw: Lex,
    nud: Token<PatNudTag>,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::Binding);
    i.env.state.sink.start(SyntaxKind::BindingHeader);
    i.env.state.sink.lex(&head_kw);

    // nud が Equal stop なら直接 Equal 処理へ（pat なし）
    if matches!(nud.tag, PatNudTag::Stop) && nud.lex.kind == SyntaxKind::Equal {
        let equal = nud.lex;
        i.env.state.sink.lex(&equal);
        i.env.state.sink.finish();
        i.env.state.sink.start(SyntaxKind::BindingBody);
        let body = parse_binding_body(i.rb(), equal.trailing_trivia_info())?;
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(body);
    }

    // nud が他の stop（閉じ括弧等）→ pat なしで終了
    if matches!(nud.tag, PatNudTag::Stop) {
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Right(nud.lex));
    }

    // Atom 等 → parse_pattern_from_nud で pat を完成させる
    let mut j = i.rb();
    j.env.stop.insert(SyntaxKind::Equal);
    let pat_result = parse_pattern_from_nud(j, nud);

    let stop = match pat_result? {
        Either::Right(stop) => stop,
        Either::Left(info) => {
            i.env.state.sink.finish();
            i.env.state.sink.finish();
            return Some(Either::Left(info));
        }
    };

    if stop.kind != SyntaxKind::Equal {
        if matches!(
            stop.kind,
            SyntaxKind::Semicolon
                | SyntaxKind::Comma
                | SyntaxKind::BraceR
                | SyntaxKind::ParenR
                | SyntaxKind::BracketR
        ) {
            i.env.state.sink.finish();
            i.env.state.sink.finish();
            return Some(Either::Right(stop));
        }
        emit_invalid(i.rb(), stop.clone());
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Right(stop));
    }

    i.env.state.sink.lex(&stop);
    i.env.state.sink.finish();

    i.env.state.sink.start(SyntaxKind::BindingBody);
    let body = parse_binding_body(i.rb(), stop.trailing_trivia_info())?;
    i.env.state.sink.finish();
    i.env.state.sink.finish();
    Some(body)
}

fn parse_binding_body<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let binding_line_indent = i.env.indent;
    i.env.state.line_indent = binding_line_indent;

    match leading_info {
        TriviaInfo::Newline { indent, .. } if indent > binding_line_indent => {
            let next = parse_indent_stmt_block(i.rb(), indent, leading_info)?;
            Some(Either::Left(next))
        }
        TriviaInfo::Newline { .. } => {
            emit_missing_invalid(i.rb());
            Some(Either::Left(leading_info))
        }
        _ => match parse_expr(leading_info, i.rb()) {
            Some(parsed) => Some(parsed),
            None => {
                emit_missing_invalid(i.rb());
                Some(Either::Left(leading_info))
            }
        },
    }
}
