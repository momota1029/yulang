use chasa::prelude::*;
use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::parse_expr;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::op::{BpVec, OpDef};
use crate::parse::emit_invalid;
use crate::scan::trivia::scan_trivia;
use crate::sink::EventSink;

use super::block::parse_indent_stmt_block;
use super::common::scan_stmt_lex;

pub(super) fn parse_op_def_stmt<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    visibility: Option<Lex>,
    fixity_kw: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::OpDef);
    i.env.state.sink.start(SyntaxKind::OpDefHeader);

    if let Some(vis) = visibility {
        i.env.state.sink.lex(&vis);
    }

    let fixity = fixity_from_kind(fixity_kw.kind);
    i.env.state.sink.lex(&fixity_kw);

    // `(op_name)`
    let after_fixity = fixity_kw.trailing_trivia_info();
    let Some(paren_l) = scan_stmt_lex(after_fixity, i.rb()) else {
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(after_fixity));
    };
    if paren_l.kind != SyntaxKind::ParenL {
        let next = paren_l.trailing_trivia_info();
        emit_invalid(i.rb(), paren_l);
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(next));
    }
    i.env.state.sink.lex(&paren_l);

    let after_paren_l = paren_l.trailing_trivia_info();
    let Some(op_tok) = scan_op_name(after_paren_l, i.rb()) else {
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(after_paren_l));
    };
    let op_name: Box<str> = op_tok.text.clone();
    i.env.state.sink.lex(&op_tok);

    let after_op = op_tok.trailing_trivia_info();
    let Some(paren_r) = scan_stmt_lex(after_op, i.rb()) else {
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(after_op));
    };
    if paren_r.kind != SyntaxKind::ParenR {
        let next = paren_r.trailing_trivia_info();
        emit_invalid(i.rb(), paren_r);
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(next));
    }
    i.env.state.sink.lex(&paren_r);

    // bp_vec の収集と `=`
    let mut prefix_rbp: Option<BpVec> = None;
    let mut suffix_lbp: Option<BpVec> = None;
    let mut infix_lbp: Option<BpVec> = None;
    let mut infix_rbp: Option<BpVec> = None;

    let after_paren_r = paren_r.trailing_trivia_info();

    let after_bps = match fixity {
        Some(Fixity::Nullfix) => after_paren_r,
        Some(Fixity::Prefix) => {
            let Some(bp_tok) = scan_bp_vec(after_paren_r, i.rb()) else {
                i.env.state.sink.finish();
                i.env.state.sink.finish();
                return Some(Either::Left(after_paren_r));
            };
            prefix_rbp = BpVec::parse(bp_tok.text.as_ref());
            let after = bp_tok.trailing_trivia_info();
            i.env.state.sink.lex(&bp_tok);
            after
        }
        Some(Fixity::Suffix) => {
            let Some(bp_tok) = scan_bp_vec(after_paren_r, i.rb()) else {
                i.env.state.sink.finish();
                i.env.state.sink.finish();
                return Some(Either::Left(after_paren_r));
            };
            suffix_lbp = BpVec::parse(bp_tok.text.as_ref());
            let after = bp_tok.trailing_trivia_info();
            i.env.state.sink.lex(&bp_tok);
            after
        }
        Some(Fixity::Infix) => {
            let Some(lbp_tok) = scan_bp_vec(after_paren_r, i.rb()) else {
                i.env.state.sink.finish();
                i.env.state.sink.finish();
                return Some(Either::Left(after_paren_r));
            };
            infix_lbp = BpVec::parse(lbp_tok.text.as_ref());
            let after_lbp = lbp_tok.trailing_trivia_info();
            i.env.state.sink.lex(&lbp_tok);

            let Some(rbp_tok) = scan_bp_vec(after_lbp, i.rb()) else {
                i.env.state.sink.finish();
                i.env.state.sink.finish();
                return Some(Either::Left(after_lbp));
            };
            infix_rbp = BpVec::parse(rbp_tok.text.as_ref());
            let after = rbp_tok.trailing_trivia_info();
            i.env.state.sink.lex(&rbp_tok);
            after
        }
        None => after_paren_r,
    };

    // op テーブル更新（ローカル）
    update_op_table(
        &mut i, &op_name, fixity, prefix_rbp, infix_lbp, infix_rbp, suffix_lbp,
    );

    // `=` を探す
    let Some(eq_tok) = scan_stmt_lex(after_bps, i.rb()) else {
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(after_bps));
    };
    if eq_tok.kind != SyntaxKind::Equal {
        let next = eq_tok.trailing_trivia_info();
        emit_invalid(i.rb(), eq_tok);
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(next));
    }
    i.env.state.sink.lex(&eq_tok);
    i.env.state.sink.finish(); // OpDefHeader

    // OpDefBody
    i.env.state.sink.start(SyntaxKind::OpDefBody);
    let after_eq = eq_tok.trailing_trivia_info();
    let result = parse_op_def_body(i.rb(), after_eq)?;
    i.env.state.sink.finish(); // OpDefBody
    i.env.state.sink.finish(); // OpDef
    Some(result)
}

fn parse_op_def_body<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let base_indent = i.env.indent;
    match leading_info {
        TriviaInfo::Newline { indent, .. } if indent > base_indent => {
            let next = parse_indent_stmt_block(i.rb(), indent, leading_info)?;
            Some(Either::Left(next))
        }
        TriviaInfo::Newline { .. } => Some(Either::Left(leading_info)),
        _ => parse_expr(leading_info, i.rb()),
    }
}

fn update_op_table<I: EventInput, S: EventSink>(
    i: &mut In<I, S>,
    op_name: &str,
    fixity: Option<Fixity>,
    prefix_rbp: Option<BpVec>,
    infix_lbp: Option<BpVec>,
    infix_rbp: Option<BpVec>,
    suffix_lbp: Option<BpVec>,
) {
    let prev = i
        .env
        .state
        .ops
        .0
        .get(op_name.as_bytes())
        .cloned()
        .unwrap_or_default();
    let updated = match fixity {
        Some(Fixity::Nullfix) => OpDef {
            nullfix: true,
            ..prev
        },
        Some(Fixity::Prefix) => OpDef {
            prefix: prefix_rbp.or(prev.prefix),
            ..prev
        },
        Some(Fixity::Suffix) => OpDef {
            suffix: suffix_lbp.or(prev.suffix),
            ..prev
        },
        Some(Fixity::Infix) => {
            let infix = match (infix_lbp, infix_rbp) {
                (Some(l), Some(r)) => Some((l, r)),
                _ => prev.infix,
            };
            OpDef { infix, ..prev }
        }
        None => prev,
    };
    i.env.state.ops.0.insert(op_name.into(), updated);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fixity {
    Prefix,
    Infix,
    Suffix,
    Nullfix,
}

fn fixity_from_kind(kind: SyntaxKind) -> Option<Fixity> {
    match kind {
        SyntaxKind::Prefix => Some(Fixity::Prefix),
        SyntaxKind::Infix => Some(Fixity::Infix),
        SyntaxKind::Suffix => Some(Fixity::Suffix),
        SyntaxKind::Nullfix => Some(Fixity::Nullfix),
        _ => None,
    }
}

/// `(op_name)` の op_name 部分をスキャン（空白・括弧・記号以外の任意文字列）
fn scan_op_name<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Lex> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return None;
    }
    let parser = one_of(|ch: char| {
        !ch.is_whitespace()
            && !matches!(
                ch,
                '(' | ')' | '[' | ']' | '{' | '}' | '\\' | ',' | ';' | '"' | '\''
            )
    })
    .many1_skip();
    let ((), text) = i.run(parser.with_seq())?;
    let trailing = i.run(scan_trivia)?;
    Some(Lex::new(
        leading_info,
        SyntaxKind::OpName,
        text.as_ref(),
        trailing,
    ))
}

/// `5.0.0` 形式の bp_vec をスキャン
fn scan_bp_vec<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Lex> {
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return None;
    }
    let digits = ascii_digit.many1_skip();
    let parser = digits.left((item('.'), ascii_digit.many1_skip()).many_skip());
    let ((), text) = i.run(parser.with_seq())?;
    let trailing = i.run(scan_trivia)?;
    Some(Lex::new(
        leading_info,
        SyntaxKind::Number,
        text.as_ref(),
        trailing,
    ))
}
