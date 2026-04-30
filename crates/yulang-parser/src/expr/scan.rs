use chasa::prelude::*;
use reborrow_generic::Reborrow as _;

pub mod op;
pub mod rule;

use crate::EventInput;
use crate::context::In;
use crate::expr::scan::rule::scan_rule_lit_start;
use crate::lex::{Lex, SyntaxKind, Token, Trivia, TriviaInfo};
use crate::op::{BpVec, OpUse};
use crate::scan::trivia::scan_trivia;
use crate::scan::{
    scan_doc_comment_token, scan_dot_field, scan_ident_or_keyword, scan_number, scan_punct_expr,
    scan_sigil_ident, scan_symbol, scan_unknown,
};
use crate::sink::EventSink;
use crate::string::scan::scan_string_start;

#[derive(Debug, Clone)]
pub enum ExprNudTag {
    Atom,
    StringStart,
    RuleLitStart,
    Nullfix,
    OpenParen,
    OpenBracket,
    OpenBrace,
    Backslash,
    Apostrophe,
    Prefix(BpVec),
    Stop,
}

#[derive(Debug, Clone)]
pub enum ExprLedTag {
    Infix(BpVec, BpVec),
    Suffix(BpVec),
    Pipe,
    Field,
    As,
    With,
    MlNud(ExprNudTag),
    CallStart,
    IndexStart,
    Colon,
    Assign,
    PathSep,
    Stop,
}

pub fn scan_expr_nud<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Token<ExprNudTag>> {
    let fence_stop = from_fn(|mut i: In<I, S>| {
        if !i.env.stop.contains(&SyntaxKind::YmFenceSigil) {
            return None;
        }
        if !matches!(leading_info, TriviaInfo::None | TriviaInfo::Newline { .. }) {
            return None;
        }
        let (_, text) = i.with_seq(tag("```"))?;
        Some(
            Lex::new(
                leading_info,
                SyntaxKind::YmFenceSigil,
                text.as_ref(),
                Trivia::empty(),
            )
            .tag(ExprNudTag::Stop),
        )
    });
    let prim_parser = from_fn(|mut i: In<I, S>| {
        let stop = i.env.stop.clone();
        let (tag, (kind, text)) = i.choice((
            (value(ExprNudTag::Atom), scan_sigil_ident),
            (value(ExprNudTag::Atom), scan_number),
            scan_ident_or_keyword.map(|(kind, text)| match kind {
                SyntaxKind::Ident
                | SyntaxKind::Do
                | SyntaxKind::Case
                | SyntaxKind::If
                | SyntaxKind::Catch
                | SyntaxKind::Rule => (ExprNudTag::Atom, (kind, text)),
                _ => (ExprNudTag::Stop, (kind, text)),
            }),
            from_fn(|i| scan_symbol(leading_info, true, i))
                .map(|(kind, text)| (ExprNudTag::Atom, (kind, text))),
            scan_punct_expr
                .map_once(move |(kind, text)| (read_expr_nud_punct(kind, stop), (kind, text))),
            (value(ExprNudTag::Stop), scan_unknown),
        ))?;
        let trailing_trivia = i.run(scan_trivia)?;
        Some(Lex::new(leading_info, kind, text, trailing_trivia).tag(tag))
    });
    let op_parser = from_fn(|mut i: In<I, S>| {
        let (use_, def, lex) = op::scan::scan_op_nud(i.rb(), leading_info)?;
        let tag = match use_ {
            OpUse::Prefix => ExprNudTag::Prefix(def.prefix?),
            OpUse::Nullfix => ExprNudTag::Nullfix,
            OpUse::Infix | OpUse::Suffix => return None,
        };
        Some(lex.tag(tag))
    });
    let string_parser = from_fn(|mut i: In<I, S>| {
        let lex = scan_string_start(leading_info, i.rb())?;
        Some(lex.tag(ExprNudTag::StringStart))
    });
    let rule_lit_parser = from_fn(|mut i: In<I, S>| {
        let lex = scan_rule_lit_start(leading_info, i.rb())?;
        Some(lex.tag(ExprNudTag::RuleLitStart))
    });
    let doc_comment_nud = from_fn(|mut i: In<I, S>| {
        let (kind, text) = scan_doc_comment_token(i.rb())?;
        // trailing trivia は空にして本文を parse_ym_doc(DocLine) に委ねる
        Some(Lex::new(leading_info, kind, text, Trivia::empty()).tag(ExprNudTag::Stop))
    });
    i.choice((
        fence_stop,
        doc_comment_nud,
        op_parser,
        rule_lit_parser,
        string_parser,
        prim_parser,
    ))
}
fn read_expr_nud_punct(kind: SyntaxKind, stop: im::HashSet<SyntaxKind>) -> ExprNudTag {
    match kind {
        kind if stop.contains(&kind) => ExprNudTag::Stop,
        SyntaxKind::ParenL => ExprNudTag::OpenParen,
        SyntaxKind::BracketL => ExprNudTag::OpenBracket,
        SyntaxKind::BraceL => ExprNudTag::OpenBrace,
        SyntaxKind::Backslash => ExprNudTag::Backslash,
        SyntaxKind::Apostrophe => ExprNudTag::Apostrophe,
        _ => ExprNudTag::Stop,
    }
}

pub fn scan_expr_led<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Token<ExprLedTag>> {
    let fence_stop = from_fn(|mut i: In<I, S>| {
        if !i.env.stop.contains(&SyntaxKind::YmFenceSigil) {
            return None;
        }
        if !matches!(leading_info, TriviaInfo::None | TriviaInfo::Newline { .. }) {
            return None;
        }
        let (_, text) = i.with_seq(tag("```"))?;
        Some(
            Lex::new(
                leading_info,
                SyntaxKind::YmFenceSigil,
                text.as_ref(),
                Trivia::empty(),
            )
            .tag(ExprLedTag::Stop),
        )
    });
    let prim_parser = from_fn(|mut i: In<I, S>| {
        let stop = i.env.stop.clone();
        let (tag, (kind, text)) = i.choice((
            (value(ExprLedTag::Field), scan_dot_field),
            from_fn(|i| scan_symbol(leading_info, false, i))
                .map(|(kind, text)| (ExprLedTag::MlNud(ExprNudTag::Atom), (kind, text))),
            (value(ExprLedTag::MlNud(ExprNudTag::Atom)), scan_sigil_ident),
            (value(ExprLedTag::MlNud(ExprNudTag::Atom)), scan_number),
            scan_ident_or_keyword.map(|(kind, text)| match kind {
                SyntaxKind::Ident | SyntaxKind::Do => {
                    (ExprLedTag::MlNud(ExprNudTag::Atom), (kind, text))
                }
                SyntaxKind::As => (ExprLedTag::As, (kind, text)),
                SyntaxKind::With => (ExprLedTag::With, (kind, text)),
                _ => (ExprLedTag::Stop, (kind, text)),
            }),
            scan_punct_expr.map_once(move |(kind, text)| match kind {
                kind if stop.contains(&kind) => (ExprLedTag::Stop, (kind, text)),
                SyntaxKind::ColonColon => (ExprLedTag::PathSep, (kind, text)),
                SyntaxKind::Colon => (ExprLedTag::Colon, (kind, text)),
                SyntaxKind::Equal => (ExprLedTag::Assign, (kind, text)),
                SyntaxKind::Pipe => (ExprLedTag::Pipe, (kind, text)),
                SyntaxKind::ParenL if matches!(leading_info, TriviaInfo::None) => {
                    (ExprLedTag::CallStart, (kind, text))
                }
                SyntaxKind::BracketL if matches!(leading_info, TriviaInfo::None) => {
                    (ExprLedTag::IndexStart, (kind, text))
                }
                kind => match read_expr_nud_punct(kind, stop) {
                    ExprNudTag::Stop => (ExprLedTag::Stop, (kind, text)),
                    tag => (ExprLedTag::MlNud(tag), (kind, text)),
                },
            }),
            (value(ExprLedTag::Stop), scan_unknown),
        ))?;
        let trailing_trivia = i.run(scan_trivia)?;
        Some(Lex::new(leading_info, kind, text, trailing_trivia).tag(tag))
    });
    let op_parser = from_fn(|mut i: In<I, S>| {
        let (use_, def, lex) = op::scan::scan_op_led(i.rb(), leading_info)?;
        let tag = match use_ {
            OpUse::Prefix => ExprLedTag::MlNud(ExprNudTag::Prefix(def.prefix?)),
            OpUse::Nullfix => ExprLedTag::MlNud(ExprNudTag::Nullfix),
            OpUse::Infix => {
                let (lbp, rbp) = def.infix?;
                ExprLedTag::Infix(lbp, rbp)
            }
            OpUse::Suffix => ExprLedTag::Suffix(def.suffix?),
        };
        Some(lex.tag(tag))
    });
    let string_parser = from_fn(|mut i: In<I, S>| {
        let lex = scan_string_start(leading_info, i.rb())?;
        Some(lex.tag(ExprLedTag::MlNud(ExprNudTag::StringStart)))
    });
    let rule_lit_parser = from_fn(|mut i: In<I, S>| {
        let lex = scan_rule_lit_start(leading_info, i.rb())?;
        Some(lex.tag(ExprLedTag::MlNud(ExprNudTag::RuleLitStart)))
    });
    let doc_comment_led = from_fn(|mut i: In<I, S>| {
        let (kind, text) = scan_doc_comment_token(i.rb())?;
        // trailing trivia は空にして本文を parse_ym_doc(DocLine) に委ねる
        Some(Lex::new(leading_info, kind, text, Trivia::empty()).tag(ExprLedTag::Stop))
    });
    i.choice((
        fence_stop,
        doc_comment_led,
        op_parser,
        rule_lit_parser,
        string_parser,
        prim_parser,
    ))
}
