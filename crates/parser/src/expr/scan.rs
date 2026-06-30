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
    scan_doc_comment_token, scan_dot_field, scan_expr_led_word, scan_expr_nud_word, scan_number,
    scan_projection_dot, scan_punct_expr, scan_sigil_ident, scan_stmt_head_word, scan_symbol,
    scan_unknown,
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
    Field,
    ProjectionDot,
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
    i: In<I, S>,
) -> Option<Token<ExprNudTag>> {
    scan_expr_nud_with_words(leading_info, i, ExprWordMode::Expr)
}

pub fn scan_stmt_head_nud<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    i: In<I, S>,
) -> Option<Token<ExprNudTag>> {
    scan_expr_nud_with_words(leading_info, i, ExprWordMode::StmtHead)
}

#[derive(Debug, Clone, Copy)]
enum ExprWordMode {
    Expr,
    StmtHead,
}

fn scan_expr_nud_with_words<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
    word_mode: ExprWordMode,
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
        let word_stop = stop.clone();
        let (tag, (kind, text)) = i.choice((
            (value(ExprNudTag::Atom), scan_sigil_ident),
            (value(ExprNudTag::Atom), scan_number),
            from_fn(move |i| scan_nud_word(word_mode, i, &word_stop)).map(read_expr_nud_word),
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
    let yada_yada_parser = from_fn(|mut i: In<I, S>| {
        let (kind, text) = scan_punct_expr(i.rb())?;
        (kind == SyntaxKind::YadaYada).then_some(())?;
        let trailing_trivia = i.run(scan_trivia)?;
        Some(Lex::new(leading_info, kind, text, trailing_trivia).tag(ExprNudTag::Nullfix))
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
        yada_yada_parser,
        op_parser,
        rule_lit_parser,
        string_parser,
        prim_parser,
    ))
}

fn scan_nud_word<I: EventInput, S: EventSink>(
    mode: ExprWordMode,
    i: In<I, S>,
    stop: &im::HashSet<SyntaxKind>,
) -> Option<(SyntaxKind, Box<str>)> {
    match mode {
        ExprWordMode::Expr => scan_expr_nud_word(i, stop),
        ExprWordMode::StmtHead => scan_stmt_head_word(i),
    }
}

fn read_expr_nud_word(
    (kind, text): (SyntaxKind, Box<str>),
) -> (ExprNudTag, (SyntaxKind, Box<str>)) {
    let tag = match kind {
        SyntaxKind::Ident
        | SyntaxKind::Do
        | SyntaxKind::Case
        | SyntaxKind::If
        | SyntaxKind::Catch
        | SyntaxKind::Sub
        | SyntaxKind::Rule => ExprNudTag::Atom,
        _ => ExprNudTag::Stop,
    };
    (tag, (kind, text))
}

fn read_expr_nud_punct(kind: SyntaxKind, stop: im::HashSet<SyntaxKind>) -> ExprNudTag {
    match kind {
        kind if stop.contains(&kind) => ExprNudTag::Stop,
        SyntaxKind::YadaYada => ExprNudTag::Nullfix,
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
        let word_stop = stop.clone();
        let (tag, (kind, text)) = i.choice((
            (value(ExprLedTag::ProjectionDot), scan_projection_dot),
            (value(ExprLedTag::Field), scan_dot_field),
            from_fn(|i| scan_symbol(leading_info, false, i))
                .map(|(kind, text)| (ExprLedTag::MlNud(ExprNudTag::Atom), (kind, text))),
            from_fn(|mut i| {
                let item = scan_sigil_ident(i.rb())?;
                Some((ExprLedTag::MlNud(ExprNudTag::Atom), item))
            }),
            from_fn(|mut i| {
                let item = scan_number(i.rb())?;
                Some((ExprLedTag::MlNud(ExprNudTag::Atom), item))
            }),
            from_fn(|mut i| {
                let (kind, text) = scan_expr_led_word(i.rb(), &word_stop)?;
                let tag = match kind {
                    SyntaxKind::Ident | SyntaxKind::Do => ExprLedTag::MlNud(ExprNudTag::Atom),
                    SyntaxKind::As => ExprLedTag::As,
                    SyntaxKind::With => ExprLedTag::With,
                    _ => ExprLedTag::Stop,
                };
                Some((tag, (kind, text)))
            }),
            from_fn(|mut i| {
                let (kind, text) = scan_punct_expr(i.rb())?;
                let tag = match kind {
                    kind if stop.contains(&kind) => ExprLedTag::Stop,
                    SyntaxKind::ColonColon => ExprLedTag::PathSep,
                    SyntaxKind::Colon => ExprLedTag::Colon,
                    SyntaxKind::Equal => ExprLedTag::Assign,
                    SyntaxKind::ParenL if matches!(leading_info, TriviaInfo::None) => {
                        ExprLedTag::CallStart
                    }
                    SyntaxKind::BracketL if matches!(leading_info, TriviaInfo::None) => {
                        ExprLedTag::IndexStart
                    }
                    kind => match read_expr_nud_punct(kind, stop.clone()) {
                        ExprNudTag::Stop => ExprLedTag::Stop,
                        tag => ExprLedTag::MlNud(tag),
                    },
                };
                Some((tag, (kind, text)))
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

pub(crate) fn scan_expr_spread_dotdot<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Lex> {
    let (_, text) = i.with_seq(tag(".."))?;
    i.not(item('<'))?;
    let trailing = i.run(scan_trivia)?;
    Some(Lex::new(
        leading_info,
        SyntaxKind::DotDot,
        text.as_ref(),
        trailing,
    ))
}
