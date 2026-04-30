use chasa::prelude::*;
use unicode_ident::{is_xid_continue, is_xid_start};

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, Token, TriviaInfo};
use crate::scan::trivia::scan_trivia;
use crate::sink::EventSink;

/// use 文専用のトークンタグ
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UseTag {
    /// 識別子・パスセグメント
    Ident,
    /// `*` グロブ
    Glob,
    /// `::`
    ColonColon,
    /// `/`
    Slash,
    /// `,`
    Comma,
    /// `{`
    BraceL,
    /// `}`
    BraceR,
    /// `(`
    ParenL,
    /// `)`
    ParenR,
    /// parenthesized operator name
    Op,
    /// `as` キーワード
    As,
    /// `without` キーワード
    Without,
    /// 停止トークン（それ以外）
    Stop,
}

/// use 文の単一トークンをスキャンする
///
/// trivia（空白・コメント）を読み飛ばし、次のトークンとそのタグを返す。
/// ただし改行や EOF を検出したときは `None` を返す。
pub fn scan_use_tok<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Token<UseTag>> {
    // 改行や EOF は停止（None）
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return None;
    }

    let parser = choice((
        tag("::").to(SyntaxKind::ColonColon),
        item('*').to(SyntaxKind::OpName),
        item('/').to(SyntaxKind::Slash),
        item(',').to(SyntaxKind::Comma),
        item('{').to(SyntaxKind::BraceL),
        item('}').to(SyntaxKind::BraceR),
        item(';').to(SyntaxKind::Semicolon),
        item('(').to(SyntaxKind::ParenL),
        item(')').to(SyntaxKind::ParenR),
        item('[').to(SyntaxKind::BracketL),
        item(']').to(SyntaxKind::BracketR),
    ));

    if let Some((kind, text)) = i.run(parser.with_seq()) {
        let tag = match kind {
            SyntaxKind::ColonColon => UseTag::ColonColon,
            SyntaxKind::OpName => UseTag::Glob,
            SyntaxKind::Slash => UseTag::Slash,
            SyntaxKind::Comma => UseTag::Comma,
            SyntaxKind::BraceL => UseTag::BraceL,
            SyntaxKind::BraceR => UseTag::BraceR,
            SyntaxKind::ParenL => UseTag::ParenL,
            SyntaxKind::ParenR => UseTag::ParenR,
            _ => UseTag::Stop,
        };
        let trailing_trivia = i.run(scan_trivia)?;
        let lex = Lex::new(leading_info, kind, text.as_ref(), trailing_trivia);
        return Some(lex.tag(tag));
    }

    // 識別子を試みる
    if let Some(((), text)) = i.run(use_ident_chars.with_seq()) {
        let s: Box<str> = text.as_ref().into();
        let (tag, kind) = match s.as_ref() {
            "as" => (UseTag::As, SyntaxKind::As),
            "without" => (UseTag::Without, SyntaxKind::Ident),
            _ => (UseTag::Ident, SyntaxKind::Ident),
        };
        let trailing_trivia = i.run(scan_trivia)?;
        let lex = Lex::new(leading_info, kind, s, trailing_trivia);
        return Some(lex.tag(tag));
    }

    if let Some(((), text)) = i.run(use_op_name_chars.with_seq()) {
        let trailing_trivia = i.run(scan_trivia)?;
        let lex = Lex::new(
            leading_info,
            SyntaxKind::OpName,
            text.as_ref(),
            trailing_trivia,
        );
        return Some(lex.tag(UseTag::Op));
    }

    // その他（予期しない文字）は Stop
    if let Some((_, text)) = i.run(one_of(|_: char| true).with_seq()) {
        let trailing_trivia = i.run(scan_trivia)?;
        let lex = Lex::new(
            leading_info,
            SyntaxKind::Unknown,
            text.as_ref(),
            trailing_trivia,
        );
        return Some(lex.tag(UseTag::Stop));
    }

    None
}

/// 識別子文字列をスキャン
fn use_ident_chars<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    i.choice((one_of(is_xid_start).skip(), item('_').skip()))?;
    i.many_skip(one_of(is_xid_continue))?;
    i.skip(one_of("?!").or_not())
}

fn use_op_name_chars<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    i.many1_skip(one_of(|c: char| {
        !c.is_whitespace()
            && !matches!(c, ':' | '(' | ')' | '{' | '}' | '[' | ']' | ',' | ';' | '/')
    }))
}
