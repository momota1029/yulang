use chasa::prelude::*;
use reborrow_generic::Reborrow as _;
use unicode_ident::is_xid_continue;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, Token, Trivia, TriviaInfo};
use crate::scan::trivia::scan_trivia;
use crate::scan::{scan_dot_field, scan_number, scan_punct_expr, scan_sigil_ident, scan_unknown};
use crate::sink::EventSink;
use crate::string::scan::scan_string_start;

// ─────────────────────────────────────────────
// ヘルパー
// ─────────────────────────────────────────────

fn rule_lex(kind: SyntaxKind, text: impl Into<Box<str>>) -> Lex {
    Lex::new(TriviaInfo::None, kind, text, Trivia::empty())
}

// ─────────────────────────────────────────────
// ~"..." リテラルスキャン
// ─────────────────────────────────────────────

/// `~"` を2文字まとめてスキャンして `RuleLitStart` トークンを返す。
pub fn scan_rule_lit_start<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Lex> {
    let (_, text) = i.run(tag("~\"").with_seq())?;
    Some(Lex::new(
        leading_info,
        SyntaxKind::RuleLitStart,
        text.as_ref(),
        Trivia::empty(),
    ))
}

/// `"` を読んで `RuleLitEnd` を返す。
fn scan_rule_lit_end<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Lex> {
    let (_, text) = i.run(item('"').with_seq())?;
    let trailing = i.run(scan_trivia)?;
    Some(Lex::new(
        TriviaInfo::None,
        SyntaxKind::RuleLitEnd,
        text.as_ref(),
        trailing,
    ))
}

// ─────────────────────────────────────────────
// ~"..." 内部トークン
// ─────────────────────────────────────────────

/// `~"..."` の中のプレーンテキスト部分（`"`, `{`, `:` 以外）
fn scan_rule_lit_text<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Lex> {
    let (_, text) = i.run(none_of("\"{:").many1_skip().with_seq())?;
    Some(rule_lex(SyntaxKind::RuleLitText, text.as_ref()))
}

/// `{` を読んで `RuleLitOpenBrace` を返す
pub fn scan_rule_lit_open_brace<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Lex> {
    let (_, text) = i.run(item('{').with_seq())?;
    Some(rule_lex(SyntaxKind::RuleLitOpenBrace, text.as_ref()))
}

/// `}` を読んで `RuleLitCloseBrace` を返す
pub fn scan_rule_lit_close_brace<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Lex> {
    let (_, text) = i.run(item('}').with_seq())?;
    Some(rule_lex(SyntaxKind::RuleLitCloseBrace, text.as_ref()))
}

/// `:` を読んで `RuleLitColon` を返す（`:name` lazy capture の開始）
fn scan_rule_lit_colon<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Lex> {
    let (_, text) = i.run(item(':').with_seq())?;
    Some(rule_lex(SyntaxKind::RuleLitColon, text.as_ref()))
}

/// `~"..."` 内の次のトークンを表す型
#[derive(Debug, Clone)]
pub enum RuleLitTok {
    /// `"` — リテラル終端
    End(Lex),
    /// `{` — パーサー参照またはキャプチャ式の開始
    InterpOpen(Lex),
    /// `:` — lazy capture の開始
    LazyCapture(Lex),
    /// プレーンテキスト
    Tok(Lex),
}

/// `~"..."` 内の次のトークンをスキャンする。
pub fn scan_rule_lit_token<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<RuleLitTok> {
    i.choice((
        from_fn_once(|i| scan_rule_lit_end(i).map(RuleLitTok::End)),
        from_fn_once(|i| scan_rule_lit_open_brace(i).map(RuleLitTok::InterpOpen)),
        from_fn_once(|i| scan_rule_lit_colon(i).map(RuleLitTok::LazyCapture)),
        from_fn_once(|i| scan_rule_lit_text(i).map(RuleLitTok::Tok)),
        // フォールバック: 1文字ずつ消費
        from_fn_once(|mut i: In<I, S>| {
            let (_, text) = i.run(any.with_seq())?;
            Some(RuleLitTok::Tok(rule_lex(
                SyntaxKind::RuleLitText,
                text.as_ref(),
            )))
        }),
    ))
}

/// `{...}` 内の名前部分をスキャン（`=` または `}` まで）
pub fn scan_rule_lit_interp_name<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Lex> {
    let (_, text) = i.run(none_of("=}").many1_skip().with_seq())?;
    Some(rule_lex(SyntaxKind::RuleLitText, text.as_ref()))
}

/// `:name` の名前部分をスキャン（XID 継続文字のみ）
pub fn scan_rule_lit_lazy_name<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Lex> {
    let (_, text) = i.run(one_of(is_xid_continue).many1_skip().with_seq())?;
    Some(rule_lex(SyntaxKind::RuleLitText, text.as_ref()))
}

// ─────────────────────────────────────────────
// rule { } ボディ用識別子スキャナ
// ─────────────────────────────────────────────

/// ルールボディ用の識別子スキャナ。
///
/// 通常の識別子と異なり、末尾の `?` と `!` を含めない。
/// `?` は量化子として使うため。
fn scan_rule_ident_or_keyword<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
) -> Option<(SyntaxKind, Box<str>)> {
    use unicode_ident::is_xid_start;
    let ident_no_suffix = from_fn(|mut i: In<I, S>| {
        i.choice((one_of(is_xid_start).skip(), item('_').skip()))?;
        i.many_skip(one_of(is_xid_continue))?;
        Some(())
    });
    let ((), text) = i.run(ident_no_suffix.with_seq())?;
    let kind = rule_keyword_kind(text.as_ref()).unwrap_or(SyntaxKind::Ident);
    Some((kind, text.as_ref().into()))
}

fn rule_keyword_kind(text: &str) -> Option<SyntaxKind> {
    match text {
        "do" => Some(SyntaxKind::Do),
        "if" => Some(SyntaxKind::If),
        "else" => Some(SyntaxKind::Else),
        "case" => Some(SyntaxKind::Case),
        "catch" => Some(SyntaxKind::Catch),
        "rule" => Some(SyntaxKind::Rule),
        _ => None,
    }
}

// ─────────────────────────────────────────────
// rule { } ボディスキャナ
// ─────────────────────────────────────────────

/// ルールボディ内のNUDタグ
#[derive(Debug, Clone)]
pub enum RuleNudTag {
    Atom,
    StringStart,
    OpenParen,
    OpenBracket,
    Stop,
}

/// ルールボディ内のLEDタグ
#[derive(Debug, Clone)]
pub enum RuleLedTag {
    /// `=` — キャプチャバインディング
    Equal,
    /// `*`, `+`, `?`, `*?`, `+?` — 量化子（接尾辞）
    Quant,
    /// `.field` — フィールドアクセス
    Field,
    /// `::` — パスセパレータ
    PathSep,
    /// `(` — C式呼び出し（スペースなし）
    CallStart,
    /// `[` — インデックス（スペースなし）
    IndexStart,
}

/// ルールボディ用NUDスキャナ。
///
/// 式のNUDスキャナとは異なり、ユーザー定義演算子やlambdaを認識しない。
/// 認識するもの: ident, number, sigil_ident, string, `(`, `[`, punct(Stop)
pub fn scan_rule_body_nud<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Token<RuleNudTag>> {
    let string_parser = from_fn(|mut i: In<I, S>| {
        let lex = scan_string_start(leading_info, i.rb())?;
        Some(lex.tag(RuleNudTag::StringStart))
    });
    let prim_parser = from_fn(|mut i: In<I, S>| {
        let (tag, (kind, text)) = i.choice((
            (value(RuleNudTag::Atom), scan_sigil_ident),
            (value(RuleNudTag::Atom), scan_number),
            scan_rule_ident_or_keyword.map(|(kind, text)| match kind {
                SyntaxKind::Ident => (RuleNudTag::Atom, (kind, text)),
                _ => (RuleNudTag::Stop, (kind, text)),
            }),
            scan_punct_expr.map(|(kind, text)| {
                let tag = match kind {
                    SyntaxKind::ParenL => RuleNudTag::OpenParen,
                    SyntaxKind::BracketL => RuleNudTag::OpenBracket,
                    _ => RuleNudTag::Stop,
                };
                (tag, (kind, text))
            }),
            (value(RuleNudTag::Stop), scan_unknown),
        ))?;
        let trailing_trivia = i.run(scan_trivia)?;
        Some(Lex::new(leading_info, kind, text, trailing_trivia).tag(tag))
    });
    i.choice((string_parser, prim_parser))
}

/// ルールボディ用LEDスキャナ。
///
/// スペースなし（`leading_info == None`）の場合: 量化子, `=`, `.field`, `::`, `(`, `[`
/// スペースあり（`leading_info == Space`）の場合: `=` のみ
/// 改行の場合: None（LEDなし）
///
/// **ユーザー定義演算子は認識しない。** ML-applyも発生しない。
pub fn scan_rule_body_led<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Token<RuleLedTag>> {
    // 改行 → LEDなし
    if matches!(leading_info, TriviaInfo::Newline { .. }) {
        return None;
    }

    let has_space = leading_info != TriviaInfo::None;

    // スペースあり → `=` のみ
    if has_space {
        let (kind, text) = i.run(item('=').to(SyntaxKind::Equal).with_seq())?;
        let trailing = i.run(scan_trivia)?;
        let lex = Lex::new(leading_info, kind, text.as_ref(), trailing);
        return Some(lex.tag(RuleLedTag::Equal));
    }

    // スペースなし → 全LED
    i.choice((
        // 量化子（`*?`, `+?`, `*`, `+`, `?`）
        from_fn(|i| scan_rule_quant(leading_info, i).map(|lex| lex.tag(RuleLedTag::Quant))),
        // `.field`
        from_fn(|mut i: In<I, S>| {
            let (kind, text) = scan_dot_field(i.rb())?;
            let trailing = i.run(scan_trivia)?;
            Some(Lex::new(leading_info, kind, text, trailing).tag(RuleLedTag::Field))
        }),
        // `=`
        from_fn(|mut i: In<I, S>| {
            let (kind, text) = i.run(item('=').to(SyntaxKind::Equal).with_seq())?;
            let trailing = i.run(scan_trivia)?;
            Some(Lex::new(leading_info, kind, text.as_ref(), trailing).tag(RuleLedTag::Equal))
        }),
        // `::`
        from_fn(|mut i: In<I, S>| {
            let (kind, text) = i.run(tag("::").to(SyntaxKind::ColonColon).with_seq())?;
            let trailing = i.run(scan_trivia)?;
            Some(Lex::new(leading_info, kind, text.as_ref(), trailing).tag(RuleLedTag::PathSep))
        }),
        // `(` — C式呼び出し
        from_fn(|mut i: In<I, S>| {
            let (_, text) = i.run(item('(').with_seq())?;
            Some(
                Lex::new(
                    leading_info,
                    SyntaxKind::ParenL,
                    text.as_ref(),
                    Trivia::empty(),
                )
                .tag(RuleLedTag::CallStart),
            )
        }),
        // `[` — インデックス
        from_fn(|mut i: In<I, S>| {
            let (_, text) = i.run(item('[').with_seq())?;
            Some(
                Lex::new(
                    leading_info,
                    SyntaxKind::BracketL,
                    text.as_ref(),
                    Trivia::empty(),
                )
                .tag(RuleLedTag::IndexStart),
            )
        }),
    ))
}

// ─────────────────────────────────────────────
// rule { } ボディ量化子スキャン
// ─────────────────────────────────────────────

/// `rule { }` ボディ内の量化子トークンをスキャンする。
/// - `*?` → `RuleQuantStarLazy`
/// - `+?` → `RuleQuantPlusLazy`
/// - `*`  → `RuleQuantStar`
/// - `+`  → `RuleQuantPlus`
/// - `?`  → `RuleQuantOpt`
pub fn scan_rule_quant<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Lex> {
    let parser = choice((
        tag("*?").to(SyntaxKind::RuleQuantStarLazy),
        tag("+?").to(SyntaxKind::RuleQuantPlusLazy),
        item('*').to(SyntaxKind::RuleQuantStar),
        item('+').to(SyntaxKind::RuleQuantPlus),
        item('?').to(SyntaxKind::RuleQuantOpt),
    ));
    let (kind, text) = i.run(parser.with_seq())?;
    let trailing = i.run(scan_trivia)?;
    Some(Lex::new(leading_info, kind, text.as_ref(), trailing))
}
