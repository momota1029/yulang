use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::expr::scan::rule::{
    RuleLedTag, RuleLitTok, RuleNudTag, scan_rule_body_led, scan_rule_body_nud,
    scan_rule_lit_close_brace, scan_rule_lit_interp_name, scan_rule_lit_lazy_name,
    scan_rule_lit_open_brace, scan_rule_lit_token,
};
use crate::expr::scan::scan_expr_nud;
use crate::lex::{Lex, SyntaxKind, TriviaInfo};
use crate::parse::DelimitedListMachine;
use crate::sink::EventSink;

use super::group::{delimited, parse_call_group};
use super::string::parse_string_lit;

// ─────────────────────────────────────────────
// rule { body } 式
// ─────────────────────────────────────────────

/// `rule { body }` 式をパースする。
///
/// `rule_lex` は既にスキャンされた `Rule` キーワードトークン。
/// 戻り値は `}` 後の trivia 情報。
/// 呼び出し側は既に `Expr` ノードを `start` している。
pub(crate) fn parse_rule_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    rule_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::RuleExpr);
    i.env.state.sink.lex(&rule_lex);

    let after_rule = rule_lex.trailing_trivia_info();

    // 次のトークンは `{` を期待
    let brace_nud = scan_expr_nud(after_rule, i.rb())?;
    let after = match brace_nud.lex.kind {
        SyntaxKind::BraceL => {
            // `rule { body }` — ルールボディ専用パーサーで解析
            parse_rule_body(i.rb(), brace_nud.lex)?
        }
        _ => {
            // `{` が来なかった: エラー回復
            i.env.state.sink.lex(&brace_nud.lex);
            brace_nud.lex.trailing_trivia_info()
        }
    };

    i.env.state.sink.finish(); // RuleExpr
    Some(after)
}

/// `rule { }` のボディを `|` 区切りの alternation としてパースする。
///
/// `open_lex` は `{` トークン。
fn parse_rule_body<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::BraceGroup);
    let mut machine = RuleBodyMachine;
    let result = machine.parse_delimited_list(i.rb(), open_lex)?;
    i.env.state.sink.finish();
    Some(result)
}

struct RuleBodyMachine;

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for RuleBodyMachine {
    fn end_kind(&self) -> SyntaxKind {
        SyntaxKind::BraceR
    }

    fn is_group_sep(&self, kind: SyntaxKind) -> bool {
        kind == SyntaxKind::Pipe
    }

    fn is_implicit_separator(&self, info: TriviaInfo, _base_indent: usize) -> bool {
        // `{}` 内では改行があれば暗黙のセパレータ
        matches!(info, TriviaInfo::Newline { .. })
    }

    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        _base_indent: usize,
    ) -> Option<Either<TriviaInfo, Lex>> {
        parse_rule_seq(i, leading_info)
    }
}

// ─────────────────────────────────────────────
// ルールシーケンス（一つの alternation）
// ─────────────────────────────────────────────

/// alternation の一つのブランチ（アイテムの並び）をパースする。
///
/// スペース区切り = PEG シーケンス。ML-apply は発生しない。
/// `|` または `}` で停止してストップトークンを返す。
fn parse_rule_seq<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    mut leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    loop {
        match parse_rule_item(i.rb(), leading_info)? {
            Either::Left(trailing) => {
                match trailing {
                    TriviaInfo::None => {
                        // スペースなしで LED もなかった → 次のトークンはストップか次アイテム
                        // NUD スキャンで判定（次のループで Stop になる）
                        leading_info = trailing;
                    }
                    TriviaInfo::Space => {
                        // スペースあり → シーケンスの次アイテム
                        leading_info = trailing;
                    }
                    TriviaInfo::Newline { .. } => {
                        // 改行 → マシンに返して暗黙セパレータ判定
                        return Some(Either::Left(trailing));
                    }
                }
            }
            Either::Right(stop_lex) => {
                return Some(Either::Right(stop_lex));
            }
        }
    }
}

// ─────────────────────────────────────────────
// ルールアイテム（NUD + テール）
// ─────────────────────────────────────────────

/// ルールボディ内の一つのアイテムをパースする。
///
/// NUD（ident, string, number, `(`, etc.）をスキャンし、
/// テールループで `=`, 量化子, `.field`, `::`, `()`, `[]` を処理する。
fn parse_rule_item<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    leading_info: TriviaInfo,
) -> Option<Either<TriviaInfo, Lex>> {
    let nud = scan_rule_body_nud(leading_info, i.rb())?;
    match nud.tag {
        RuleNudTag::Stop => {
            return Some(Either::Right(nud.lex));
        }
        RuleNudTag::Atom => {
            i.env.state.sink.start(SyntaxKind::Expr);
            i.env.state.sink.lex(&nud.lex);
            let trailing = parse_rule_body_tail(nud.lex.trailing_trivia_info(), i.rb())?;
            i.env.state.sink.finish();
            Some(trailing)
        }
        RuleNudTag::StringStart => {
            i.env.state.sink.start(SyntaxKind::Expr);
            let after = parse_string_lit(i.rb(), nud.lex)?;
            i.env.state.sink.finish();
            Some(Either::Left(after))
        }
        RuleNudTag::OpenParen => {
            i.env.state.sink.start(SyntaxKind::Expr);
            let after = parse_rule_paren_group(i.rb(), nud.lex)?;
            let trailing = parse_rule_body_tail(after, i.rb())?;
            i.env.state.sink.finish();
            Some(trailing)
        }
        RuleNudTag::OpenBracket => {
            i.env.state.sink.start(SyntaxKind::Expr);
            let after = delimited(i.rb(), SyntaxKind::Bracket, SyntaxKind::BracketR, nud.lex)?;
            let trailing = parse_rule_body_tail(after, i.rb())?;
            i.env.state.sink.finish();
            Some(trailing)
        }
    }
}

/// `(...)` をルールボディグループとしてパースする（`|` が alternation セパレータ）。
fn parse_rule_paren_group<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    open_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::Paren);
    let mut machine = RuleParenMachine;
    let result = machine.parse_delimited_list(i.rb(), open_lex)?;
    i.env.state.sink.finish();
    Some(result)
}

struct RuleParenMachine;

impl<I: EventInput, S: EventSink> DelimitedListMachine<I, S> for RuleParenMachine {
    fn end_kind(&self) -> SyntaxKind {
        SyntaxKind::ParenR
    }

    fn is_group_sep(&self, kind: SyntaxKind) -> bool {
        kind == SyntaxKind::Pipe || kind == SyntaxKind::Comma
    }

    fn is_implicit_separator(&self, info: TriviaInfo, _base_indent: usize) -> bool {
        matches!(info, TriviaInfo::Newline { .. })
    }

    fn parse_item(
        &mut self,
        i: In<I, S>,
        leading_info: TriviaInfo,
        _base_indent: usize,
    ) -> Option<Either<TriviaInfo, Lex>> {
        parse_rule_seq(i, leading_info)
    }
}

// ─────────────────────────────────────────────
// ルールボディテールループ
// ─────────────────────────────────────────────

/// ルールボディ内のテールループ。
///
/// NUD の後に来る LED（`=`, 量化子, `.field`, `::`, `()`, `[]`）を処理する。
/// ML-apply は発生しない。スペース後は `=` のみ LED として認識。
fn parse_rule_body_tail<I: EventInput, S: EventSink>(
    mut leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Either<TriviaInfo, Lex>> {
    loop {
        let Some(led) = i.maybe_fn(|i| scan_rule_body_led(leading_info, i))? else {
            // LED が見つからない → アイテム終了
            return Some(Either::Left(leading_info));
        };
        match led.tag {
            RuleLedTag::Equal => {
                // `name = rhs` — キャプチャバインディング
                i.env.state.sink.start(SyntaxKind::RuleCapture);
                i.env.state.sink.lex(&led.lex);
                // RHS: 一つのルールアイテムをパース
                let rhs_result = parse_rule_item(i.rb(), led.lex.trailing_trivia_info())?;
                i.env.state.sink.finish(); // RuleCapture
                return Some(rhs_result);
            }
            RuleLedTag::Quant => {
                // `expr*`, `expr+`, `expr?`, `expr*?`, `expr+?`
                i.env.state.sink.start(SyntaxKind::RuleQuant);
                i.env.state.sink.lex(&led.lex);
                i.env.state.sink.finish();
                leading_info = led.lex.trailing_trivia_info();
            }
            RuleLedTag::Field => {
                // `expr.field`
                i.env.state.sink.start(SyntaxKind::Field);
                i.env.state.sink.lex(&led.lex);
                i.env.state.sink.finish();
                leading_info = led.lex.trailing_trivia_info();
            }
            RuleLedTag::PathSep => {
                // `expr::path`
                i.env.state.sink.start(SyntaxKind::PathSep);
                i.env.state.sink.lex(&led.lex);
                // `::` の後に ident を期待
                let rhs_nud = scan_rule_body_nud(led.lex.trailing_trivia_info(), i.rb())?;
                if matches!(rhs_nud.tag, RuleNudTag::Atom) && rhs_nud.lex.kind == SyntaxKind::Ident
                {
                    i.env.state.sink.lex(&rhs_nud.lex);
                } else {
                    i.env.state.sink.start(SyntaxKind::InvalidToken);
                    i.env.state.sink.lex(&rhs_nud.lex);
                    i.env.state.sink.finish();
                };
                i.env.state.sink.finish(); // PathSep
                leading_info = rhs_nud.lex.trailing_trivia_info();
            }
            RuleLedTag::CallStart => {
                // `expr(args)` — C式呼び出し（引数は通常のYulang式）
                i.env.state.sink.start(SyntaxKind::ApplyC);
                let next_info = parse_call_group(i.rb(), led.lex)?;
                i.env.state.sink.finish();
                leading_info = next_info;
            }
            RuleLedTag::IndexStart => {
                // `expr[index]` — インデックス
                i.env.state.sink.start(SyntaxKind::Index);
                let next_info =
                    delimited(i.rb(), SyntaxKind::Bracket, SyntaxKind::BracketR, led.lex)?;
                i.env.state.sink.finish();
                leading_info = next_info;
            }
        }
    }
}

// ─────────────────────────────────────────────
// ~"..." リテラル
// ─────────────────────────────────────────────

/// `~"..."` リテラルをパースする。
///
/// `start_lex` は既にスキャンされた `RuleLitStart` (`~"`) トークン。
/// 戻り値は `"` 後の trivia 情報。
/// 呼び出し側は既に `Expr` ノードを `start` している。
pub(crate) fn parse_rule_lit<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    start_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::RuleLit);
    i.env.state.sink.lex(&start_lex);

    loop {
        let Some(token) = scan_rule_lit_token(i.rb()) else {
            // EOF
            i.env.state.sink.finish(); // RuleLit
            return Some(TriviaInfo::None);
        };

        match token {
            RuleLitTok::End(lex) => {
                let after = lex.trailing_trivia_info();
                i.env.state.sink.lex(&lex);
                i.env.state.sink.finish(); // RuleLit
                return Some(after);
            }
            RuleLitTok::Tok(lex) => {
                i.env.state.sink.lex(&lex);
            }
            RuleLitTok::InterpOpen(open_lex) => {
                // `{...}` — ルールボディと同じ文法でパース
                parse_rule_lit_interp(i.rb(), open_lex);
            }
            RuleLitTok::LazyCapture(colon_lex) => {
                // `:name` または `:{name}` — lazy capture
                parse_rule_lit_lazy_capture(i.rb(), colon_lex);
            }
        }
    }
}

/// `{...}` をパースする（`{` は既にスキャン済み）。
///
/// ルールボディと同じ文法（PEGシーケンス、`=` キャプチャ）を使う。
/// `}` で終了。
fn parse_rule_lit_interp<I: EventInput, S: EventSink>(mut i: In<I, S>, open_lex: Lex) {
    i.env.state.sink.start(SyntaxKind::RuleLitInterp);
    i.env.state.sink.lex(&open_lex);

    // ルールシーケンスとしてパース（`}` で停止）
    let mut leading_info = TriviaInfo::None;
    loop {
        match parse_rule_item(i.rb(), leading_info) {
            Some(Either::Left(trailing)) => {
                match trailing {
                    TriviaInfo::None | TriviaInfo::Space => {
                        leading_info = trailing;
                        continue;
                    }
                    TriviaInfo::Newline { .. } => {
                        // ~"..." 内に改行は通常ないが、念のため
                        leading_info = trailing;
                        continue;
                    }
                }
            }
            Some(Either::Right(stop)) => {
                if stop.kind == SyntaxKind::BraceR || stop.kind == SyntaxKind::RuleLitCloseBrace {
                    // `}` を CloseBrace として再発行
                    let close_lex = Lex::new(
                        stop.leading_trivia_info,
                        SyntaxKind::RuleLitCloseBrace,
                        stop.text,
                        stop.trailing_trivia,
                    );
                    i.env.state.sink.lex(&close_lex);
                } else {
                    i.env.state.sink.start(SyntaxKind::InvalidToken);
                    i.env.state.sink.lex(&stop);
                    i.env.state.sink.finish();
                }
                break;
            }
            None => {
                // EOF — そのまま閉じる
                break;
            }
        }
    }

    i.env.state.sink.finish(); // RuleLitInterp
}

/// `:name` または `:{name}` lazy capture をパースする（`:` は既にスキャン済み）。
fn parse_rule_lit_lazy_capture<I: EventInput, S: EventSink>(mut i: In<I, S>, colon_lex: Lex) {
    i.env.state.sink.start(SyntaxKind::RuleLazyCapture);
    i.env.state.sink.lex(&colon_lex);

    // `:name` 形式を先に試す — XID 継続文字の有無で区別できる
    if let Some(name_lex) = scan_rule_lit_lazy_name(i.rb()) {
        // `:name` 形式
        i.env.state.sink.lex(&name_lex);
    } else if let Some(open) = scan_rule_lit_open_brace(i.rb()) {
        // `:{name}` 形式 — `{name}` を読む
        i.env.state.sink.lex(&open);
        if let Some(name_lex) = scan_rule_lit_interp_name(i.rb()) {
            i.env.state.sink.lex(&name_lex);
        }
        if let Some(close_lex) = scan_rule_lit_close_brace(i.rb()) {
            i.env.state.sink.lex(&close_lex);
        }
    }

    i.env.state.sink.finish(); // RuleLazyCapture
}
