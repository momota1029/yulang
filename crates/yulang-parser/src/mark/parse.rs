use chasa::prelude::{any, eoi, from_fn, item, tag};
use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{SyntaxKind, TriviaInfo, TriviaKind};
use crate::scan::trivia::scan_trivia;
use crate::sink::EventSink;

use super::scan::{BlockNudTag, InlineNudTag, Mark, MarkNudTag, scan_mark};

// ---------------------------------------------------------------------------
// Emit helpers
// ---------------------------------------------------------------------------

fn emit_text_trivia<I: EventInput, S: EventSink>(i: &mut In<I, S>, mark: &Mark) {
    if !mark.text.is_empty() {
        i.env.state.sink.push(SyntaxKind::YmText, &mark.text);
    }
    for part in mark.trivia.parts() {
        i.env.state.sink.push(part.kind.into(), &part.text);
    }
}

/// trivia のみ emit する。Space に `\n` が含まれる場合は YmNewline として出す。
fn emit_trivia_only<I: EventInput, S: EventSink>(i: &mut In<I, S>, mark: &Mark) {
    for part in mark.trivia.parts() {
        let kind: SyntaxKind = if part.kind == TriviaKind::Space && part.text.contains('\n') {
            SyntaxKind::YmNewline
        } else {
            part.kind.into()
        };
        i.env.state.sink.push(kind, &part.text);
    }
}

fn emit_nud_lex<I: EventInput, S: EventSink>(i: &mut In<I, S>, mark: &Mark) {
    if let Some(lex) = &mark.nud.lex {
        i.env.state.sink.push(lex.kind, &lex.text);
    }
}

fn emit_mark<I: EventInput, S: EventSink>(i: &mut In<I, S>, mark: &Mark) {
    emit_text_trivia(i, mark);
    emit_nud_lex(i, mark);
}

/// `]` の後に `(url)` が続く場合、YmLinkDest ノードを emit する。
fn parse_bracket_led<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<()> {
    let Some(_) = i.maybe(item('('))? else {
        return Some(());
    };
    i.env.state.sink.start(SyntaxKind::YmLinkDest);
    i.env.state.sink.push(SyntaxKind::ParenL, "(");
    let (_, text) = i.with_seq(from_fn(|mut j: In<I, S>| {
        loop {
            if j.lookahead(item(')')).is_some() {
                break;
            }
            if j.maybe(eoi)?.is_some() {
                break;
            }
            j.skip(any)?;
        }
        Some(())
    }))?;
    if !text.as_ref().is_empty() {
        i.env.state.sink.push(SyntaxKind::YmText, text.as_ref());
    }
    if i.maybe(item(')'))?.is_some() {
        i.env.state.sink.push(SyntaxKind::ParenR, ")");
    }
    i.env.state.sink.finish(); // YmLinkDest
    Some(())
}

fn is_terminal(mark: &Mark) -> bool {
    matches!(
        mark.nud.tag,
        MarkNudTag::Block(
            BlockNudTag::InputEnd | BlockNudTag::Dequote { .. } | BlockNudTag::DocBlockClose
        )
    )
}

// ---------------------------------------------------------------------------
// parse_inline
// ---------------------------------------------------------------------------

/// インラインコンテンツを parse する。Block nud または closing nud で停止し、
/// その Mark を返す。env.inline = true のとき改行で InputEnd になる。
pub fn parse_inline<I: EventInput, S: EventSink>(i: In<I, S>) -> Option<Mark> {
    parse_inline_impl(i, None)
}

/// `initial` に先読み済みの Mark を渡せる parse_inline の実装本体。
fn parse_inline_impl<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    initial: Option<Mark>,
) -> Option<Mark> {
    let mut pending = initial;
    loop {
        let mark = match pending.take() {
            Some(m) => m,
            None => scan_mark(i.rb())?,
        };
        match mark.nud.tag {
            MarkNudTag::Block(_) => {
                // text のみ emit。trivia はブロック構造の呼び出し元が処理する。
                if !mark.text.is_empty() {
                    i.env.state.sink.push(SyntaxKind::YmText, &mark.text);
                }
                return Some(mark);
            }
            MarkNudTag::Inline(inline_tag) => match inline_tag {
                InlineNudTag::Newline { .. } => {
                    // env.inline = false のとき: 改行を超えて継続。
                    // QuotePrefix trivia は lossless のため emit する。
                    emit_text_trivia(&mut i, &mark);
                }
                InlineNudTag::Emphasis => {
                    if i.env.stop.contains(&SyntaxKind::YmStarSigil) {
                        // 閉じ * — text/trivia を emit して返す（outer が sigil を emit する）
                        emit_text_trivia(&mut i, &mark);
                        return Some(mark);
                    }
                    emit_text_trivia(&mut i, &mark);
                    i.env.state.sink.start(SyntaxKind::YmEmphasis);
                    emit_nud_lex(&mut i, &mark);
                    i.env.stop.insert(SyntaxKind::YmStarSigil);
                    let stop = parse_inline(i.rb())?;
                    i.env.stop.remove(&SyntaxKind::YmStarSigil);
                    if matches!(stop.nud.tag, MarkNudTag::Inline(InlineNudTag::Emphasis)) {
                        // inner が text を emit 済み; 閉じ sigil のみ emit
                        emit_nud_lex(&mut i, &stop);
                    } else {
                        emit_mark(&mut i, &stop);
                    }
                    i.env.state.sink.finish();
                    if matches!(stop.nud.tag, MarkNudTag::Block(_)) {
                        return Some(stop);
                    }
                }
                InlineNudTag::Strong => {
                    if i.env.stop.contains(&SyntaxKind::YmStrongSigil) {
                        // 閉じ ** — text/trivia を emit して返す
                        emit_text_trivia(&mut i, &mark);
                        return Some(mark);
                    }
                    emit_text_trivia(&mut i, &mark);
                    i.env.state.sink.start(SyntaxKind::YmStrong);
                    emit_nud_lex(&mut i, &mark);
                    i.env.stop.insert(SyntaxKind::YmStrongSigil);
                    let stop = parse_inline(i.rb())?;
                    i.env.stop.remove(&SyntaxKind::YmStrongSigil);
                    if matches!(stop.nud.tag, MarkNudTag::Inline(InlineNudTag::Strong)) {
                        emit_nud_lex(&mut i, &stop);
                    } else {
                        emit_mark(&mut i, &stop);
                    }
                    i.env.state.sink.finish();
                    if matches!(stop.nud.tag, MarkNudTag::Block(_)) {
                        return Some(stop);
                    }
                }
                InlineNudTag::OpenBracket => {
                    emit_text_trivia(&mut i, &mark);
                    i.env.state.sink.start(SyntaxKind::YmInlineExpr);
                    emit_nud_lex(&mut i, &mark); // BracketL "["
                    let inner = parse_inline(i.rb())?;
                    if matches!(
                        inner.nud.tag,
                        MarkNudTag::Inline(InlineNudTag::CloseBracket)
                    ) {
                        emit_nud_lex(&mut i, &inner); // BracketR "]"
                        parse_bracket_led(i.rb())?;
                    } else {
                        emit_mark(&mut i, &inner);
                    }
                    i.env.state.sink.finish(); // YmInlineExpr
                    if matches!(inner.nud.tag, MarkNudTag::Block(_)) {
                        return Some(inner);
                    }
                }
                InlineNudTag::CloseBracket | InlineNudTag::CloseBrace => {
                    // 対応する open の呼び出し元に返す
                    emit_text_trivia(&mut i, &mark);
                    return Some(mark);
                }
                InlineNudTag::SectionClose => {
                    emit_text_trivia(&mut i, &mark);
                    return Some(mark);
                }
                InlineNudTag::Bang => {
                    emit_text_trivia(&mut i, &mark);
                    if i.maybe(item('['))?.is_none() {
                        // bare ! — そのまま emit
                        emit_nud_lex(&mut i, &mark);
                    } else {
                        // image: ![alt](url)
                        i.env.state.sink.start(SyntaxKind::YmInlineExpr);
                        emit_nud_lex(&mut i, &mark); // YmBang "!"
                        i.env.state.sink.push(SyntaxKind::YmLBracket, "[");
                        let inner = parse_inline(i.rb())?;
                        if matches!(
                            inner.nud.tag,
                            MarkNudTag::Inline(InlineNudTag::CloseBracket)
                        ) {
                            emit_nud_lex(&mut i, &inner); // BracketR "]"
                            parse_bracket_led(i.rb())?;
                        } else {
                            emit_mark(&mut i, &inner);
                        }
                        i.env.state.sink.finish(); // YmInlineExpr
                        if matches!(inner.nud.tag, MarkNudTag::Block(_)) {
                            return Some(inner);
                        }
                    }
                }
                InlineNudTag::Backslash => {
                    // TODO: escape sequence / inline command
                    emit_text_trivia(&mut i, &mark);
                    emit_nud_lex(&mut i, &mark);
                }
            },
        }
    }
}

// ---------------------------------------------------------------------------
// parse_paragraph
// ---------------------------------------------------------------------------

/// 段落を parse する。
/// scan_mark の結果が Inline(Newline) なら YmParagraph を開いて parse_inline へ。
/// Block nud が最初に来たらそのまま返す（空段落を作らない）。
fn parse_paragraph<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Mark> {
    i.env.inline = false;
    let first = scan_mark(i.rb())?;
    match first.nud.tag {
        MarkNudTag::Block(_) => {
            if first.text.is_empty() {
                // text なし = 構造的な区切り: trivia を YmNewline として emit
                emit_trivia_only(&mut i, &first);
            } else {
                // text あり = paragraph として wrap する
                i.env.state.sink.start(SyntaxKind::YmParagraph);
                emit_text_trivia(&mut i, &first);
                i.env.state.sink.finish();
            }
            return Some(first);
        }
        MarkNudTag::Inline(InlineNudTag::CloseBrace | InlineNudTag::CloseBracket) => {
            // ブロック doc の閉じ区切り: 空段落を作って返す
            i.env.state.sink.start(SyntaxKind::YmParagraph);
            i.env.state.sink.finish();
            return Some(first);
        }
        MarkNudTag::Inline(InlineNudTag::SectionClose) if first.text.is_empty() => {
            // ブロック位置の #. → YmSectionClose ノード
            i.env.state.sink.start(SyntaxKind::YmSectionClose);
            emit_nud_lex(&mut i, &first); // YmHashDotSigil "#."
            i.env.inline = true;
            let stop = parse_inline(i.rb())?;
            emit_trivia_only(&mut i, &stop); // \n → YmNewline
            i.env.state.sink.finish(); // YmSectionClose
            i.env.inline = false;
            return Some(stop);
        }
        MarkNudTag::Inline(InlineNudTag::Backslash) if first.text.is_empty() => {
            // ブロック位置の \cmd → YmCommand ノード
            i.env.state.sink.start(SyntaxKind::YmCommand);
            emit_nud_lex(&mut i, &first); // YmBackslash "\"
            // コマンド名 (識別子) をスキャン
            if let Some((_, ident_text)) = i.with_seq(crate::scan::ident) {
                i.env
                    .state
                    .sink
                    .push(SyntaxKind::YmIdent, ident_text.as_ref());
            }
            // 行末まで消費して trailing \n を YmNewline として emit
            i.env.inline = true;
            let stop = parse_inline(i.rb())?;
            emit_trivia_only(&mut i, &stop); // \n → YmNewline
            i.env.state.sink.finish(); // YmCommand
            i.env.inline = false;
            return Some(stop);
        }
        MarkNudTag::Inline(InlineNudTag::Newline { .. }) => {
            i.env.state.sink.start(SyntaxKind::YmParagraph);
            let stop = parse_inline_impl(i.rb(), Some(first))?;
            for part in stop.trivia.parts() {
                i.env.state.sink.push(part.kind.into(), &part.text);
            }
            i.env.state.sink.finish();
            Some(stop)
        }
        MarkNudTag::Inline(_) => {
            // doc 先頭など trivia なしで inline sigil が来るケース
            // first を parse_inline_impl に渡して正しく入れ子にする
            i.env.state.sink.start(SyntaxKind::YmParagraph);
            let stop = parse_inline_impl(i.rb(), Some(first))?;
            i.env.state.sink.finish();
            Some(stop)
        }
    }
}

// ---------------------------------------------------------------------------
// parse_heading
// ---------------------------------------------------------------------------

fn parse_heading<I: EventInput, S: EventSink>(mut i: In<I, S>, mark: Mark) -> Option<Mark> {
    i.env.state.sink.start(SyntaxKind::YmHeading);
    emit_nud_lex(&mut i, &mark);
    i.env.inline = true;
    let stop = parse_inline(i.rb())?;
    // stop は InputEnd か Block nud (text は parse_inline 側で emit 済み)
    if matches!(stop.nud.tag, MarkNudTag::Block(BlockNudTag::NewParagraph)) {
        // blank line が続く場合: trivia の最初の部分 (heading 終端 \n) のみ emit し、
        // blank line は parse_doc_body 側へ返して処理させる
        if let Some(part) = stop.trivia.parts().first() {
            let kind: SyntaxKind = if part.kind == TriviaKind::Space && part.text.contains('\n') {
                SyntaxKind::YmNewline
            } else {
                part.kind.into()
            };
            i.env.state.sink.push(kind, &part.text);
        }
        i.env.state.sink.finish(); // YmHeading
        i.env.inline = false;
        return Some(stop); // parse_doc_body の NewParagraph ハンドラへ
    }
    emit_trivia_only(&mut i, &stop); // trailing trivia を YmNewline 等で emit
    i.env.state.sink.finish();
    i.env.inline = false;
    parse_doc_body(i) // 見出し後の本文を継続パース
}

// ---------------------------------------------------------------------------
// parse_fence
// ---------------------------------------------------------------------------

fn parse_fence<I: EventInput, S: EventSink>(mut i: In<I, S>, mark: Mark) -> Option<Mark> {
    i.env.state.sink.start(SyntaxKind::YmCodeFence);
    emit_nud_lex(&mut i, &mark);
    // info line (``` の後、同じ行) — yulang fence かどうかを先に判定
    let is_yulang = i.lookahead(tag("yulang")).is_some();
    i.env.state.sink.start(SyntaxKind::YmCodeFenceInfo);
    i.env.inline = true;
    let info_stop = parse_inline(i.rb())?;
    i.env.inline = false;
    // parse_inline already emitted text; only emit trivia (newline) AFTER closing info
    i.env.state.sink.finish(); // YmCodeFenceInfo
    emit_trivia_only(&mut i, &info_stop);
    // early exit on real EOI or document-level terminal
    if is_terminal(&info_stop) {
        i.env.state.sink.finish(); // YmCodeFence
        return Some(info_stop);
    }
    if is_yulang {
        parse_fence_yulang(i)
    } else {
        parse_fence_raw(i)
    }
}

/// 通常フェンス body: raw text loop
fn parse_fence_raw<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Mark> {
    i.env.state.sink.start(SyntaxKind::YmCodeFenceText);
    loop {
        let inner = scan_mark(i.rb())?;
        match inner.nud.tag {
            MarkNudTag::Block(BlockNudTag::Fence) => {
                emit_text_trivia(&mut i, &inner);
                i.env.state.sink.finish(); // YmCodeFenceText
                emit_nud_lex(&mut i, &inner);
                i.env.state.sink.finish(); // YmCodeFence
                // ``` の後の構造的区切り \n を読み飛ばしてから継続
                let sep = scan_mark(i.rb())?;
                if is_terminal(&sep) {
                    return Some(sep);
                }
                match sep.nud.tag {
                    // 空テキスト + 単純改行: 構造区切りとして読み捨て
                    MarkNudTag::Inline(InlineNudTag::Newline { .. }) if sep.text.is_empty() => {
                        return parse_doc_body(i);
                    }
                    MarkNudTag::Block(_) => return parse_block_nud(i, sep),
                    _ => return parse_doc_body(i),
                }
            }
            MarkNudTag::Block(
                BlockNudTag::InputEnd | BlockNudTag::Dequote { .. } | BlockNudTag::DocBlockClose,
            ) => {
                emit_text_trivia(&mut i, &inner);
                i.env.state.sink.finish(); // YmCodeFenceText (未閉じ)
                i.env.state.sink.finish(); // YmCodeFence
                return Some(inner);
            }
            _ => emit_mark(&mut i, &inner),
        }
    }
}

/// Yulang フェンス body: stmt パーサで解析
fn parse_fence_yulang<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Mark> {
    i.env.stop.insert(SyntaxKind::YmFenceSigil);
    let mut next_info: Option<TriviaInfo> = None;

    loop {
        let info = if let Some(info) = next_info.take() {
            info
        } else {
            let trivia = i.run(scan_trivia)?;
            trivia.info()
        };

        let Some(parsed) = crate::stmt::parse_statement(info, i.rb()) else {
            break;
        };

        match parsed {
            Either::Left(next) => next_info = Some(next),
            Either::Right(stop) => {
                if stop.kind == SyntaxKind::YmFenceSigil {
                    // 閉じ ``` — フェンス終了
                    i.env.stop.remove(&SyntaxKind::YmFenceSigil);
                    i.env.state.sink.lex(&stop);
                    i.env.state.sink.finish(); // YmCodeFence
                    let sep = scan_mark(i.rb())?;
                    if is_terminal(&sep) {
                        return Some(sep);
                    }
                    match sep.nud.tag {
                        MarkNudTag::Inline(InlineNudTag::Newline { .. }) if sep.text.is_empty() => {
                            return parse_doc_body(i);
                        }
                        MarkNudTag::Block(_) => return parse_block_nud(i, sep),
                        _ => return parse_doc_body(i),
                    }
                }
                // 予期しない stop — 終了
                break;
            }
        }
    }

    // 閉じ ``` なし — unclosed fence
    i.env.stop.remove(&SyntaxKind::YmFenceSigil);
    i.env.state.sink.finish(); // YmCodeFence (unclosed)
    None
}

// ---------------------------------------------------------------------------
// parse_blockquote
// ---------------------------------------------------------------------------

fn parse_blockquote<I: EventInput, S: EventSink>(mut i: In<I, S>, mark: Mark) -> Option<Mark> {
    i.env.state.sink.start(SyntaxKind::YmQuoteBlock);
    emit_nud_lex(&mut i, &mark);
    let outer_depth = i.env.mark_quote_depth;
    i.env.mark_quote_depth += 1;
    let stop = parse_doc_body(i.rb())?;
    i.env.mark_quote_depth = outer_depth;
    i.env.state.sink.finish();
    match stop.nud.tag {
        MarkNudTag::Block(BlockNudTag::Dequote { quote_level, .. })
            if quote_level < outer_depth =>
        {
            Some(stop) // さらに外へ伝播
        }
        MarkNudTag::Block(BlockNudTag::Dequote { .. }) => {
            // 同じ深さへの dequote: 外側の doc_body を継続
            parse_doc_body(i)
        }
        _ => parse_block_nud(i, stop),
    }
}

// ---------------------------------------------------------------------------
// parse_list
// ---------------------------------------------------------------------------

fn parse_list<I: EventInput, S: EventSink>(mut i: In<I, S>, first_mark: Mark) -> Option<Mark> {
    i.env.state.sink.start(SyntaxKind::YmList);
    let mut stop = parse_list_item(i.rb(), first_mark)?;
    loop {
        match stop.nud.tag {
            MarkNudTag::Block(BlockNudTag::ListMinus | BlockNudTag::ListNum) => {
                // TODO: indent チェックで同一リストか確認
                stop = parse_list_item(i.rb(), stop)?;
            }
            _ => break,
        }
    }
    i.env.state.sink.finish(); // YmList
    Some(stop)
}

fn parse_list_item<I: EventInput, S: EventSink>(mut i: In<I, S>, mark: Mark) -> Option<Mark> {
    i.env.state.sink.start(SyntaxKind::YmListItem);
    emit_nud_lex(&mut i, &mark);
    i.env.state.sink.start(SyntaxKind::YmListItemBody);
    i.env.inline = true;
    let stop = parse_inline(i.rb())?;
    i.env.state.sink.finish(); // YmListItemBody
    i.env.state.sink.finish(); // YmListItem
    Some(stop)
}

// ---------------------------------------------------------------------------
// parse_block_nud
// ---------------------------------------------------------------------------

pub fn parse_block_nud<I: EventInput, S: EventSink>(mut i: In<I, S>, mark: Mark) -> Option<Mark> {
    match mark.nud.tag {
        MarkNudTag::Block(block_tag) => match block_tag {
            BlockNudTag::Heading => parse_heading(i, mark),
            BlockNudTag::Fence => parse_fence(i, mark),
            BlockNudTag::BlockQuote => parse_blockquote(i, mark),
            BlockNudTag::ListMinus | BlockNudTag::ListNum => parse_list(i, mark),
            BlockNudTag::NewParagraph => {
                i.env.state.sink.start(SyntaxKind::YmBlankLine);
                i.env.state.sink.finish();
                parse_doc_body(i)
            }
            BlockNudTag::DocBlockClose => {
                // `---` — 呼び出し元（DocBlock parser）へ伝播
                emit_nud_lex(&mut i, &mark);
                Some(mark)
            }
            BlockNudTag::InputEnd | BlockNudTag::Dequote { .. } | BlockNudTag::LineEnd => {
                Some(mark)
            }
        },
        MarkNudTag::Inline(_) => unreachable!("parse_block_nud に Inline nud"),
    }
}

// ---------------------------------------------------------------------------
// parse_doc_body — メインブロックループ
// ---------------------------------------------------------------------------

fn parse_doc_body<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Mark> {
    loop {
        let stop = parse_paragraph(i.rb())?;
        if is_terminal(&stop) {
            return Some(stop);
        }
        match stop.nud.tag {
            MarkNudTag::Block(BlockNudTag::NewParagraph) => {
                i.env.state.sink.start(SyntaxKind::YmBlankLine);
                i.env.state.sink.finish();
            }
            MarkNudTag::Block(_) => {
                let next = parse_block_nud(i.rb(), stop)?;
                if is_terminal(&next) {
                    return Some(next);
                }
                if matches!(
                    next.nud.tag,
                    MarkNudTag::Inline(InlineNudTag::CloseBrace | InlineNudTag::CloseBracket)
                ) {
                    return Some(next);
                }
                // block parser (e.g. parse_heading) が NewParagraph を返した場合
                if matches!(next.nud.tag, MarkNudTag::Block(BlockNudTag::NewParagraph)) {
                    i.env.state.sink.start(SyntaxKind::YmBlankLine);
                    i.env.state.sink.finish();
                }
            }
            MarkNudTag::Inline(InlineNudTag::CloseBrace | InlineNudTag::CloseBracket) => {
                return Some(stop);
            }
            MarkNudTag::Inline(InlineNudTag::SectionClose) => {
                // 連続 #.#. 等: parse_paragraph の SectionClose ブランチから伝播
                i.env.state.sink.start(SyntaxKind::YmSectionClose);
                emit_nud_lex(&mut i, &stop);
                i.env.state.sink.finish();
                // 改行は次の parse_paragraph 呼び出しで処理される
            }
            MarkNudTag::Inline(_) => unreachable!(),
        }
    }
}

// ---------------------------------------------------------------------------
// Public entry points
// ---------------------------------------------------------------------------

/// DocLine モード: `--` doc コメントなど一行インライン
pub fn parse_doc_line<I: EventInput, S: EventSink>(mut i: In<I, S>) {
    i.env.state.sink.start(SyntaxKind::YmDoc);
    i.env.inline = true;
    let _ = parse_inline(i.rb());
    i.env.state.sink.finish();
}

/// DocBlock モード: `---` で囲まれたフル Yumark ドキュメント
pub fn parse_doc<I: EventInput, S: EventSink>(mut i: In<I, S>) {
    i.env.state.sink.start(SyntaxKind::YmDoc);
    i.env.inline = false;
    let _ = parse_doc_body(i.rb());
    i.env.state.sink.finish();
}

pub fn parse_doc_body_pub<I: EventInput, S: EventSink>(i: In<I, S>) -> Option<Mark> {
    parse_doc_body(i)
}
