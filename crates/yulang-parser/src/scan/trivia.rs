use crate::{
    EventInput,
    context::In,
    lex::{Trivia, TriviaInfo, TriviaKind, TriviaPart},
    sink::EventSink,
};
use chasa::{
    parser::SkipParserOnce as _,
    prelude::{any, choice, from_fn_mut, item, many_skip, none_of, one_of, tag},
};
use smallvec::{SmallVec, smallvec};

pub fn scan_trivia<I: EventInput, S: EventSink>(mut i: In<I, S>) -> Option<Trivia> {
    let mut max_quote_depth = i.env.mark_quote_depth;
    let mut trivias: SmallVec<[TriviaPart; 1]> = smallvec![];
    loop {
        let line_sp = choice((
            (tag("//"), many_skip(none_of("\r\n")))
                .to(TriviaKind::LineComment)
                .with_seq(),
            from_fn_mut(|i| quoted_space(i, &mut max_quote_depth)).with_seq(),
        ));
        if let Some((kind, text)) = i.maybe(line_sp)? {
            trivias.push(TriviaPart::new(kind, text))
        } else if i
            .maybe_fn(|i| block_comment(i, &mut trivias, &mut max_quote_depth))?
            .is_none()
        {
            break;
        }
    }
    let trivia = Trivia::new(trivias);
    if let TriviaInfo::Newline { indent, .. } = trivia.info() {
        i.env.state.line_indent = indent
    }
    return Some(trivia);
}

fn quoted_space<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    max_quote_depth: &mut usize,
) -> Option<TriviaKind> {
    let start_index = i.index();
    let mut trivia_kind = TriviaKind::Space;
    loop {
        i.many_skip(one_of(" \t"))?; // 要らない空白を取る
        if *max_quote_depth == 0 {
            let ln = choice((tag("\r\n"), one_of("\r\n"))).skip();
            if i.maybe(ln)?.is_none() {
                if i.index() == start_index {
                    return None; // 何も消費していない → 失敗
                }
                return Some(trivia_kind);
            }
            i.many_skip(one_of(" \t"))?; // 改行後のインデント空白
            return Some(trivia_kind);
        }
        let ln = choice((tag("\r\n"), one_of("\r\n"))).skip();
        if i.maybe(ln)?.is_none() {
            if i.index() == start_index {
                return None; // 何も消費していない → 失敗
            }
            return Some(trivia_kind);
        }
        // `> ` または `>` 単独 (空行継続) を quote prefix としてカウント
        *max_quote_depth = i.many_map(
            from_fn_mut(|mut j: In<I, S>| {
                j.skip(item('>'))?;
                let _ = j.maybe(one_of(" \t"))?;
                Some(())
            }),
            |it| it.take(*max_quote_depth).count(),
        )?;
        if *max_quote_depth > 0 {
            trivia_kind = TriviaKind::QuotePrefix;
        }
    }
}

pub(crate) fn block_comment<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    trivias: &mut SmallVec<[TriviaPart; 1]>,
    max_quote_depth: &mut usize,
) -> Option<()> {
    let (_, text) = i.with_seq((item('/'), item('*')))?;
    trivias.push(TriviaPart::new(TriviaKind::BlockCommentStart, text));
    let mut checkpoint = i.input.checkpoint();
    let mut depth = 1_usize;
    loop {
        let middle_checkpoint = i.input.checkpoint();
        if i.maybe(item('/'))?.is_some() {
            // `/*/` のように `*/` が直後に続く場合はネスト開きではなくスキップ
            i.many_skip(tag("*/"))?;
            if i.maybe(item('*'))?.is_some() {
                // ネスト開き "/*"
                let new_checkpoint = i.input.checkpoint();
                let normal = TriviaPart::new(
                    TriviaKind::BlockCommentText,
                    I::seq(checkpoint, middle_checkpoint.clone()),
                );
                if !normal.text.is_empty() {
                    trivias.push(normal);
                }
                trivias.push(TriviaPart::new(
                    TriviaKind::BlockCommentStart,
                    I::seq(middle_checkpoint, new_checkpoint.clone()),
                ));
                checkpoint = new_checkpoint;
                depth += 1;
            }
            // else: コメント本文中の "/" — 次のループで checkpoint に含まれる
        } else if i.maybe(item('*'))?.is_some() {
            // `*/*/ ` のように `/*` が直後に続く場合はネスト閉じではなくスキップ
            i.many_skip(tag("/*"))?;
            if i.maybe(item('/'))?.is_some() {
                // 閉じ "*/"
                let new_checkpoint = i.input.checkpoint();
                let normal = TriviaPart::new(
                    TriviaKind::BlockCommentText,
                    I::seq(checkpoint, middle_checkpoint.clone()),
                );
                if !normal.text.is_empty() {
                    trivias.push(normal);
                }
                trivias.push(TriviaPart::new(
                    TriviaKind::BlockCommentEnd,
                    I::seq(middle_checkpoint, new_checkpoint.clone()),
                ));
                depth -= 1;
                if depth == 0 {
                    return Some(());
                }
                checkpoint = new_checkpoint;
            }
            // else: コメント本文中の "*" — 次のループで checkpoint に含まれる
        } else if let Some((kind, text)) =
            i.maybe(from_fn_mut(|i| quoted_space(i, max_quote_depth)).with_seq())?
        {
            let normal = TriviaPart::new(
                TriviaKind::BlockCommentText,
                I::seq(checkpoint, middle_checkpoint.clone()),
            );
            if !normal.text.is_empty() {
                trivias.push(normal);
            }
            trivias.push(TriviaPart::new(kind, text));
            checkpoint = i.input.checkpoint()
        } else if i.maybe(any)?.is_none() {
            // EOF — 未閉じコメント
            trivias.push(TriviaPart::new(TriviaKind::BlockCommentEnd, ""));
            return Some(());
        }
    }
}
