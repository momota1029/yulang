use chasa::prelude::*;

use crate::EventInput;
use crate::context::In;
use crate::lex::{BareToken, Lex, SyntaxKind, Trivia, TriviaInfo};
use crate::sink::EventSink;

use crate::scan::trivia;

/// 文字列リテラルのモード
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StringMode {
    /// 通常の `"..."` 文字列
    Normal,
    /// Heredoc `"""..."""` 文字列（連続するクォートの数を保持）
    Heredoc { quotes: usize },
}

#[derive(Debug)]
pub enum StrNud {
    Escape,
    Interp,
    End(Trivia),
}

// ─────────────────────────────────────────────
// 文字列開始スキャン
// ─────────────────────────────────────────────

/// `"` を1個以上スキャンして `(StringStart lex, StringMode)` を返す。
///
/// - `"` が3個以上 → Heredoc モード（ greedy でスキャン）
/// - `"` が1個 → Normal モード
pub fn scan_string_start<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    mut i: In<I, S>,
) -> Option<Lex> {
    let (_, text) = i.with_seq((item('"'), (tag("\"\""), item('\"').many_skip()).or_not()))?;
    Some(Lex::new(
        leading_info,
        SyntaxKind::StringStart,
        text.as_ref(),
        Trivia::empty(),
    ))
}

pub fn scan_string_nud<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    mode: StringMode,
) -> Option<(Box<str>, BareToken<StrNud>)> {
    let token = from_fn_mut(|mut i: In<I, S>| {
        let start = i.input.checkpoint();
        let esc = item('\\')
            .to((SyntaxKind::StringEscapeLead, StrNud::Escape))
            .with_seq();
        let interp = item('%')
            .to((SyntaxKind::StringInterpPercent, StrNud::Interp))
            .with_seq();
        let end = from_fn(|mut i| {
            let (_, text) = i.with_seq(from_fn(|mut i| match mode {
                StringMode::Normal => i.skip(item('"')),
                StringMode::Heredoc { quotes } => {
                    for _ in 0..quotes {
                        i.skip(item('"'))?
                    }
                    Some(())
                }
            }))?;
            Some((
                (SyntaxKind::StringEnd, StrNud::End(trivia::scan_trivia(i)?)),
                text,
            ))
        });
        i.run((value(start), choice((esc, interp, end))))
    });

    let start = i.input.checkpoint();
    let ((), (end, ((kind, tag), tag_text))) = i.many_till(any.skip(), token)?;
    Some((
        Box::from(I::seq(start, end).as_ref()),
        BareToken {
            kind,
            tag,
            text: Box::from(tag_text.as_ref()),
        },
    ))
}
