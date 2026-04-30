use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, Trivia, TriviaInfo};
use crate::mark::parse::{parse_doc_body_pub, parse_inline};
use crate::mark::scan::Mark;
use crate::parse::emit_invalid;
use crate::scan::trivia::scan_trivia;
use crate::sink::EventSink;
use chasa::prelude::{any, item};
use either::Either;
use reborrow_generic::Reborrow as _;

#[derive(Debug, Clone, Copy)]
struct YumarkBoundary {
    close_kind: SyntaxKind,
    close_text: &'static str,
    body_kind: SyntaxKind,
    allow_blocks: bool,
}

const YUMARK_INLINE_BRACKET: YumarkBoundary = YumarkBoundary {
    close_kind: SyntaxKind::BracketR,
    close_text: "]",
    body_kind: SyntaxKind::MarkInlineBody,
    allow_blocks: false,
};

const YUMARK_BLOCK_BRACE: YumarkBoundary = YumarkBoundary {
    close_kind: SyntaxKind::BraceR,
    close_text: "}",
    body_kind: SyntaxKind::MarkHeredocBody,
    allow_blocks: true,
};

pub(super) fn parse_quoted_mark_expr<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    quote_lex: Lex,
) -> Option<Either<TriviaInfo, Lex>> {
    i.env.state.sink.start(SyntaxKind::MarkExpr);

    let after_quote = quote_lex.trailing_trivia_info();
    let Some((start_lex, boundary)) =
        scan_quoted_mark_start(quote_lex.leading_trivia_info, after_quote, i.rb())
    else {
        i.env.state.sink.start(SyntaxKind::InvalidToken);
        i.env.state.sink.finish();
        i.env.state.sink.finish();
        return Some(Either::Left(after_quote));
    };

    i.env.state.sink.start(boundary.body_kind);
    i.env.state.sink.lex(&start_lex);
    let end = parse_quoted_yumark_body(i.rb(), boundary)?;
    let after = end.trailing_trivia_info();
    i.env.state.sink.lex(&end);
    i.env.state.sink.finish();
    i.env.state.sink.finish();
    Some(Either::Left(after))
}

fn scan_quoted_mark_start<I: EventInput, S: EventSink>(
    leading_info: TriviaInfo,
    after_quote: TriviaInfo,
    mut i: In<I, S>,
) -> Option<(Lex, YumarkBoundary)> {
    if !matches!(after_quote, TriviaInfo::None) {
        return None;
    }

    if i.maybe(item('['))?.is_some() {
        return Some((
            Lex::new(
                leading_info,
                SyntaxKind::MarkLitStart,
                "'[",
                Trivia::empty(),
            ),
            YUMARK_INLINE_BRACKET,
        ));
    }

    if i.maybe(item('{'))?.is_some() {
        return Some((
            Lex::new(
                leading_info,
                SyntaxKind::MarkLitStart,
                "'{",
                Trivia::empty(),
            ),
            YUMARK_BLOCK_BRACE,
        ));
    }

    None
}

fn parse_quoted_yumark_body<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    boundary: YumarkBoundary,
) -> Option<Lex> {
    i.env.stop.insert(boundary.close_kind);
    i.env.state.sink.start(SyntaxKind::YmDoc);

    let close = if boundary.allow_blocks {
        if let Some(close) = consume_empty_close(i.rb(), boundary)? {
            close
        } else {
            let tail = parse_doc_body_pub(i.rb())?;
            let tail_kind = tail.nud.lex.as_ref().map(|l| l.kind);
            if tail_kind != Some(boundary.close_kind) {
                return None;
            }
            let tail_text = tail.nud.lex.as_ref().map(|l| l.text.as_ref()).unwrap_or("");
            Lex::new(
                TriviaInfo::None,
                SyntaxKind::MarkLitEnd,
                tail_text,
                i.run(scan_trivia)?,
            )
        }
    } else {
        if let Some(close) = consume_empty_close(i.rb(), boundary)? {
            close
        } else {
            let tail = parse_inline(i.rb())?;
            let tail_kind = tail.nud.lex.as_ref().map(|l| l.kind);
            if tail_kind != Some(boundary.close_kind) {
                recover_invalid_inline_tail(i.rb(), tail, boundary)?
            } else {
                let tail_text = tail.nud.lex.as_ref().map(|l| l.text.as_ref()).unwrap_or("");
                Lex::new(
                    TriviaInfo::None,
                    SyntaxKind::MarkLitEnd,
                    tail_text,
                    i.run(scan_trivia)?,
                )
            }
        }
    };

    i.env.state.sink.finish();
    Some(close)
}

fn recover_invalid_inline_tail<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    tail: Mark,
    boundary: YumarkBoundary,
) -> Option<Lex> {
    let (text, kind) = match &tail.nud.lex {
        Some(lex) => (lex.text.as_ref(), lex.kind),
        None => (tail.text.as_ref(), SyntaxKind::Unknown),
    };
    emit_invalid(
        i.rb(),
        Lex::new(TriviaInfo::None, kind, text, Trivia::empty()),
    );

    let mut skipped = String::new();
    loop {
        let closed = match boundary.close_kind {
            SyntaxKind::BracketR => i.maybe(item(']'))?.is_some(),
            SyntaxKind::BraceR => i.maybe(item('}'))?.is_some(),
            _ => false,
        };
        if closed {
            if !skipped.is_empty() {
                emit_invalid(
                    i.rb(),
                    Lex::new(
                        TriviaInfo::None,
                        SyntaxKind::Unknown,
                        skipped.as_str(),
                        Trivia::empty(),
                    ),
                );
            }
            return Some(Lex::new(
                TriviaInfo::None,
                SyntaxKind::MarkLitEnd,
                boundary.close_text,
                i.run(scan_trivia)?,
            ));
        }

        match i.run(any) {
            Some(ch) => skipped.push(ch),
            None => return None,
        }
    }
}

fn consume_empty_close<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    boundary: YumarkBoundary,
) -> Option<Option<Lex>> {
    let closed = match boundary.close_kind {
        SyntaxKind::BracketR => i.maybe(item(']'))?.is_some(),
        SyntaxKind::BraceR => i.maybe(item('}'))?.is_some(),
        _ => false,
    };

    if !closed {
        return Some(None);
    }

    Some(Some(Lex::new(
        TriviaInfo::None,
        SyntaxKind::MarkLitEnd,
        boundary.close_text,
        i.run(scan_trivia)?,
    )))
}
