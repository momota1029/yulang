use chasa::parser::str::tag;
use chasa::parser::{SkipParserMut as _, SkipParserOnce as _};
use chasa::prelude::{any, from_fn, item, many_till, one_of};
use either::Either;
use reborrow_generic::Reborrow as _;

use crate::EventInput;
use crate::context::In;
use crate::lex::{Lex, SyntaxKind, Trivia, TriviaInfo};
use crate::sink::EventSink;
use crate::string::scan::{StrNud, StringMode, scan_string_nud};

use crate::expr::parse_expr_bp;

pub(crate) fn parse_string_lit<I: EventInput, S: EventSink>(
    i: In<I, S>,
    start_lex: Lex,
) -> Option<TriviaInfo> {
    parse_string(i, start_lex)
}

pub fn parse_string<I: EventInput, S: EventSink>(
    mut i: In<I, S>,
    start_lex: Lex,
) -> Option<TriviaInfo> {
    i.env.state.sink.start(SyntaxKind::StringLit);
    i.env.state.sink.lex(&start_lex);
    let mode = if start_lex.text.len() == 1 {
        StringMode::Normal
    } else {
        StringMode::Heredoc {
            quotes: start_lex.text.len(),
        }
    };
    loop {
        let (text, tok) = scan_string_nud(i.rb(), mode)?;
        if !text.is_empty() {
            i.env.state.sink.push(SyntaxKind::StringText, text.as_ref());
        }
        match tok.tag {
            StrNud::Interp => {
                i.env.state.sink.start(SyntaxKind::StringInterp);
                i.env.state.sink.push(tok.kind, tok.text.as_ref());

                let chk = from_fn(|i: In<I, S>| Some(i.input.checkpoint()));
                let (start, ((), ((end, _), text))) =
                    i.run((chk, many_till(any.skip(), (chk, item('{')).with_seq())))?;
                let fmt = I::seq(start, end);
                if !fmt.as_ref().is_empty() {
                    i.env
                        .state
                        .sink
                        .push(SyntaxKind::StringInterpFormatText, fmt.as_ref());
                }
                i.env
                    .state
                    .sink
                    .push(SyntaxKind::StringInterpOpenBrace, text.as_ref());
                let mut j = i.rb();
                j.env.stop.insert(SyntaxKind::BraceR);
                let mut stop_lex = match parse_expr_bp(None, TriviaInfo::None, j)? {
                    Ok(Either::Right(stop)) if stop.kind == SyntaxKind::BraceR => stop,
                    Err(led) if led.lex.kind == SyntaxKind::BraceR => led.lex,
                    _ => {
                        i.env.state.sink.finish();
                        continue;
                    }
                };
                let trailing_text: String = stop_lex
                    .trailing_trivia
                    .parts()
                    .iter()
                    .map(|p| p.text.as_ref())
                    .collect();
                stop_lex.trailing_trivia = Trivia::empty();

                stop_lex.kind = SyntaxKind::StringInterpCloseBrace;
                i.env.state.sink.lex(&stop_lex);
                i.env.state.sink.finish();

                if !trailing_text.is_empty() {
                    i.env
                        .state
                        .sink
                        .push(SyntaxKind::StringText, &trailing_text);
                }
            }
            StrNud::Escape => {
                i.env.state.sink.push(tok.kind, tok.text.as_ref());
                if let Some((_, text)) = i.maybe(tag("u{").with_seq())? {
                    i.env
                        .state
                        .sink
                        .push(SyntaxKind::StringEscapeUnicodeStart, text.as_ref());
                    let (_, text) =
                        i.with_seq(one_of(|c: char| c.is_ascii_hexdigit()).many1_skip())?;
                    i.env
                        .state
                        .sink
                        .push(SyntaxKind::StringEscapeUnicodeHex, text.as_ref());
                    let (_, text) = i.run(item('}').with_seq())?;
                    i.env
                        .state
                        .sink
                        .push(SyntaxKind::StringEscapeUnicodeEnd, text.as_ref());
                } else {
                    let (_, text) = i.run(any.with_seq())?;
                    i.env
                        .state
                        .sink
                        .push(SyntaxKind::StringEscapeSimple, text.as_ref());
                }
            }
            StrNud::End(trailing_trivia) => {
                let info = trailing_trivia.info();
                let end_lex = Lex::new(TriviaInfo::None, tok.kind, tok.text, trailing_trivia);
                i.env.state.sink.lex(&end_lex);
                i.env.state.sink.finish();
                return Some(info);
            }
        }
    }
}
