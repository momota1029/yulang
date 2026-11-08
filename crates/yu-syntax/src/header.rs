//! Source-leading header discovery using the same owners as full construction.

use std::{ops::Range, sync::Arc};

use reborrow_generic::Reborrow as _;

use crate::{
    HeaderCoverage, HeaderImport, HeaderInfo, HeaderOperator, HeaderStop, SourceText,
    syntax_kind::SyntaxKind,
};

use crate::{
    cursor::{LexIn, Recover},
    handoff::{Either, NormalizedExit},
    lexical::{current_item::LineEntry, item::Item},
    yumark::judge::StatementPosition,
};

pub(crate) struct HeaderDiscovery {
    pub(crate) coverage: Range<usize>,
    pub(crate) stop: HeaderStop,
    pub(crate) imports: Vec<HeaderImport>,
    pub(crate) operators: Vec<HeaderOperator>,
}

impl HeaderDiscovery {
    pub(crate) fn into_header_info(self, source: Arc<SourceText>) -> HeaderInfo {
        HeaderInfo {
            source,
            coverage: HeaderCoverage {
                range: self.coverage,
                stop: self.stop,
            },
            imports: self.imports.into(),
            operators: self.operators.into(),
        }
    }
}

pub(crate) fn discover_header(source: &str) -> HeaderDiscovery {
    crate::cursor::discover_header(source)
}

pub(crate) fn discover_header_with_cursor(
    source: &str,
    recover: &mut Recover,
    output: &mut rowan::GreenNodeBuilder,
) -> HeaderDiscovery {
    output.start_node(SyntaxKind::Root.into());
    let mut remaining = source;
    let mut origin = 0;
    let mut line = LineEntry::PhysicalStart;
    let mut pending = None;
    let mut imports = Vec::new();
    let mut facts = Vec::new();
    let (coverage_end, stop) = loop {
        let entered_at_start = line == LineEntry::PhysicalStart;
        let mut i: crate::cursor::SyntaxIn =
            crate::cursor::SyntaxIn::new(&mut remaining, &mut *recover, &mut *output);
        let mut item = pending.take().unwrap_or_else(|| {
            i.token(|lex| {
                Some(crate::declaration::next_use_item_lex(
                    lex,
                    &mut origin,
                    &mut line,
                    None,
                ))
            })
            .unwrap()
        });
        let leading_newline = item.leading_view().contains_line_break();
        let indentation =
            crate::lexical::observation::indentation_after_newline(item.leading_view());
        let start = origin - item.payload_view().spelling().map_or(0, str::len);
        let at_start = (start == 0 || leading_newline || entered_at_start)
            && indentation
                .unwrap_or_else(|| usize::from(item.leading_view().has_ordinary_horizontal_gap()))
                == 0;
        item.emit_all_remaining_leading(&mut *i.state);
        if item.payload_view().is_eof() {
            break (origin, HeaderStop::Eof);
        }
        if !at_start {
            break (start, HeaderStop::FirstNonHeader);
        }
        let is_doc = i
            .rb()
            .map(
                |lex: LexIn| {
                    Some(
                        crate::declaration::doc_comment_selected_lexical(
                            lex.remainder(),
                            &item,
                            origin,
                            StatementPosition::CanonicalLineStart { base_col: 0 },
                        )
                        .is_some(),
                    )
                },
                |selected| selected,
            )
            .unwrap();
        if is_doc {
            break (start, HeaderStop::FirstNonHeader);
        }
        let is_use =
            crate::declaration::use_declaration_selected_normalized(i.rb(), &item, origin, None);
        let is_operator = !is_use
            && i.rb()
                .map(
                    |lex: LexIn| Some(operator_selected(lex, &item, origin, None)),
                    |x| x,
                )
                .unwrap();
        if !is_use && !is_operator {
            break (start, HeaderStop::FirstNonHeader);
        }
        drop(i);
        if is_use {
            let (exit, batch) = crate::declaration::use_declaration_header_normalized(
                crate::cursor::SyntaxIn::new(&mut remaining, &mut *recover, &mut *output),
                item,
                0,
                0,
                origin,
                line,
                None,
            );
            imports.extend(batch);
            origin = source.len() - remaining.len();
            let (item, next_line) = match exit {
                NormalizedExit::Complete(Err(Either::Left(item)), line)
                | NormalizedExit::Deferred(item, line) => (Some(item), line),
                NormalizedExit::Complete(Err(Either::Right(end)), line) => (Some(end.item), line),
                NormalizedExit::Complete(Ok(()), line) => (None, line),
            };
            pending = item;
            line = next_line;
        } else {
            let (item, next_origin, next_line, fact) =
                crate::declaration::operator_header_normalized(
                    crate::cursor::SyntaxIn::new(&mut remaining, &mut *recover, &mut *output),
                    item,
                    origin,
                    line,
                    None,
                );
            origin = next_origin;
            line = next_line;
            if let Some(fact) = fact {
                facts.push(fact);
            }
            pending = item;
            if pending.is_none() {
                let mut i: crate::cursor::SyntaxIn =
                    crate::cursor::SyntaxIn::new(&mut remaining, &mut *recover, &mut *output);
                let ((), text) = i
                    .token(|mut lex| {
                        let ((), text) = lex.rb().with_str(|lex| skip_opaque_body(lex));
                        Some(((), text))
                    })
                    .unwrap();
                origin += text.len();
                output.token(SyntaxKind::Unknown.into(), text);
                line = LineEntry::PhysicalStart;
            }
        }
    };
    output.finish_node();
    HeaderDiscovery {
        coverage: 0..coverage_end,
        stop,
        imports,
        operators: facts,
    }
}

pub(super) fn operator_selected(
    mut i: LexIn,
    item: &Item,
    origin: usize,
    fence: Option<&crate::lexical::yumark::FenceBoundary>,
) -> bool {
    // Statement intro rule 3 reserves `my <word> =` for Binding before
    // interpreting the word as an explicit-private operator modifier.
    if item.payload_view().spelling() == Some("my")
        && crate::declaration::binding::binding_statement_selected_lexical(
            i.remainder(),
            item,
            0,
            origin,
            fence,
        )
    {
        return false;
    }
    let mut word = item.payload_view().spelling().unwrap_or("").to_owned();
    if matches!(word.as_str(), "my" | "our" | "pub" | "lazy") {
        let mut position = origin;
        let mut line = LineEntry::InLine;
        let mut selected = false;
        let _: Option<()> = i.token(|mut lex| {
            if matches!(word.as_str(), "my" | "our" | "pub") {
                let item = crate::declaration::next_use_item_lex(
                    lex.rb(),
                    &mut position,
                    &mut line,
                    fence,
                );
                if item.leading_view().is_grammar_empty()
                    || item.leading_view().contains_line_break()
                {
                    return None;
                }
                word = item.payload_view().spelling().unwrap_or("").to_owned();
            }
            if word == "lazy" {
                let item =
                    crate::declaration::next_use_item_lex(lex, &mut position, &mut line, fence);
                if item.leading_view().is_grammar_empty()
                    || item.leading_view().contains_line_break()
                {
                    return None;
                }
                word = item.payload_view().spelling().unwrap_or("").to_owned();
            }
            selected = matches!(word.as_str(), "prefix" | "infix" | "suffix" | "nullfix");
            None
        });
        selected
    } else {
        matches!(word.as_str(), "prefix" | "infix" | "suffix" | "nullfix")
    }
}

/// The body is scanned once on the live lexical cursor. Nested lexical regions
/// protect their own delimiters and physical lines from the outer layout loop.
fn skip_opaque_body(mut i: LexIn) {
    let mut closes = Vec::new();
    while !i.remainder().is_empty() {
        if opaque_region(i.rb()) {
            continue;
        }
        let c = i.next().unwrap();
        if let Some(close) = matching_close(c) {
            closes.push(close);
        } else if closes.last() == Some(&c) {
            closes.pop();
        }
        if matches!(c, '\r' | '\n') && closes.is_empty() {
            if c == '\r' && i.remainder().starts_with('\n') {
                i.next();
            }
            let mut indent = 0;
            while matches!(i.remainder().chars().next(), Some(' ' | '\t')) {
                i.next();
                indent += 1;
            }
            if indent == 0 {
                return;
            }
        }
    }
}

pub(super) fn matching_close(c: char) -> Option<char> {
    match c {
        '(' => Some(')'),
        '[' => Some(']'),
        '{' => Some('}'),
        _ => None,
    }
}

fn opaque_region(i: LexIn) -> bool {
    crate::lexical::opaque_region::skip_literal(i)
}
