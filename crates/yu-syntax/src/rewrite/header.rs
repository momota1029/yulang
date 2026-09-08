//! Source-leading header discovery using the same owners as full construction.

use std::{ops::Range, sync::Arc};

use chasa_recover::In;
use reborrow_generic::Reborrow as _;

use crate::{
    HeaderCoverage, HeaderImport, HeaderInfo, HeaderOperator, HeaderStop, OperatorTable,
    SourceText, session::CommittedRecoveryRecord, syntax_kind::SyntaxKind,
};

use super::{
    LexIn,
    current_item::LineEntry,
    driver::{Either, NormalizedExit},
    item::Item,
    operator_header,
    output::RewriteOutput,
    state::Recover,
    use_decl,
};

pub(crate) struct HeaderDiscovery {
    pub(crate) coverage: Range<usize>,
    pub(crate) stop: HeaderStop,
    pub(crate) imports: Vec<HeaderImport>,
    pub(crate) operators: Vec<HeaderOperator>,
    pub(crate) recoveries: Vec<CommittedRecoveryRecord>,
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
    discover_header_with_frozen(source, None)
}

pub(super) fn discover_header_with_frozen(
    source: &str,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> HeaderDiscovery {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut output = frozen.map_or_else(RewriteOutput::new, RewriteOutput::reconcile_scoped);
    output.start_node(SyntaxKind::Root.into());
    let mut remaining = source;
    let mut origin = 0;
    let mut line = LineEntry::PhysicalStart;
    let mut pending = None;
    let mut imports = Vec::new();
    let mut facts = Vec::new();
    let (coverage_end, stop) = loop {
        let entered_at_start = line == LineEntry::PhysicalStart;
        let mut i: super::RewriteIn = In::new(&mut remaining, &mut recover, &mut output);
        let mut item = pending.take().unwrap_or_else(|| {
            i.token(|lex| {
                Some(use_decl::next_use_item_lex(
                    lex,
                    &mut origin,
                    &mut line,
                    None,
                ))
            })
            .unwrap()
        });
        let leading_newline = item.leading_view().contains_line_break();
        let indentation = super::driver::indentation_after_newline(item.leading_view());
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
        let is_use = use_decl::use_declaration_selected_normalized(i.rb(), &item, origin, None);
        let is_operator = !is_use
            && i.rb()
                .map(
                    |lex: LexIn| Some(operator_selected(lex, &item, origin)),
                    |x| x,
                )
                .unwrap();
        if !is_use && !is_operator {
            break (start, HeaderStop::FirstNonHeader);
        }
        drop(i);
        if is_use {
            let (exit, batch) = {
                let mut scope = output.header_reconciliation_scope();
                use_decl::use_declaration_header_normalized(
                    In::new(&mut remaining, &mut recover, &mut *scope),
                    item,
                    0,
                    0,
                    origin,
                    line,
                    None,
                )
            };
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
            let (item, next_origin, next_line, fact) = {
                let mut scope = output.header_reconciliation_scope();
                operator_header::operator_header_normalized(
                    In::new(&mut remaining, &mut recover, &mut *scope),
                    item,
                    origin,
                    line,
                    None,
                )
            };
            origin = next_origin;
            line = next_line;
            if let Some(fact) = fact {
                facts.push(fact);
            }
            pending = item;
            if pending.is_none() {
                let mut i: super::RewriteIn = In::new(&mut remaining, &mut recover, &mut output);
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
    let (_, recoveries) = output.finish_with_recoveries();
    HeaderDiscovery {
        coverage: 0..coverage_end,
        stop,
        imports,
        operators: facts,
        recoveries,
    }
}

pub(super) fn operator_selected(mut i: LexIn, item: &Item, origin: usize) -> bool {
    // Statement intro rule 3 reserves `my <word> =` for Binding before
    // interpreting the word as an explicit-private operator modifier.
    if item.payload_view().spelling() == Some("my")
        && super::binding::binding_statement_selected_lexical(i.remainder(), item, 0, origin, None)
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
                let item = use_decl::next_use_item_lex(lex.rb(), &mut position, &mut line, None);
                if item.leading_view().is_grammar_empty()
                    || item.leading_view().contains_line_break()
                {
                    return None;
                }
                word = item.payload_view().spelling().unwrap_or("").to_owned();
            }
            if word == "lazy" {
                let item = use_decl::next_use_item_lex(lex, &mut position, &mut line, None);
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

fn opaque_region(mut i: LexIn) -> bool {
    if i.remainder().starts_with("//") {
        while !matches!(i.remainder().chars().next(), None | Some('\r' | '\n')) {
            i.next();
        }
        return true;
    }
    if i.remainder().starts_with("/*") {
        take(&mut i, 2);
        let mut depth = 1;
        while depth > 0 && !i.remainder().is_empty() {
            if i.remainder().starts_with("/*") {
                take(&mut i, 2);
                depth += 1;
            } else if i.remainder().starts_with("*/") {
                take(&mut i, 2);
                depth -= 1;
            } else {
                i.next();
            }
        }
        return true;
    }
    if i.remainder().starts_with("'[") || i.remainder().starts_with("'{") {
        i.next();
        let close = matching_close(i.next().unwrap()).unwrap();
        yumark_region(i, close);
        return true;
    }
    if i.remainder().starts_with("~\"") {
        take(&mut i, 2);
        finish_opaque_opener(i, "~\"");
        return true;
    }
    if i.remainder().starts_with('"') {
        let quotes = i.remainder().chars().take_while(|c| *c == '"').count();
        let count = if quotes >= 3 { quotes } else { 1 };
        take(&mut i, count);
        string_region(i, count);
        return true;
    }
    false
}

/// Continue an opaque region whose opener is the already-owned current Item.
pub(super) fn finish_opaque_opener(mut i: LexIn, opener: &str) -> bool {
    if opener == "~\"" {
        while let Some(c) = i.next() {
            if c == '"' {
                break;
            }
            if c == '{' {
                code_region(i.rb(), '}');
            }
        }
    } else if !opener.is_empty() && opener.chars().all(|c| c == '"') {
        string_region(i, opener.len());
    } else if opener == "'[" || opener == "'{" {
        yumark_region(i, if opener == "'[" { ']' } else { '}' });
    } else if opener == "'" && matches!(i.remainder().chars().next(), Some('[' | '{')) {
        let close = matching_close(i.next().unwrap()).unwrap();
        yumark_region(i, close);
    } else {
        return false;
    }
    true
}

fn string_region(mut i: LexIn, count: usize) {
    while !i.remainder().is_empty() {
        if i.remainder().starts_with('"') {
            let run = i.remainder().chars().take_while(|c| *c == '"').count();
            take(&mut i, if count == 1 { 1 } else { run });
            if count == 1 || run == count {
                break;
            }
            continue;
        }
        match i.next().unwrap() {
            '\\' => {
                i.next();
            }
            '%' => {
                while let Some(c) = i.next() {
                    if c == '{' {
                        code_region(i.rb(), '}');
                        break;
                    }
                }
            }
            _ => {}
        }
    }
}

pub(super) fn code_region(mut i: LexIn, close: char) {
    let mut closes = vec![close];
    while !i.remainder().is_empty() {
        if opaque_region(i.rb()) {
            continue;
        }
        let c = i.next().unwrap();
        if closes.last() == Some(&c) {
            closes.pop();
            if closes.is_empty() {
                return;
            }
        } else if let Some(close) = matching_close(c) {
            closes.push(close);
        }
    }
}

pub(super) fn yumark_region(mut i: LexIn, close: char) {
    let mut closes = vec![close];
    let mut line_start = close == '}';
    while !i.remainder().is_empty() {
        if line_start && close == '}' {
            while matches!(i.remainder().chars().next(), Some(' ' | '\t')) {
                i.next();
            }
            let mut quote_depth = 0;
            while i.remainder().starts_with('>') {
                i.next();
                quote_depth += 1;
                if matches!(i.remainder().chars().next(), Some(' ' | '\t')) {
                    i.next();
                }
            }
            if i.remainder().starts_with("```") {
                fence_region(i.rb(), quote_depth);
            }
        }
        let Some(c) = i.next() else {
            return;
        };
        line_start = matches!(c, '\r' | '\n');
        if closes.last() == Some(&c) {
            closes.pop();
            if closes.is_empty() {
                return;
            }
        } else if let Some(close) = matching_close(c) {
            closes.push(close);
        }
    }
}

fn fence_region(mut i: LexIn, quote_depth: usize) {
    take(&mut i, 3);
    let yulang = i.remainder().starts_with("yulang");
    while let Some(c) = i.next() {
        if matches!(c, '\r' | '\n') {
            break;
        }
    }
    let mut line_start = true;
    while !i.remainder().is_empty() {
        if line_start {
            while matches!(i.remainder().chars().next(), Some(' ' | '\t')) {
                i.next();
            }
            let mut matched = true;
            for _ in 0..quote_depth {
                if !i.remainder().starts_with('>') {
                    matched = false;
                    break;
                }
                i.next();
                if matches!(i.remainder().chars().next(), Some(' ' | '\t')) {
                    i.next();
                }
            }
            if matched && i.remainder().starts_with("```") {
                take(&mut i, 3);
                return;
            }
        }
        if yulang && opaque_region(i.rb()) {
            line_start = false;
            continue;
        }
        line_start = i.next().is_some_and(|c| matches!(c, '\r' | '\n'));
    }
}

fn take(i: &mut LexIn, count: usize) {
    for _ in 0..count {
        i.next();
    }
}
