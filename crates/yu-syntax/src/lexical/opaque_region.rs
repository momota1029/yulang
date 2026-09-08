//! Lexical continuation of an already accepted opaque recovery opener.

use reborrow_generic::Reborrow as _;

use super::{
    current_item::LineEntry,
    item::{ForeignSplit, Item, LeadingTrivia, Payload, PendingBoundary, PendingFragments},
    yumark::{FenceBoundary, FenceLineDecision, judge_fence_line},
};
use crate::{cursor::LexIn, syntax_kind::SyntaxKind};

pub(crate) struct OpaqueRegion {
    pub(crate) length: usize,
    pub(crate) boundary: Option<Item>,
    pub(crate) line: LineEntry,
    fragments: Option<PendingFragments>,
}

impl OpaqueRegion {
    pub(crate) fn visit_segments(
        &self,
        text: &str,
        origin: usize,
        mut visit: impl FnMut(&str, std::ops::Range<usize>, SyntaxKind),
    ) {
        assert_eq!(text.len(), self.length);
        if let Some(fragments) = &self.fragments {
            fragments.visit_segments(text, visit);
        } else if !text.is_empty() {
            visit(text, origin..origin + text.len(), SyntaxKind::Unknown);
        }
    }
}

pub(crate) fn finish_opaque_opener(
    mut i: LexIn,
    opener: &str,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> OpaqueRegion {
    let mut scan = Scan {
        origin,
        initial_len: i.remainder().len(),
        fence,
        foreign: None,
        pending: None,
        line: LineEntry::InLine,
    };
    if opener == "~\"" {
        while let Some(c) = scan.next(i.rb()) {
            if c == '"' {
                break;
            }
            if c == '{' {
                scan.code(i.rb(), '}');
            }
        }
    } else if !opener.is_empty() && opener.chars().all(|c| c == '"') {
        scan.string(i.rb(), opener.len());
    } else if opener == "'[" || opener == "'{" {
        scan.yumark(i.rb(), if opener == "'[" { ']' } else { '}' });
    } else if opener == "'" && matches!(i.remainder().chars().next(), Some('[' | '{')) {
        let close = matching_close(scan.next(i.rb()).unwrap()).unwrap();
        scan.yumark(i.rb(), close);
    }
    scan.ready(i.rb());
    let length = scan.initial_len - i.remainder().len();
    OpaqueRegion {
        length,
        boundary: scan
            .pending
            .map(|pending| Item::plain(LeadingTrivia::default(), Payload::Boundary(pending))),
        line: scan.line,
        fragments: PendingFragments::finish(scan.foreign, origin, length)
            .expect("opaque region owns ordered source-backed prefix splits"),
    }
}

struct Scan<'f> {
    origin: usize,
    initial_len: usize,
    fence: Option<&'f FenceBoundary>,
    foreign: Option<Vec<ForeignSplit>>,
    pending: Option<PendingBoundary>,
    line: LineEntry,
}

impl Scan<'_> {
    fn ready(&mut self, mut i: LexIn) -> bool {
        if self.pending.is_some() {
            return false;
        }
        if let Some(fence) = self.fence
            && (self.line == LineEntry::PhysicalStart || i.remainder().is_empty())
        {
            let origin = self.origin + self.initial_len - i.remainder().len();
            match judge_fence_line(i.remainder(), origin, fence) {
                FenceLineDecision::Boundary(pending) => {
                    self.line = if i.remainder().is_empty() {
                        LineEntry::InLine
                    } else {
                        LineEntry::PhysicalStart
                    };
                    self.pending = Some(pending);
                    return false;
                }
                FenceLineDecision::Body {
                    prefix: Some(_),
                    content,
                } => {
                    let length = content - origin;
                    let remaining = i.remainder().len() - length;
                    while i.remainder().len() > remaining {
                        i.next();
                    }
                    PendingFragments::record(
                        &mut self.foreign,
                        ForeignSplit::quote_prefix(origin, length),
                    )
                    .expect("judged prefix is ordered");
                }
                FenceLineDecision::Body { prefix: None, .. } => {}
            }
            self.line = LineEntry::InLine;
        }
        !i.remainder().is_empty()
    }

    fn next(&mut self, mut i: LexIn) -> Option<char> {
        if !self.ready(i.rb()) {
            return None;
        }
        let c = i.next()?;
        if self.fence.is_some() && c == '\r' && i.remainder().starts_with('\n') {
            i.next();
            self.line = LineEntry::PhysicalStart;
            self.ready(i);
            return Some('\n');
        }
        self.line = if c == '\n' {
            LineEntry::PhysicalStart
        } else {
            LineEntry::InLine
        };
        if self.line == LineEntry::PhysicalStart {
            self.ready(i);
        }
        Some(c)
    }

    fn take(&mut self, mut i: LexIn, count: usize) {
        for _ in 0..count {
            if self.next(i.rb()).is_none() {
                break;
            }
        }
    }

    fn opaque(&mut self, mut i: LexIn) -> bool {
        if !self.ready(i.rb()) {
            return false;
        }
        if i.remainder().starts_with("//") {
            while self.ready(i.rb()) && !matches!(i.remainder().chars().next(), Some('\r' | '\n')) {
                self.next(i.rb());
            }
        } else if i.remainder().starts_with("/*") {
            self.take(i.rb(), 2);
            let mut depth = 1;
            while depth > 0 && self.ready(i.rb()) {
                if i.remainder().starts_with("/*") {
                    self.take(i.rb(), 2);
                    depth += 1;
                } else if i.remainder().starts_with("*/") {
                    self.take(i.rb(), 2);
                    depth -= 1;
                } else {
                    self.next(i.rb());
                }
            }
        } else if i.remainder().starts_with("'[") || i.remainder().starts_with("'{") {
            self.next(i.rb());
            let close = matching_close(self.next(i.rb()).unwrap()).unwrap();
            self.yumark(i, close);
        } else if i.remainder().starts_with("~\"") {
            self.take(i.rb(), 2);
            while let Some(c) = self.next(i.rb()) {
                if c == '"' {
                    break;
                }
                if c == '{' {
                    self.code(i.rb(), '}');
                }
            }
        } else if i.remainder().starts_with('"') {
            let quotes = i.remainder().bytes().take_while(|c| *c == b'"').count();
            let count = if quotes >= 3 { quotes } else { 1 };
            self.take(i.rb(), count);
            self.string(i, count);
        } else {
            return false;
        }
        true
    }

    fn string(&mut self, mut i: LexIn, count: usize) {
        while self.ready(i.rb()) {
            if i.remainder().starts_with('"') {
                let run = i.remainder().bytes().take_while(|c| *c == b'"').count();
                self.take(i.rb(), if count == 1 { 1 } else { run });
                if count == 1 || run == count {
                    break;
                }
                continue;
            }
            match self.next(i.rb()).unwrap() {
                '\\' => {
                    self.next(i.rb());
                }
                '%' => {
                    while let Some(c) = self.next(i.rb()) {
                        if c == '{' {
                            self.code(i.rb(), '}');
                            break;
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn code(&mut self, mut i: LexIn, close: char) {
        let mut closes = vec![close];
        while self.ready(i.rb()) {
            if self.opaque(i.rb()) {
                continue;
            }
            let Some(c) = self.next(i.rb()) else {
                break;
            };
            if closes.last() == Some(&c) {
                closes.pop();
                if closes.is_empty() {
                    break;
                }
            } else if let Some(close) = matching_close(c) {
                closes.push(close);
            }
        }
    }

    fn yumark(&mut self, mut i: LexIn, close: char) {
        let mut closes = vec![close];
        let mut line_start = close == '}';
        while self.ready(i.rb()) {
            if line_start && close == '}' {
                while self.ready(i.rb()) && matches!(i.remainder().chars().next(), Some(' ' | '\t'))
                {
                    self.next(i.rb());
                }
                let mut depth = 0;
                while self.ready(i.rb()) && i.remainder().starts_with('>') {
                    self.next(i.rb());
                    depth += 1;
                    if matches!(i.remainder().chars().next(), Some(' ' | '\t')) {
                        self.next(i.rb());
                    }
                }
                if self.ready(i.rb()) && i.remainder().starts_with("```") {
                    self.nested_fence(i.rb(), depth);
                }
            }
            let Some(c) = self.next(i.rb()) else {
                break;
            };
            line_start = matches!(c, '\r' | '\n');
            if closes.last() == Some(&c) {
                closes.pop();
                if closes.is_empty() {
                    break;
                }
            } else if let Some(close) = matching_close(c) {
                closes.push(close);
            }
        }
    }

    fn nested_fence(&mut self, mut i: LexIn, depth: usize) {
        self.take(i.rb(), 3);
        let yulang = i.remainder().starts_with("yulang");
        while let Some(c) = self.next(i.rb()) {
            if matches!(c, '\r' | '\n') {
                break;
            }
        }
        let mut line_start = true;
        while self.ready(i.rb()) {
            if line_start {
                while self.ready(i.rb()) && matches!(i.remainder().chars().next(), Some(' ' | '\t'))
                {
                    self.next(i.rb());
                }
                let mut matched = true;
                for _ in 0..depth {
                    if !i.remainder().starts_with('>') {
                        matched = false;
                        break;
                    }
                    self.next(i.rb());
                    if matches!(i.remainder().chars().next(), Some(' ' | '\t')) {
                        self.next(i.rb());
                    }
                }
                if self.ready(i.rb()) && matched && i.remainder().starts_with("```") {
                    self.take(i, 3);
                    return;
                }
            }
            if yulang && self.opaque(i.rb()) {
                line_start = false;
                continue;
            }
            line_start = self.next(i.rb()).is_some_and(|c| matches!(c, '\r' | '\n'));
        }
    }
}

fn matching_close(c: char) -> Option<char> {
    match c {
        '(' => Some(')'),
        '[' => Some(']'),
        '{' => Some('}'),
        _ => None,
    }
}
