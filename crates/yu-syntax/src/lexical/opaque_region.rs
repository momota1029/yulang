//! Lexical continuation of an already accepted opaque recovery opener.

use reborrow_generic::Reborrow as _;

use super::{
    current_item::LineEntry,
    item::{ForeignSplit, Item, LeadingTrivia, Payload, PendingBoundary, PendingFragments},
    yumark::{FenceBoundary, FenceLineDecision, judge_fence_line},
};
use crate::cursor::LexIn;

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
        mut visit: impl FnMut(&str, std::ops::Range<usize>),
    ) {
        assert_eq!(text.len(), self.length);
        if let Some(fragments) = &self.fragments {
            fragments.visit_segments(text, visit);
        } else if !text.is_empty() {
            visit(text, origin..origin + text.len());
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
        let mut frames = Vec::new();
        if !self.open_opaque(i.rb(), &mut frames) {
            return false;
        }
        self.drive(i, frames);
        true
    }

    // The opaque scanner is used before grammar guards (source matching) and
    // inside recovery. String interpolation / code / Yumark / fence cycles
    // therefore use explicit frames instead of the native stack.
    fn open_opaque(&mut self, mut i: LexIn, frames: &mut Vec<OpaqueFrame>) -> bool {
        if !self.ready(i.rb()) {
            return false;
        }
        if i.remainder().starts_with("//") {
            while self.ready(i.rb()) && !matches!(i.remainder().chars().next(), Some('\r' | '\n')) {
                self.next(i.rb());
            }
        } else if i.remainder().starts_with("/*") {
            self.take(i.rb(), 2);
            let mut depth = 1usize;
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
            frames.push(OpaqueFrame::Yumark {
                close,
                closes: vec![close],
                line_start: close == '}',
            });
        } else if i.remainder().starts_with("~\"") {
            self.take(i.rb(), 2);
            frames.push(OpaqueFrame::RuleString);
        } else if i.remainder().starts_with('"') {
            let quotes = i.remainder().bytes().take_while(|c| *c == b'"').count();
            let count = if quotes >= 3 { quotes } else { 1 };
            self.take(i.rb(), count);
            frames.push(OpaqueFrame::String(count));
        } else {
            return false;
        }
        true
    }

    fn string(&mut self, i: LexIn, count: usize) {
        self.drive(i, vec![OpaqueFrame::String(count)]);
    }
    fn code(&mut self, i: LexIn, close: char) {
        self.drive(i, vec![OpaqueFrame::Code(vec![close])]);
    }
    fn yumark(&mut self, i: LexIn, close: char) {
        self.drive(
            i,
            vec![OpaqueFrame::Yumark {
                close,
                closes: vec![close],
                line_start: close == '}',
            }],
        );
    }
    fn nested_fence(&mut self, mut i: LexIn, depth: usize) {
        let frame = self.open_fence(i.rb(), depth);
        self.drive(i, vec![frame]);
    }
    fn open_fence(&mut self, mut i: LexIn, depth: usize) -> OpaqueFrame {
        self.take(i.rb(), 3);
        let yulang = i.remainder().starts_with("yulang");
        while let Some(c) = self.next(i.rb()) {
            if matches!(c, '\r' | '\n') {
                break;
            }
        }
        OpaqueFrame::Fence {
            depth,
            yulang,
            line_start: true,
        }
    }

    fn drive(&mut self, mut i: LexIn, mut frames: Vec<OpaqueFrame>) {
        while self.ready(i.rb()) {
            let Some(frame) = frames.pop() else {
                break;
            };
            match frame {
                OpaqueFrame::RuleString => match self.next(i.rb()) {
                    Some('"') | None => {}
                    Some('{') => {
                        frames.push(OpaqueFrame::RuleString);
                        frames.push(OpaqueFrame::Code(vec!['}']));
                    }
                    _ => frames.push(OpaqueFrame::RuleString),
                },
                OpaqueFrame::String(count) => {
                    if i.remainder().starts_with('"') {
                        let run = i.remainder().bytes().take_while(|c| *c == b'"').count();
                        self.take(i.rb(), if count == 1 { 1 } else { run });
                        if count != 1 && run != count {
                            frames.push(OpaqueFrame::String(count));
                        }
                    } else {
                        let c = self.next(i.rb()).unwrap();
                        if c == '\\' {
                            self.next(i.rb());
                        }
                        frames.push(OpaqueFrame::String(count));
                        if c == '%' {
                            while let Some(c) = self.next(i.rb()) {
                                if c == '{' {
                                    frames.push(OpaqueFrame::Code(vec!['}']));
                                    break;
                                }
                            }
                        }
                    }
                }
                OpaqueFrame::Code(mut closes) => {
                    // Leave the parent frame in place while an opaque child runs.
                    let parent = frames.len();
                    frames.push(OpaqueFrame::Code(Vec::new()));
                    if self.open_opaque(i.rb(), &mut frames) {
                        frames[parent] = OpaqueFrame::Code(closes);
                        continue;
                    }
                    frames.pop();
                    let Some(c) = self.next(i.rb()) else {
                        break;
                    };
                    if closes.last() == Some(&c) {
                        closes.pop();
                    } else if let Some(close) = matching_close(c) {
                        closes.push(close);
                    }
                    if !closes.is_empty() {
                        frames.push(OpaqueFrame::Code(closes));
                    }
                }
                OpaqueFrame::Yumark {
                    close,
                    mut closes,
                    mut line_start,
                } => {
                    if line_start && close == '}' {
                        while self.ready(i.rb())
                            && matches!(i.remainder().chars().next(), Some(' ' | '\t'))
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
                            frames.push(OpaqueFrame::YumarkAfterFence { close, closes });
                            frames.push(self.open_fence(i.rb(), depth));
                            continue;
                        }
                    }
                    let Some(c) = self.next(i.rb()) else {
                        break;
                    };
                    line_start = matches!(c, '\r' | '\n');
                    if closes.last() == Some(&c) {
                        closes.pop();
                    } else if let Some(close) = matching_close(c) {
                        closes.push(close);
                    }
                    if !closes.is_empty() {
                        frames.push(OpaqueFrame::Yumark {
                            close,
                            closes,
                            line_start,
                        });
                    }
                }
                OpaqueFrame::YumarkAfterFence { close, mut closes } => {
                    let Some(c) = self.next(i.rb()) else {
                        break;
                    };
                    if closes.last() == Some(&c) {
                        closes.pop();
                    } else if let Some(close) = matching_close(c) {
                        closes.push(close);
                    }
                    if !closes.is_empty() {
                        frames.push(OpaqueFrame::Yumark {
                            close,
                            closes,
                            line_start: matches!(c, '\r' | '\n'),
                        });
                    }
                }
                OpaqueFrame::Fence {
                    depth,
                    yulang,
                    mut line_start,
                } => {
                    if line_start {
                        while self.ready(i.rb())
                            && matches!(i.remainder().chars().next(), Some(' ' | '\t'))
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
                            self.take(i.rb(), 3);
                            continue;
                        }
                    }
                    if yulang {
                        let parent = frames.len();
                        frames.push(OpaqueFrame::Fence {
                            depth,
                            yulang,
                            line_start: false,
                        });
                        if self.open_opaque(i.rb(), &mut frames) {
                            continue;
                        }
                        frames.truncate(parent);
                    }
                    line_start = self.next(i.rb()).is_some_and(|c| matches!(c, '\r' | '\n'));
                    frames.push(OpaqueFrame::Fence {
                        depth,
                        yulang,
                        line_start,
                    });
                }
            }
        }
    }
}

// Continuations of the source-backed scanner; none owns syntax output.
enum OpaqueFrame {
    String(usize),
    RuleString,
    Code(Vec<char>),
    Yumark {
        close: char,
        closes: Vec<char>,
        line_start: bool,
    },
    YumarkAfterFence {
        close: char,
        closes: Vec<char>,
    },
    Fence {
        depth: usize,
        yulang: bool,
        line_start: bool,
    },
}

fn matching_close(c: char) -> Option<char> {
    match c {
        '(' => Some(')'),
        '[' => Some(']'),
        '{' => Some('}'),
        _ => None,
    }
}

/// Source matching reuses the committed lexer's opaque-body scanner. It does
/// not tokenize or build a second literal/comment grammar.
pub(crate) fn skip_source_opaque(mut i: LexIn, origin: usize, line_indent: Option<usize>) -> bool {
    let mut scan = Scan {
        origin,
        initial_len: i.remainder().len(),
        fence: None,
        foreign: None,
        pending: None,
        line: LineEntry::InLine,
    };
    if scan.opaque(i.rb()) {
        return true;
    }
    if let Some(("rule", suffix)) = super::lexer::source_identifier(i.remainder()) {
        use super::trivia::{TriviaObservation, observe_logical_fenced_trivia};
        if let TriviaObservation::Visible(visible) =
            observe_logical_fenced_trivia(suffix, 0, LineEntry::InLine, None)
            && visible.source.starts_with('{')
        {
            let length = i.remainder().len() - visible.source.len() + 1;
            let end = i.remainder().len() - length;
            while i.remainder().len() > end {
                scan.next(i.rb());
            }
            scan.code(i, '}');
            return true;
        }
    }
    use crate::yumark::judge::{
        ActiveClose, BlockCloseContext, BlockCloseDecision, ChunkContext, ChunkKind,
        DocumentMarkerKind, StatementPosition, judge_block_close, judge_chunk,
        judge_document_marker, judge_line_document,
    };
    let position = match line_indent {
        Some(base_col) => StatementPosition::CanonicalLineStart { base_col },
        None if i.recovery().operators().definition("--").is_none() => {
            StatementPosition::CanonicalSameLine
        }
        None => return false,
    };
    let Some(marker) = judge_document_marker(i.remainder(), origin, position) else {
        return false;
    };
    if marker.kind == DocumentMarkerKind::Line {
        let extent = judge_line_document(i.remainder(), origin).unwrap();
        let end = i.remainder().len() - (extent.end.start - origin);
        while i.remainder().len() > end {
            scan.next(i.rb());
        }
        return true;
    }
    let base_col = line_indent.unwrap();
    while let Some(ch) = scan.next(i.rb()) {
        if ch == '\n' {
            break;
        }
    }
    while scan.ready(i.rb()) {
        let mut indent = 0;
        while i.remainder().starts_with([' ', '\t']) {
            scan.next(i.rb());
            indent += 1;
        }
        if matches!(
            judge_block_close(
                i.remainder(),
                0,
                BlockCloseContext {
                    after_opening_line: true,
                    at_physical_line_start: true,
                    indent_col: indent,
                    base_col,
                }
            ),
            BlockCloseDecision::Close(_)
        ) {
            scan.take(i, 3);
            return true;
        }
        let chunk = judge_chunk(
            i.remainder(),
            0,
            ChunkContext {
                at_line_start: true,
                indent_col: indent,
                base_col,
                active_close: Some(ActiveClose::BlockDocument {
                    after_opening_line: true,
                }),
            },
        );
        if chunk.kind == ChunkKind::RawFence {
            scan.nested_fence(i.rb(), 0);
        }
        while let Some(ch) = scan.next(i.rb()) {
            if ch == '\n' {
                break;
            }
        }
    }
    true
}

/// Header body scanning shares the same iterative literal/comment owner, but
/// does not enable source-matching's rule/document recognition.
pub(crate) fn skip_literal(i: LexIn) -> bool {
    let mut scan = Scan {
        origin: 0,
        initial_len: i.remainder().len(),
        fence: None,
        foreign: None,
        pending: None,
        line: LineEntry::InLine,
    };
    scan.opaque(i)
}
