use serde::Serialize;

use crate::output::Diagnostic;

#[derive(Debug, Clone, Serialize)]
pub struct ColorizeOutput {
    pub ok: bool,
    pub spans: Vec<HighlightSpan>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Clone, Serialize)]
pub struct HighlightSpan {
    pub start: usize,
    pub end: usize,
    pub kind: HighlightKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum HighlightKind {
    Comment,
    Keyword,
    String,
    Number,
    Ident,
    Symbol,
}

pub fn colorize_source(source: &str) -> ColorizeOutput {
    let utf16_offsets = utf16_offsets_by_byte(source);
    let spans = SourceScanner::new(source, &utf16_offsets).scan();
    ColorizeOutput {
        ok: true,
        spans,
        diagnostics: Vec::new(),
    }
}

fn utf16_offsets_by_byte(source: &str) -> Vec<usize> {
    let mut offsets = vec![0; source.len() + 1];
    let mut utf16_offset = 0;
    for (byte_offset, ch) in source.char_indices() {
        offsets[byte_offset] = utf16_offset;
        utf16_offset += ch.len_utf16();
        let next_byte_offset = byte_offset + ch.len_utf8();
        for offset in &mut offsets[(byte_offset + 1)..=next_byte_offset] {
            *offset = utf16_offset;
        }
    }
    offsets
}

struct SourceScanner<'a> {
    source: &'a str,
    utf16_offsets: &'a [usize],
    cursor: usize,
    spans: Vec<HighlightSpan>,
}

impl<'a> SourceScanner<'a> {
    fn new(source: &'a str, utf16_offsets: &'a [usize]) -> Self {
        Self {
            source,
            utf16_offsets,
            cursor: 0,
            spans: Vec::new(),
        }
    }

    fn scan(mut self) -> Vec<HighlightSpan> {
        while self.cursor < self.source.len() {
            if self.scan_line_comment()
                || self.scan_block_comment()
                || self.scan_string()
                || self.scan_number()
                || self.scan_ident()
                || self.scan_symbol()
            {
                continue;
            }
            self.bump_char();
        }
        self.spans
    }

    fn scan_line_comment(&mut self) -> bool {
        if !self.rest().starts_with("//") {
            return false;
        }
        let start = self.cursor;
        self.cursor += 2;
        while let Some(ch) = self.current_char() {
            if ch == '\n' || ch == '\r' {
                break;
            }
            self.bump_char();
        }
        self.push(start, self.cursor, HighlightKind::Comment);
        true
    }

    fn scan_block_comment(&mut self) -> bool {
        if !self.rest().starts_with("/*") {
            return false;
        }
        let start = self.cursor;
        self.cursor += 2;
        let mut depth = 1;
        while self.cursor < self.source.len() {
            if self.rest().starts_with("/*") {
                self.cursor += 2;
                depth += 1;
            } else if self.rest().starts_with("*/") {
                self.cursor += 2;
                depth -= 1;
                if depth == 0 {
                    break;
                }
            } else {
                self.bump_char();
            }
        }
        self.push(start, self.cursor, HighlightKind::Comment);
        true
    }

    fn scan_string(&mut self) -> bool {
        let start = self.cursor;
        if self.rest().starts_with("r\"") || self.rest().starts_with("~\"") {
            self.cursor += 1;
        } else if !self.rest().starts_with('"') {
            return false;
        }
        self.cursor += 1;
        while let Some(ch) = self.current_char() {
            self.bump_char();
            if ch == '\\' {
                self.bump_char();
            } else if ch == '"' {
                break;
            }
        }
        self.push(start, self.cursor, HighlightKind::String);
        true
    }

    fn scan_number(&mut self) -> bool {
        let start = self.cursor;
        if self.current_char().is_some_and(|ch| ch.is_ascii_digit()) {
            self.consume_ascii_digits();
            if self.rest().starts_with('.')
                && !self.rest().starts_with("..")
                && self
                    .next_char_after(1)
                    .is_some_and(|ch| ch.is_ascii_digit())
            {
                self.cursor += 1;
                self.consume_ascii_digits();
            }
        } else if self.rest().starts_with('.')
            && self
                .next_char_after(1)
                .is_some_and(|ch| ch.is_ascii_digit())
        {
            self.cursor += 1;
            self.consume_ascii_digits();
        } else {
            return false;
        }

        if matches!(self.current_char(), Some('e' | 'E')) {
            let exp_start = self.cursor;
            self.bump_char();
            if matches!(self.current_char(), Some('+' | '-')) {
                self.bump_char();
            }
            if self.current_char().is_some_and(|ch| ch.is_ascii_digit()) {
                self.consume_ascii_digits();
            } else {
                self.cursor = exp_start;
            }
        }

        self.push(start, self.cursor, HighlightKind::Number);
        true
    }

    fn scan_ident(&mut self) -> bool {
        let start = self.cursor;
        if matches!(self.current_char(), Some('$' | '&' | '_' | '\'')) {
            self.bump_char();
            if !self.current_char().is_some_and(is_ident_start) {
                self.cursor = start;
                return false;
            }
        } else if !self.current_char().is_some_and(is_ident_start) {
            return false;
        }
        self.bump_char();
        while self.current_char().is_some_and(is_ident_continue) {
            self.bump_char();
        }
        let text = &self.source[start..self.cursor];
        let kind = if is_keyword(text) {
            HighlightKind::Keyword
        } else {
            HighlightKind::Ident
        };
        self.push(start, self.cursor, kind);
        true
    }

    fn scan_symbol(&mut self) -> bool {
        let start = self.cursor;
        for symbol in [
            "->", "::", "..", "<=", ">=", "==", "!=", "=>", "+", "-", "*", "/", "%", "<", ">", "=",
            ":", ";", ",", ".", "|", "\\", "'", "(", ")", "[", "]", "{", "}", "$", "&",
        ] {
            if self.rest().starts_with(symbol) {
                self.cursor += symbol.len();
                self.push(start, self.cursor, HighlightKind::Symbol);
                return true;
            }
        }
        false
    }

    fn consume_ascii_digits(&mut self) {
        while self.current_char().is_some_and(|ch| ch.is_ascii_digit()) {
            self.bump_char();
        }
    }

    fn push(&mut self, start: usize, end: usize, kind: HighlightKind) {
        if start == end {
            return;
        }
        self.spans.push(HighlightSpan {
            start: self.utf16_offsets[start],
            end: self.utf16_offsets[end],
            kind,
        });
    }

    fn bump_char(&mut self) {
        if let Some(ch) = self.current_char() {
            self.cursor += ch.len_utf8();
        }
    }

    fn current_char(&self) -> Option<char> {
        self.rest().chars().next()
    }

    fn next_char_after(&self, bytes: usize) -> Option<char> {
        self.source.get((self.cursor + bytes)..)?.chars().next()
    }

    fn rest(&self) -> &'a str {
        &self.source[self.cursor..]
    }
}

fn is_ident_start(ch: char) -> bool {
    ch == '_' || ch.is_alphabetic()
}

fn is_ident_continue(ch: char) -> bool {
    ch == '_' || ch.is_alphanumeric()
}

fn is_keyword(text: &str) -> bool {
    matches!(
        text,
        "act"
            | "as"
            | "case"
            | "catch"
            | "do"
            | "else"
            | "elsif"
            | "enum"
            | "false"
            | "for"
            | "if"
            | "impl"
            | "in"
            | "infix"
            | "mark"
            | "mod"
            | "my"
            | "nullfix"
            | "our"
            | "prefix"
            | "pub"
            | "role"
            | "rule"
            | "struct"
            | "suffix"
            | "true"
            | "type"
            | "use"
            | "via"
            | "where"
            | "with"
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn colorize_reports_source_positions_after_comments() {
        let source = "// ascii\nmy x = 1\n";
        let comment_end = source.find('\n').expect("line end");
        let my_byte_offset = source.find("my").expect("my keyword");

        let output = colorize_source(source);

        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Comment && span.start == 0 && span.end == comment_end
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Keyword
                && span.start == my_byte_offset
                && span.end == my_byte_offset + "my".len()
        }));
    }

    #[test]
    fn colorize_reports_utf16_offsets() {
        let source = "my s = \"日本語\"\nmy x = 1\n";
        let my_byte_offset = source.rfind("my").expect("my keyword");
        let my_utf16_offset = source[..my_byte_offset].encode_utf16().count();

        let output = colorize_source(source);

        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Keyword
                && span.start == my_utf16_offset
                && span.end == my_utf16_offset + "my".len()
        }));
    }
}
