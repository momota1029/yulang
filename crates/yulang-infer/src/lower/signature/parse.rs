use rowan::{TextRange, TextSize};

use super::{SigRecordField, SigRow, SigType, SigVar};
use crate::lower::SyntaxNode;
use crate::symbols::{Name, Path};

pub struct SigParser<'a> {
    chars: &'a [u8],
    base: TextSize,
    i: usize,
}

impl<'a> SigParser<'a> {
    pub fn new(text: &'a str, base: TextSize) -> Self {
        Self {
            chars: text.as_bytes(),
            base,
            i: 0,
        }
    }

    pub fn parse_type(&mut self) -> Option<SigType> {
        self.skip_ws();
        let start = self.i;
        let lhs = self.parse_apply()?;
        self.skip_ws();
        if self.consume_str("->") {
            let ret_eff = self.parse_row_if_present();
            let rhs = self.parse_type()?;
            let span = self.range(start, self.offset_of(rhs.span().end()));
            Some(SigType::Fun {
                arg: Box::new(lhs),
                ret_eff,
                ret: Box::new(rhs),
                span,
            })
        } else {
            Some(lhs)
        }
    }

    pub fn is_eof(&mut self) -> bool {
        self.skip_ws();
        self.peek().is_none()
    }

    fn parse_apply(&mut self) -> Option<SigType> {
        let base = self.parse_atom()?;
        let mut args = Vec::new();
        loop {
            self.skip_ws();
            match self.peek() {
                Some(b'\'') | Some(b'(') => args.push(self.parse_atom()?),
                Some(ch) if is_ident_start(ch) => args.push(self.parse_atom()?),
                _ => break,
            }
        }
        if args.is_empty() {
            Some(base)
        } else if let SigType::Prim { path, span } = base {
            let end = args
                .last()
                .map(|arg| arg.span().end())
                .unwrap_or(span.end());
            Some(SigType::Apply {
                path,
                args,
                span: TextRange::new(span.start(), end),
            })
        } else {
            Some(base)
        }
    }

    fn parse_atom(&mut self) -> Option<SigType> {
        self.skip_ws();
        let start = self.i;
        if self.consume_str("()") {
            return Some(SigType::Unit {
                span: self.range(start, self.i),
            });
        }
        if self.peek()? == b'{' {
            return self.parse_record();
        }
        if self.consume_byte(b'(') {
            let first = self.parse_type()?;
            self.skip_ws();
            if self.consume_byte(b',') {
                let mut items = vec![first];
                loop {
                    self.skip_ws();
                    if self.consume_byte(b')') {
                        break;
                    }
                    items.push(self.parse_type()?);
                    self.skip_ws();
                    if self.consume_byte(b',') {
                        continue;
                    }
                    if self.consume_byte(b')') {
                        break;
                    }
                    return None;
                }
                return Some(SigType::Tuple {
                    items,
                    span: self.range(start, self.i),
                });
            }
            self.consume_byte(b')');
            return Some(first);
        }
        if self.peek()? == b'\'' {
            self.i += 1;
            let name = self.parse_ident()?;
            return Some(SigType::Var(SigVar {
                name,
                span: self.range(start, self.i),
            }));
        }
        if self.peek()? == b'_' {
            self.i += 1;
            return Some(SigType::Var(SigVar {
                name: "_".to_string(),
                span: self.range(start, self.i),
            }));
        }
        let (path, span) = self.parse_path()?;
        Some(SigType::Prim { path, span })
    }

    fn parse_record(&mut self) -> Option<SigType> {
        let start = self.i;
        self.consume_byte(b'{');
        self.skip_ws();
        if self.consume_byte(b'}') {
            return Some(SigType::Record {
                fields: Vec::new(),
                span: self.range(start, self.i),
            });
        }
        if self.consume_str("..") {
            let tail = self.parse_type()?;
            let mut fields = Vec::new();
            self.skip_ws();
            if self.consume_byte(b',') {
                loop {
                    self.skip_ws();
                    if self.consume_byte(b'}') {
                        break;
                    }
                    fields.push(self.parse_record_field()?);
                    self.skip_ws();
                    if self.consume_byte(b',') {
                        continue;
                    }
                    if self.consume_byte(b'}') {
                        break;
                    }
                    return None;
                }
            } else if !self.consume_byte(b'}') {
                return None;
            }
            return Some(SigType::RecordHeadSpread {
                tail: Box::new(tail),
                fields,
                span: self.range(start, self.i),
            });
        }
        let mut fields = Vec::new();
        loop {
            self.skip_ws();
            if self.consume_byte(b'}') {
                break;
            }
            if self.consume_str("..") {
                let tail = self.parse_type()?;
                self.skip_ws();
                if self.consume_byte(b',') {
                    self.skip_ws();
                }
                if !self.consume_byte(b'}') {
                    return None;
                }
                return Some(SigType::RecordTailSpread {
                    fields,
                    tail: Box::new(tail),
                    span: self.range(start, self.i),
                });
            }
            fields.push(self.parse_record_field()?);
            self.skip_ws();
            if self.consume_byte(b',') {
                continue;
            }
            if self.consume_byte(b'}') {
                break;
            }
            return None;
        }
        Some(SigType::Record {
            fields,
            span: self.range(start, self.i),
        })
    }

    fn parse_record_field(&mut self) -> Option<SigRecordField> {
        let name = Name(self.parse_ident()?);
        let optional = self.consume_byte(b'?');
        if !self.consume_byte(b':') {
            return None;
        }
        let ty = self.parse_type()?;
        Some(SigRecordField { name, ty, optional })
    }

    fn parse_row_if_present(&mut self) -> Option<SigRow> {
        self.skip_ws();
        if self.peek()? != b'[' {
            return None;
        }
        self.i += 1;
        let mut before_sep = Vec::new();
        let mut tail = None;
        let mut seen_sep = false;

        loop {
            self.skip_ws();
            match self.peek()? {
                b']' => {
                    self.i += 1;
                    break;
                }
                b';' => {
                    seen_sep = true;
                    self.i += 1;
                }
                b',' => {
                    self.i += 1;
                }
                _ => {
                    let ty = self.parse_type()?;
                    if seen_sep {
                        if let SigType::Var(var) = ty {
                            tail = Some(var);
                        }
                    } else {
                        before_sep.push(ty);
                    }
                }
            }
        }

        if !seen_sep && before_sep.len() == 1 {
            if let SigType::Var(var) = before_sep[0].clone() {
                return Some(SigRow {
                    items: vec![],
                    tail: Some(var),
                });
            }
        }
        Some(SigRow {
            items: before_sep,
            tail,
        })
    }

    fn parse_path(&mut self) -> Option<(Path, TextRange)> {
        let start = self.i;
        let mut segments = vec![Name(self.parse_ident()?)];
        loop {
            self.skip_ws();
            if !self.consume_str("::") {
                break;
            }
            segments.push(Name(self.parse_ident()?));
        }
        Some((Path { segments }, self.range(start, self.i)))
    }

    fn parse_ident(&mut self) -> Option<String> {
        self.skip_ws();
        let start = self.i;
        while let Some(ch) = self.peek() {
            if ch.is_ascii_alphanumeric() || ch == b'_' {
                self.i += 1;
            } else {
                break;
            }
        }
        (self.i > start)
            .then(|| String::from_utf8(self.chars[start..self.i].to_vec()).ok())
            .flatten()
    }

    fn consume_str(&mut self, s: &str) -> bool {
        self.skip_ws();
        let bytes = s.as_bytes();
        if self.chars.get(self.i..self.i + bytes.len()) == Some(bytes) {
            self.i += bytes.len();
            true
        } else {
            false
        }
    }

    fn consume_byte(&mut self, byte: u8) -> bool {
        self.skip_ws();
        if self.peek() == Some(byte) {
            self.i += 1;
            true
        } else {
            false
        }
    }

    fn skip_ws(&mut self) {
        while let Some(ch) = self.peek() {
            if ch.is_ascii_whitespace() {
                self.i += 1;
            } else {
                break;
            }
        }
    }

    fn peek(&self) -> Option<u8> {
        self.chars.get(self.i).copied()
    }

    fn range(&self, start: usize, end: usize) -> TextRange {
        TextRange::new(self.pos(start), self.pos(end))
    }

    fn pos(&self, offset: usize) -> TextSize {
        self.base + TextSize::from(offset as u32)
    }

    fn offset_of(&self, pos: TextSize) -> usize {
        u32::from(pos - self.base) as usize
    }
}

pub fn parse_sig_type_expr(type_expr: &SyntaxNode) -> Option<SigType> {
    let type_text = type_expr.to_string();
    let mut parser = SigParser::new(&type_text, type_expr.text_range().start());
    let sig = parser.parse_type()?;
    parser.is_eof().then_some(sig)
}

fn is_ident_start(ch: u8) -> bool {
    ch.is_ascii_alphabetic() || ch == b'_'
}

#[cfg(test)]
mod tests {
    use rowan::TextSize;

    use super::{SigParser, SigType};
    use crate::symbols::Name;

    #[test]
    fn sig_parser_parses_optional_record_fields() {
        let mut parser = SigParser::new("{ a?: int, b: bool }", TextSize::from(0));
        let sig = parser.parse_type().expect("record type should parse");
        assert!(parser.is_eof());

        let SigType::Record { fields, .. } = sig else {
            panic!("expected record type");
        };
        assert_eq!(fields.len(), 2);
        assert_eq!(fields[0].name, Name("a".to_string()));
        assert!(fields[0].optional);
        assert_eq!(fields[1].name, Name("b".to_string()));
        assert!(!fields[1].optional);
    }

    #[test]
    fn sig_parser_parses_empty_record() {
        let mut parser = SigParser::new("{}", TextSize::from(0));
        let sig = parser.parse_type().expect("empty record type should parse");
        assert!(parser.is_eof());

        let SigType::Record { fields, .. } = sig else {
            panic!("expected record type");
        };
        assert!(fields.is_empty());
    }

    #[test]
    fn sig_parser_parses_record_tail_spread() {
        let mut parser = SigParser::new("{ a: int, ..'t }", TextSize::from(0));
        let sig = parser
            .parse_type()
            .expect("record tail spread should parse");
        assert!(parser.is_eof());

        let SigType::RecordTailSpread { fields, tail, .. } = sig else {
            panic!("expected record tail spread");
        };
        assert_eq!(fields.len(), 1);
        assert_eq!(fields[0].name, Name("a".to_string()));
        let SigType::Var(var) = tail.as_ref() else {
            panic!("expected spread tail variable");
        };
        assert_eq!(var.name, "t");
    }

    #[test]
    fn sig_parser_parses_record_head_spread() {
        let mut parser = SigParser::new("{ ..'t, a?: int }", TextSize::from(0));
        let sig = parser
            .parse_type()
            .expect("record head spread should parse");
        assert!(parser.is_eof());

        let SigType::RecordHeadSpread { tail, fields, .. } = sig else {
            panic!("expected record head spread");
        };
        let SigType::Var(var) = tail.as_ref() else {
            panic!("expected spread tail variable");
        };
        assert_eq!(var.name, "t");
        assert_eq!(fields.len(), 1);
        assert_eq!(fields[0].name, Name("a".to_string()));
        assert!(fields[0].optional);
    }
}
