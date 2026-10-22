//! Original interpolation format grammar and source-owned text decomposition.
//! This plan does not select an implementation or authorize execution.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalSourceFormatKind { Display, Debug, LowerHex, UpperHex }
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalSourceFormatAlign { Left, Right, Center }
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalSourceFormatSign { Plus, Minus }

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LocalSourceFormatSpec {
    pub kind: LocalSourceFormatKind,
    pub align: Option<LocalSourceFormatAlign>,
    pub sign: Option<LocalSourceFormatSign>,
    pub fill: Option<char>,
    pub width: Option<i64>,
    pub precision: Option<i64>,
    pub alternate: bool,
    pub zero_pad: bool,
}

/// The original operation requested by formatting. A name is not evidence of
/// a resolved role member or standard-library provider.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalSourceFormatOperation {
    Member(&'static str),
    /// A value in std::core::fmt; receives the original format_spec then value.
    StandardFunction(&'static str),
}

impl LocalSourceFormatSpec {
    pub fn has_layout(&self) -> bool {
        self.align.is_some() || self.sign.is_some() || self.fill.is_some()
            || self.width.is_some() || self.precision.is_some() || self.alternate || self.zero_pad
    }
    pub fn operation(&self) -> LocalSourceFormatOperation {
        use LocalSourceFormatKind::*;
        if self.has_layout() {
            LocalSourceFormatOperation::StandardFunction(match self.kind {
                Display => "format_display", Debug => "format_debug",
                LowerHex => "format_lower_hex", UpperHex => "format_upper_hex",
            })
        } else {
            LocalSourceFormatOperation::Member(match self.kind {
                Display => "show", Debug => "debug", LowerHex => "lower_hex", UpperHex => "upper_hex",
            })
        }
    }
}

#[derive(Clone, Debug)]
pub enum LocalSourceStringPiece {
    /// Decoded adjacent text/escape tokens, anchored to their original bytes.
    Text { range: Range<usize>, value: Box<str> },
    /// Ordinal in this literal's actual interpolation descriptor vector.
    Interpolation(u32),
}

pub(super) fn parse_format(text: &str) -> Result<LocalSourceFormatSpec, FormationError> {
    let mut chars = text.chars().peekable();
    let mut spec = LocalSourceFormatSpec {
        kind: LocalSourceFormatKind::Display, align: None, sign: None, fill: None,
        width: None, precision: None, alternate: false, zero_pad: false,
    };
    fn align(ch: char) -> Option<LocalSourceFormatAlign> {
        match ch { '<' => Some(LocalSourceFormatAlign::Left), '>' => Some(LocalSourceFormatAlign::Right),
            '^' => Some(LocalSourceFormatAlign::Center), _ => None }
    }
    let mut lookahead = chars.clone();
    if let Some(first) = lookahead.next() {
        if let Some(value) = align(first) {
            spec.align = Some(value);
            chars.next();
        } else if first != '\n' && first != '\r' {
            if let Some(value) = lookahead.next().and_then(align) {
                spec.fill = Some(first);
                spec.align = Some(value);
                chars.next(); chars.next();
            }
        }
    }
    match chars.peek() {
        Some('+') => { spec.sign = Some(LocalSourceFormatSign::Plus); chars.next(); }
        Some('-') => { spec.sign = Some(LocalSourceFormatSign::Minus); chars.next(); }
        _ => {}
    }
    if chars.peek() == Some(&'#') { spec.alternate = true; chars.next(); }
    if chars.peek() == Some(&'0') { spec.zero_pad = true; chars.next(); }
    fn decimal(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Result<Option<i64>, FormationError> {
        let mut value = None;
        while let Some(digit) = chars.peek().and_then(|ch| ch.to_digit(10)) {
            value = Some(value.unwrap_or(0i64).checked_mul(10)
                .and_then(|value| value.checked_add(i64::from(digit))).ok_or_else(unsupported)?);
            chars.next();
        }
        Ok(value)
    }
    spec.width = decimal(&mut chars)?;
    if chars.peek() == Some(&'.') {
        chars.next();
        spec.precision = Some(decimal(&mut chars)?.ok_or_else(unsupported)?);
    }
    spec.kind = match chars.next() {
        None => LocalSourceFormatKind::Display,
        Some('?') => LocalSourceFormatKind::Debug,
        Some('x') => LocalSourceFormatKind::LowerHex,
        Some('X') => LocalSourceFormatKind::UpperHex,
        Some(_) => return Err(unsupported()),
    };
    if chars.next().is_some() { return Err(unsupported()); }
    Ok(spec)
}

pub(super) fn pieces(node: &SyntaxNode, parts: &[LocalSourceInterpolation])
    -> Result<Vec<LocalSourceStringPiece>, FormationError>
{
    let mut pieces = Vec::new();
    let mut value = String::new();
    let mut range: Option<Range<usize>> = None;
    let mut part_index = 0;
    fn flush(pieces: &mut Vec<LocalSourceStringPiece>, value: &mut String, range: &mut Option<Range<usize>>)
        -> Result<(), FormationError>
    {
        if let Some(range) = range.take() {
            if !value.is_empty() {
                push(pieces, LocalSourceStringPiece::Text { range, value: std::mem::take(value).into_boxed_str() })?;
            }
        }
        Ok(())
    }
    for element in node.children_with_tokens() {
        match element.kind() {
            SyntaxKind::StringStart | SyntaxKind::StringEnd | SyntaxKind::Whitespace
            | SyntaxKind::Newline | SyntaxKind::LineComment | SyntaxKind::BlockComment => {}
            SyntaxKind::StringInterpolation => {
                flush(&mut pieces, &mut value, &mut range)?;
                let part = parts.get(part_index).ok_or_else(invalid)?;
                let actual = element.as_node().ok_or_else(invalid)?;
                if range_of(actual).start > part.range.start || range_of(actual).end < part.range.end {
                    return Err(invalid());
                }
                push(&mut pieces, LocalSourceStringPiece::Interpolation(u32::try_from(part_index)
                    .map_err(|_| HirAvailabilityError::IdentityExhausted)?))?;
                part_index += 1;
            }
            SyntaxKind::StringText | SyntaxKind::StringEscape => {
                let bytes = usize::from(element.text_range().start())..usize::from(element.text_range().end());
                if let Some(range) = range.as_mut() { range.end = bytes.end; } else { range = Some(bytes); }
                if let Some(token) = element.as_token() {
                    value.try_reserve(token.text().len()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    value.push_str(token.text());
                } else {
                    let escape = element.as_node().ok_or_else(invalid)?;
                    let mut tokens = escape.children_with_tokens().filter_map(|element| element.into_token());
                    if tokens.next().is_none_or(|token| token.kind() != SyntaxKind::StringEscapeLead) { return Err(unsupported()); }
                    let target = tokens.next().ok_or_else(unsupported)?;
                    let ch = match target.kind() {
                        SyntaxKind::StringEscapeSimple => {
                            let mut chars = target.text().chars();
                            let ch = chars.next().ok_or_else(unsupported)?;
                            if chars.next().is_some() { return Err(unsupported()); }
                            match ch { 'n' => '\n', 'r' => '\r', 't' => '\t', '0' => '\0', other => other }
                        }
                        SyntaxKind::StringEscapeUnicodeStart => {
                            let hex = tokens.next().ok_or_else(unsupported)?;
                            if hex.kind() != SyntaxKind::StringEscapeUnicodeHex
                                || tokens.next().is_none_or(|token| token.kind() != SyntaxKind::StringEscapeUnicodeEnd)
                            { return Err(unsupported()); }
                            u32::from_str_radix(hex.text(), 16).ok().and_then(char::from_u32).unwrap_or(char::REPLACEMENT_CHARACTER)
                        }
                        _ => return Err(unsupported()),
                    };
                    if tokens.next().is_some() { return Err(unsupported()); }
                    value.try_reserve(ch.len_utf8()).map_err(|_| HirAvailabilityError::IdentityExhausted)?;
                    value.push(ch);
                }
            }
            _ => return Err(unsupported()),
        }
    }
    flush(&mut pieces, &mut value, &mut range)?;
    if part_index != parts.len() { return Err(invalid()); }
    Ok(pieces)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn original_format_grammar_keeps_member_and_layout_operations_distinct() {
        for (raw, kind, member, function) in [
            ("", LocalSourceFormatKind::Display, "show", "format_display"),
            ("?", LocalSourceFormatKind::Debug, "debug", "format_debug"),
            ("x", LocalSourceFormatKind::LowerHex, "lower_hex", "format_lower_hex"),
            ("X", LocalSourceFormatKind::UpperHex, "upper_hex", "format_upper_hex"),
        ] {
            let plain = parse_format(raw).unwrap();
            assert_eq!(plain.kind, kind);
            assert!(!plain.has_layout());
            assert_eq!(plain.operation(), LocalSourceFormatOperation::Member(member));
            let layout = parse_format(&format!("猫^+#08.2{raw}")).unwrap();
            assert_eq!(layout.kind, kind);
            assert_eq!(layout.fill, Some('猫'));
            assert_eq!(layout.align, Some(LocalSourceFormatAlign::Center));
            assert_eq!(layout.sign, Some(LocalSourceFormatSign::Plus));
            assert_eq!((layout.width, layout.precision), (Some(8), Some(2)));
            assert!(layout.alternate && layout.zero_pad);
            assert_eq!(layout.operation(), LocalSourceFormatOperation::StandardFunction(function));
        }
        assert_eq!(parse_format("<-").unwrap().align, Some(LocalSourceFormatAlign::Left));
        assert_eq!(parse_format(">").unwrap().align, Some(LocalSourceFormatAlign::Right));
        assert_eq!(parse_format("-").unwrap().sign, Some(LocalSourceFormatSign::Minus));
        assert_eq!(parse_format("0").unwrap().width, None);
        assert!(parse_format("0").unwrap().zero_pad);
        assert_eq!(parse_format("00").unwrap().width, Some(0));
        assert_eq!(parse_format(".0").unwrap().precision, Some(0));
        assert_eq!(parse_format("9223372036854775807").unwrap().width, Some(i64::MAX));
        assert_eq!(parse_format(".9223372036854775807").unwrap().precision, Some(i64::MAX));
        for invalid in ["s", ".", ".x", "++", "xX", "x8", "8x?", "8#", "#-", " 8",
            "\n<", "\r>", "9223372036854775808", ".9223372036854775808"] {
            assert!(matches!(parse_format(invalid), Err(FormationError::Unsupported(_))), "{invalid:?}");
        }
    }
}
