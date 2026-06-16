//! String literal token decoding and interpolation format parsing.
//!
//! This module stops at CST-to-structured-parts conversion. It does not allocate
//! poly expressions or type variables; expression lowering decides how each part
//! becomes a value.

use super::*;

impl<'a> ExprLowerer<'a> {
    /// Lower a string literal, using the fast plain path when no interpolation exists.
    pub(super) fn lower_string_lit(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        if node
            .children()
            .all(|child| child.kind() != SyntaxKind::StringInterp)
        {
            return self.lower_plain_string_lit(node);
        }

        self.lower_string_lit_parts(string_lit_parts(node)?)
    }

    fn lower_string_lit_parts(
        &mut self,
        parts: Vec<StringLitPart>,
    ) -> Result<Computation, LoweringError> {
        let mut acc = None;
        for part in parts {
            let part = match part {
                StringLitPart::Text(text) => self.string_value(text),
                StringLitPart::Interp(part) => self.lower_string_interp_part(part)?,
            };
            acc = Some(match acc {
                Some(left) => self.concat_string_values(left, part)?,
                None => part,
            });
        }
        Ok(acc.unwrap_or_else(|| self.string_value(String::new())))
    }

    fn lower_string_interp_part(
        &mut self,
        part: StringInterpPart,
    ) -> Result<Computation, LoweringError> {
        let value = self.lower_expr(&part.expr)?;
        if !part.format.has_layout() {
            return Ok(self.lower_format_kind_selection(value, part.format.kind));
        }

        let format_spec = self.format_spec_value(&part.format)?;
        let formatter = self.lower_std_value_ref(crate::std_paths::core_fmt_value(
            part.format.kind.format_function_name(),
        ))?;
        let formatter = self.make_app(formatter, format_spec);
        Ok(self.make_app(formatter, value))
    }

    fn lower_format_kind_selection(&mut self, value: Computation, kind: FormatKind) -> Computation {
        self.lower_synthetic_selection(value, kind.method_name().to_string())
    }

    fn format_spec_value(&mut self, spec: &FormatSpec) -> Result<Computation, LoweringError> {
        let fields = vec![
            ("kind".to_string(), self.format_kind_value(spec.kind)?),
            (
                "align".to_string(),
                self.optional_format_align_value(spec.align)?,
            ),
            (
                "sign".to_string(),
                self.optional_format_sign_value(spec.sign)?,
            ),
            (
                "fill".to_string(),
                self.optional_string_value(spec.fill.clone())?,
            ),
            ("width".to_string(), self.optional_int_value(spec.width)?),
            (
                "precision".to_string(),
                self.optional_int_value(spec.precision)?,
            ),
            ("alternate".to_string(), self.lower_bool(spec.alternate)),
            ("zero_pad".to_string(), self.lower_bool(spec.zero_pad)),
        ];
        let record = self.synthetic_record_value(fields);
        let constructor =
            self.lower_std_value_ref(crate::std_paths::core_fmt_value("format_spec"))?;
        Ok(self.make_app(constructor, record))
    }

    fn format_kind_value(&mut self, kind: FormatKind) -> Result<Computation, LoweringError> {
        self.lower_std_value_ref(crate::std_paths::core_fmt_format_kind_value(
            kind.variant_name(),
        ))
    }

    fn optional_format_align_value(
        &mut self,
        align: Option<FormatAlign>,
    ) -> Result<Computation, LoweringError> {
        match align {
            Some(align) => {
                let value = self.lower_std_value_ref(
                    crate::std_paths::core_fmt_format_align_value(align.variant_name()),
                )?;
                self.some_value(value)
            }
            None => self.none_value(),
        }
    }

    fn optional_format_sign_value(
        &mut self,
        sign: Option<FormatSign>,
    ) -> Result<Computation, LoweringError> {
        match sign {
            Some(sign) => {
                let value = self.lower_std_value_ref(
                    crate::std_paths::core_fmt_format_sign_value(sign.variant_name()),
                )?;
                self.some_value(value)
            }
            None => self.none_value(),
        }
    }

    fn optional_string_value(
        &mut self,
        value: Option<String>,
    ) -> Result<Computation, LoweringError> {
        match value {
            Some(value) => {
                let value = self.string_value(value);
                self.some_value(value)
            }
            None => self.none_value(),
        }
    }

    fn optional_int_value(&mut self, value: Option<i64>) -> Result<Computation, LoweringError> {
        match value {
            Some(value) => {
                let value = self.int_value(value);
                self.some_value(value)
            }
            None => self.none_value(),
        }
    }

    fn some_value(&mut self, value: Computation) -> Result<Computation, LoweringError> {
        let some = self.lower_std_value_ref(crate::std_paths::data_opt_value("just"))?;
        Ok(self.make_app(some, value))
    }

    fn none_value(&mut self) -> Result<Computation, LoweringError> {
        self.lower_std_value_ref(crate::std_paths::data_opt_value("nil"))
    }

    fn concat_string_values(
        &mut self,
        left: Computation,
        right: Computation,
    ) -> Result<Computation, LoweringError> {
        let concat = self.lower_std_value_ref(crate::std_paths::text_str_concat_value())?;
        let partial = self.make_app(concat, left);
        Ok(self.make_app(partial, right))
    }

    fn lower_plain_string_lit(&mut self, node: &Cst) -> Result<Computation, LoweringError> {
        let text = plain_string_lit_text(node)?;
        Ok(self.string_value(text))
    }
}

pub(super) enum StringLitPart {
    Text(String),
    Interp(StringInterpPart),
}

pub(super) struct StringInterpPart {
    pub(super) format: FormatSpec,
    pub(super) expr: Cst,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct FormatSpec {
    pub(super) kind: FormatKind,
    pub(super) align: Option<FormatAlign>,
    pub(super) sign: Option<FormatSign>,
    pub(super) fill: Option<String>,
    pub(super) width: Option<i64>,
    pub(super) precision: Option<i64>,
    pub(super) alternate: bool,
    pub(super) zero_pad: bool,
}

impl FormatSpec {
    fn display() -> Self {
        Self {
            kind: FormatKind::Display,
            align: None,
            sign: None,
            fill: None,
            width: None,
            precision: None,
            alternate: false,
            zero_pad: false,
        }
    }

    pub(super) fn has_layout(&self) -> bool {
        self.align.is_some()
            || self.sign.is_some()
            || self.fill.is_some()
            || self.width.is_some()
            || self.precision.is_some()
            || self.alternate
            || self.zero_pad
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FormatKind {
    Display,
    Debug,
    LowerHex,
    UpperHex,
}

impl FormatKind {
    pub(super) fn method_name(self) -> &'static str {
        match self {
            Self::Display => "show",
            Self::Debug => "debug",
            Self::LowerHex => "lower_hex",
            Self::UpperHex => "upper_hex",
        }
    }

    pub(super) fn format_function_name(self) -> &'static str {
        match self {
            Self::Display => "format_display",
            Self::Debug => "format_debug",
            Self::LowerHex => "format_lower_hex",
            Self::UpperHex => "format_upper_hex",
        }
    }

    pub(super) fn variant_name(self) -> &'static str {
        match self {
            Self::Display => "display",
            Self::Debug => "debug",
            Self::LowerHex => "lower_hex",
            Self::UpperHex => "upper_hex",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FormatAlign {
    Left,
    Right,
    Center,
}

impl FormatAlign {
    fn from_marker(marker: char) -> Option<Self> {
        match marker {
            '<' => Some(Self::Left),
            '>' => Some(Self::Right),
            '^' => Some(Self::Center),
            _ => None,
        }
    }

    pub(super) fn variant_name(self) -> &'static str {
        match self {
            Self::Left => "left",
            Self::Right => "right",
            Self::Center => "center",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FormatSign {
    Plus,
    Minus,
}

impl FormatSign {
    pub(super) fn variant_name(self) -> &'static str {
        match self {
            Self::Plus => "plus",
            Self::Minus => "minus",
        }
    }
}

pub(super) fn plain_string_expr_text(node: &Cst) -> Result<Option<String>, LoweringError> {
    let mut strings = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::StringLit);
    let Some(first) = strings.next() else {
        return Ok(None);
    };
    if strings.next().is_some() {
        return Ok(None);
    }
    plain_string_lit_text(&first).map(Some)
}

pub(super) fn plain_string_lit_text(node: &Cst) -> Result<String, LoweringError> {
    if node
        .children()
        .any(|child| child.kind() == SyntaxKind::StringInterp)
    {
        return Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::StringInterp,
        });
    }

    let mut text = String::new();
    let mut tokens = node.children_with_tokens().peekable();
    while let Some(item) = tokens.next() {
        let Some(token) = item.into_token() else {
            continue;
        };
        match token.kind() {
            SyntaxKind::StringText => text.push_str(token.text()),
            SyntaxKind::StringEscapeLead => text.push_str(&collect_string_escape_text(&mut tokens)),
            SyntaxKind::StringStart | SyntaxKind::StringEnd => {}
            _ => {}
        }
    }
    Ok(text)
}

pub(super) fn string_lit_parts(node: &Cst) -> Result<Vec<StringLitPart>, LoweringError> {
    let mut parts = Vec::new();
    let mut tokens = node.children_with_tokens().peekable();
    while let Some(item) = tokens.next() {
        if item_is_trivia(&item) {
            continue;
        }
        match item {
            NodeOrToken::Token(token) => match token.kind() {
                SyntaxKind::StringText => {
                    push_string_lit_text_part(&mut parts, token.text().to_string());
                }
                SyntaxKind::StringEscapeLead => {
                    push_string_lit_text_part(&mut parts, collect_string_escape_text(&mut tokens));
                }
                SyntaxKind::StringStart | SyntaxKind::StringEnd => {}
                _ => return Err(LoweringError::UnsupportedSyntax { kind: token.kind() }),
            },
            NodeOrToken::Node(child) if child.kind() == SyntaxKind::StringInterp => {
                parts.push(string_interp_part(&child)?);
            }
            NodeOrToken::Node(child) => {
                return Err(LoweringError::UnsupportedSyntax { kind: child.kind() });
            }
        }
    }
    Ok(parts)
}

fn string_interp_part(node: &Cst) -> Result<StringLitPart, LoweringError> {
    let format = string_interp_format(node)?;
    let expr = string_interp_body_expr(node).ok_or(LoweringError::UnsupportedSyntax {
        kind: SyntaxKind::StringInterp,
    })?;
    Ok(StringLitPart::Interp(StringInterpPart { format, expr }))
}

fn string_interp_format(node: &Cst) -> Result<FormatSpec, LoweringError> {
    let mut tokens = node
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .filter(|token| token.kind() == SyntaxKind::StringInterpFormatText);
    let Some(token) = tokens.next() else {
        return Ok(FormatSpec::display());
    };
    if tokens.next().is_some() {
        return Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::StringInterpFormatText,
        });
    }
    parse_format_spec(token.text())
}

fn parse_format_spec(text: &str) -> Result<FormatSpec, LoweringError> {
    let chars = text.chars().collect::<Vec<_>>();
    let mut index = 0usize;
    let mut spec = FormatSpec::display();

    if let Some((fill, align, next)) = parse_format_align(&chars) {
        spec.fill = fill;
        spec.align = Some(align);
        index = next;
    }

    match chars.get(index).copied() {
        Some('+') => {
            spec.sign = Some(FormatSign::Plus);
            index += 1;
        }
        Some('-') => {
            spec.sign = Some(FormatSign::Minus);
            index += 1;
        }
        _ => {}
    }

    if chars.get(index) == Some(&'#') {
        spec.alternate = true;
        index += 1;
    }

    if chars.get(index) == Some(&'0') {
        spec.zero_pad = true;
        index += 1;
    }

    let (width, next) = parse_format_decimal(&chars, index)?;
    spec.width = width;
    index = next;

    if chars.get(index) == Some(&'.') {
        let (precision, next) = parse_format_decimal(&chars, index + 1)?;
        let Some(precision) = precision else {
            return Err(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::StringInterpFormatText,
            });
        };
        spec.precision = Some(precision);
        index = next;
    }

    match chars.get(index).copied() {
        Some('?') => {
            spec.kind = FormatKind::Debug;
            index += 1;
        }
        Some('x') => {
            spec.kind = FormatKind::LowerHex;
            index += 1;
        }
        Some('X') => {
            spec.kind = FormatKind::UpperHex;
            index += 1;
        }
        Some(_) => {
            return Err(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::StringInterpFormatText,
            });
        }
        None => {}
    }

    if index == chars.len() {
        Ok(spec)
    } else {
        Err(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::StringInterpFormatText,
        })
    }
}

fn parse_format_align(chars: &[char]) -> Option<(Option<String>, FormatAlign, usize)> {
    if let Some(align) = chars.first().copied().and_then(FormatAlign::from_marker) {
        return Some((None, align, 1));
    }
    let fill = *chars.first()?;
    if fill == '\n' || fill == '\r' {
        return None;
    }
    let align = chars.get(1).copied().and_then(FormatAlign::from_marker)?;
    Some((Some(fill.to_string()), align, 2))
}

fn parse_format_decimal(
    chars: &[char],
    mut index: usize,
) -> Result<(Option<i64>, usize), LoweringError> {
    let start = index;
    let mut value = 0i64;
    while let Some(digit) = chars.get(index).and_then(|ch| ch.to_digit(10)) {
        value = value
            .checked_mul(10)
            .and_then(|value| value.checked_add(i64::from(digit)))
            .ok_or(LoweringError::UnsupportedSyntax {
                kind: SyntaxKind::StringInterpFormatText,
            })?;
        index += 1;
    }
    Ok(((index > start).then_some(value), index))
}

fn string_interp_body_expr(node: &Cst) -> Option<Cst> {
    node.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    })
}

fn push_string_lit_text_part(parts: &mut Vec<StringLitPart>, text: String) {
    if text.is_empty() {
        return;
    }
    match parts.last_mut() {
        Some(StringLitPart::Text(existing)) => existing.push_str(&text),
        _ => parts.push(StringLitPart::Text(text)),
    }
}

fn collect_string_escape_text(
    tokens: &mut std::iter::Peekable<rowan::SyntaxElementChildren<YulangLanguage>>,
) -> String {
    let Some(next) = tokens.next().and_then(|item| item.into_token()) else {
        return String::new();
    };
    match next.kind() {
        SyntaxKind::StringEscapeSimple => simple_escape_text(next.text()),
        SyntaxKind::StringEscapeUnicodeStart => collect_unicode_escape_text(tokens),
        _ => next.text().to_string(),
    }
}

fn simple_escape_text(text: &str) -> String {
    match text {
        "n" => "\n".to_string(),
        "r" => "\r".to_string(),
        "t" => "\t".to_string(),
        "\\" => "\\".to_string(),
        "\"" => "\"".to_string(),
        "0" => "\0".to_string(),
        other => other.to_string(),
    }
}

fn collect_unicode_escape_text(
    tokens: &mut std::iter::Peekable<rowan::SyntaxElementChildren<YulangLanguage>>,
) -> String {
    let Some(hex) = tokens.next().and_then(|item| item.into_token()) else {
        return String::new();
    };
    if hex.kind() != SyntaxKind::StringEscapeUnicodeHex {
        return hex.text().to_string();
    }
    let value = u32::from_str_radix(hex.text(), 16)
        .ok()
        .and_then(char::from_u32)
        .unwrap_or(char::REPLACEMENT_CHARACTER);
    if matches!(
        tokens
            .peek()
            .and_then(|item| item.as_token())
            .map(|token| token.kind()),
        Some(SyntaxKind::StringEscapeUnicodeEnd)
    ) {
        tokens.next();
    }
    value.to_string()
}
