//! Syntax boundary for Yulang3.

use std::{ops::Range, sync::Arc};

/// Source text consumed by syntax phase entrypoints.
pub type SourceText = str;

/// Source-level facts discovered in the syntax preamble.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderInfo {
    coverage: HeaderCoverage,
    imports: Arc<[HeaderImport]>,
    operators: Arc<[HeaderOperator]>,
}

impl HeaderInfo {
    pub fn coverage(&self) -> &HeaderCoverage {
        &self.coverage
    }

    pub fn imports(&self) -> &[HeaderImport] {
        &self.imports
    }

    pub fn operators(&self) -> &[HeaderOperator] {
        &self.operators
    }
}

/// The source prefix observed while discovering header facts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderCoverage {
    range: Range<usize>,
    stop: HeaderStop,
}

impl HeaderCoverage {
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    pub fn stop(&self) -> HeaderStop {
        self.stop
    }
}

/// Why header discovery stopped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeaderStop {
    Eof,
    FirstNonHeader,
}

/// An unresolved source-level import discovered in the header.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderImport {
    range: Range<usize>,
    form: HeaderImportForm,
    path: Vec<String>,
    visibility: Visibility,
    alias: Option<String>,
}

impl HeaderImport {
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    pub fn form(&self) -> HeaderImportForm {
        self.form
    }

    pub fn path(&self) -> &[String] {
        &self.path
    }

    pub fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub fn alias(&self) -> Option<&str> {
        self.alias.as_deref()
    }
}

/// Source-level import form, before module resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeaderImportForm {
    Plain,
    Mod,
    Realm,
    Band,
}

/// Source-level visibility of a discovered header fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Visibility {
    Private,
    Public,
}

/// A dynamic operator signature discovered in the header.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderOperator {
    range: Range<usize>,
    name: String,
    fixity: OperatorFixity,
    visibility: Visibility,
    binding_power: BindingPower,
}

impl HeaderOperator {
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn fixity(&self) -> OperatorFixity {
        self.fixity
    }

    pub fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub fn binding_power(&self) -> BindingPower {
        self.binding_power
    }
}

/// Canonical operator fixity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OperatorFixity {
    Infix,
}

/// Binding-power sides applicable to an operator signature.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BindingPower {
    left: Option<u16>,
    right: Option<u16>,
}

impl BindingPower {
    pub fn left(self) -> Option<u16> {
        self.left
    }

    pub fn right(self) -> Option<u16> {
        self.right
    }
}

/// Discover leading plain imports and infix operator signatures.
pub fn scan_header(source: Arc<SourceText>) -> HeaderInfo {
    let source = source.as_ref();
    let mut imports = Vec::new();
    let mut operators = Vec::new();
    let mut offset = 0;

    while offset < source.len() {
        let line = source_line(source, offset);

        if let Some(import) = scan_plain_use(line.text, offset) {
            imports.push(import);
        } else if let Some(operator) = scan_infix_operator(line.text, offset) {
            operators.push(operator);
        } else {
            break;
        }

        offset = line.next_offset;
    }

    let stop = if offset == source.len() {
        HeaderStop::Eof
    } else {
        HeaderStop::FirstNonHeader
    };

    HeaderInfo {
        coverage: HeaderCoverage {
            range: 0..offset,
            stop,
        },
        imports: imports.into(),
        operators: operators.into(),
    }
}

struct SourceLine<'source> {
    text: &'source str,
    next_offset: usize,
}

fn source_line(source: &str, offset: usize) -> SourceLine<'_> {
    let remainder = &source[offset..];

    match remainder.find('\n') {
        Some(relative_end) => {
            let line_end = offset + relative_end;
            let text_end = if source[..line_end].ends_with('\r') {
                line_end - 1
            } else {
                line_end
            };

            SourceLine {
                text: &source[offset..text_end],
                next_offset: line_end + 1,
            }
        }
        None => SourceLine {
            text: remainder,
            next_offset: source.len(),
        },
    }
}

fn scan_plain_use(line: &str, offset: usize) -> Option<HeaderImport> {
    let path = line.strip_prefix("use ")?;
    let path = parse_plain_path(path)?;

    Some(HeaderImport {
        range: offset..offset + line.len(),
        form: HeaderImportForm::Plain,
        path,
        visibility: Visibility::Private,
        alias: None,
    })
}

fn parse_plain_path(path: &str) -> Option<Vec<String>> {
    path.split('.')
        .map(|component| {
            let mut chars = component.chars();
            let first = chars.next()?;

            if !(first.is_ascii_alphabetic() || first == '_')
                || !chars.all(|character| character.is_ascii_alphanumeric() || character == '_')
            {
                return None;
            }

            Some(component.to_owned())
        })
        .collect()
}

fn scan_infix_operator(line: &str, offset: usize) -> Option<HeaderOperator> {
    let remainder = line.strip_prefix("infix ")?;
    let remainder = remainder.strip_prefix('(')?;
    let closing_parenthesis = remainder.find(')')?;
    let name = &remainder[..closing_parenthesis];

    if name.is_empty() {
        return None;
    }

    let remainder = &remainder[closing_parenthesis + 1..];
    let remainder = strip_required_space(remainder)?;
    let (left, remainder) = parse_u16(remainder)?;
    let remainder = strip_required_space(remainder)?;
    let (right, remainder) = parse_u16(remainder)?;
    let remainder = strip_required_space(remainder)?;
    let remainder_offset = line.len() - remainder.len();
    let _body = remainder.strip_prefix('=')?;

    Some(HeaderOperator {
        range: offset..offset + remainder_offset + 1,
        name: name.to_owned(),
        fixity: OperatorFixity::Infix,
        visibility: Visibility::Private,
        binding_power: BindingPower {
            left: Some(left),
            right: Some(right),
        },
    })
}

fn strip_required_space(text: &str) -> Option<&str> {
    let remainder = text.strip_prefix(' ')?;
    Some(remainder.trim_start_matches(' '))
}

fn parse_u16(text: &str) -> Option<(u16, &str)> {
    let digit_count = text
        .bytes()
        .take_while(|byte| byte.is_ascii_digit())
        .count();

    if digit_count == 0 {
        return None;
    }

    let (digits, remainder) = text.split_at(digit_count);
    Some((digits.parse().ok()?, remainder))
}

#[cfg(test)]
mod tests {
    use super::*;

    const LEADING_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-plain/main.yu"
    ));
    const INFIX_OPERATOR_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/infix-operator-header/main.yu"
    ));

    #[test]
    fn discovers_leading_plain_use_fixture() {
        let header = scan_header(fixture_source(LEADING_USE_SOURCE));

        assert_eq!(header.coverage().range(), &(0..13));
        assert_eq!(header.coverage().stop(), HeaderStop::FirstNonHeader);
        assert!(header.operators().is_empty());

        let [import] = header.imports() else {
            panic!("expected exactly one header import: {header:#?}");
        };
        assert_eq!(import.range(), &(0..12));
        assert_eq!(import.form(), HeaderImportForm::Plain);
        assert_eq!(import.path(), ["std".to_owned(), "data".to_owned()]);
        assert_eq!(import.visibility(), Visibility::Private);
        assert_eq!(import.alias(), None);
    }

    #[test]
    fn discovers_infix_operator_header_fixture() {
        let header = scan_header(fixture_source(INFIX_OPERATOR_SOURCE));

        assert_eq!(header.coverage().range(), &(0..25));
        assert_eq!(header.coverage().stop(), HeaderStop::FirstNonHeader);
        assert!(header.imports().is_empty());

        let [operator] = header.operators() else {
            panic!("expected exactly one header operator: {header:#?}");
        };
        assert_eq!(operator.range(), &(0..19));
        assert_eq!(operator.name(), "<+>");
        assert_eq!(operator.fixity(), OperatorFixity::Infix);
        assert_eq!(operator.visibility(), Visibility::Private);
        assert_eq!(operator.binding_power().left(), Some(50));
        assert_eq!(operator.binding_power().right(), Some(51));
    }

    fn fixture_source(bytes: &'static [u8]) -> Arc<SourceText> {
        Arc::from(std::str::from_utf8(bytes).expect("fixture source must be valid UTF-8"))
    }
}
