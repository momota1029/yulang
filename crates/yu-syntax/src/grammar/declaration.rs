//! Shared grammar for source-leading declarations.

use std::ops::Range;

use chasa::{
    ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    prelude::{In, from_fn},
};

use crate::{
    HeaderImport, HeaderImportForm, HeaderImportRoute, HeaderImportRouteSeparator, Visibility,
    grammar::expression::{Expression, IntegerLiteral, parse_expression, parse_integer_literal},
    input::SourceInput,
    scan::{
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::scan_trivia,
        word::{WordSpan, scan_word},
    },
    session::{Delimiter, ParseLocal},
};

/// One parsed source-leading declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Declaration<'source> {
    Use(UseDeclaration<'source>),
    Binding(BindingDeclaration<'source>),
    OperatorHeader(OperatorHeaderDeclaration<'source>),
}

/// A `my name = value` declaration with a minimal expression value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingDeclaration<'source> {
    range: Range<usize>,
    name: WordSpan<'source>,
    value: Expression<'source>,
}

impl<'source> BindingDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn name(&self) -> WordSpan<'source> {
        self.name
    }

    pub(crate) fn value(&self) -> &Expression<'source> {
        &self.value
    }
}

/// An infix operator signature before its opaque header body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorHeaderDeclaration<'source> {
    range: Range<usize>,
    name: &'source str,
    left_binding_power: IntegerLiteral<'source>,
    right_binding_power: IntegerLiteral<'source>,
}

impl<'source> OperatorHeaderDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn name(&self) -> &'source str {
        self.name
    }

    pub(crate) fn left_binding_power(&self) -> IntegerLiteral<'source> {
        self.left_binding_power
    }

    pub(crate) fn right_binding_power(&self) -> IntegerLiteral<'source> {
        self.right_binding_power
    }
}

/// A parsed `use` declaration before syntax planning resolves it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseDeclaration<'source> {
    range: Range<usize>,
    visibility: Visibility,
    tree: UseTree<'source>,
}

impl<'source> UseDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub(crate) fn tree(&self) -> &UseTree<'source> {
        &self.tree
    }

    /// Projects one qualifier-free single-target use declaration to a header fact.
    pub(crate) fn project_single_import(&self) -> Result<HeaderImport, UseSingleProjectionError> {
        if !matches!(self.tree.terminal, UseTerminal::Single) {
            return Err(UseSingleProjectionError::NonSingleTerminal);
        }
        if !self.tree.qualifiers.is_empty() {
            return Err(UseSingleProjectionError::Qualifiers);
        }
        let alias = match self.tree.aliases.as_slice() {
            [] => None,
            [alias] => Some(alias.text().to_owned()),
            _ => return Err(UseSingleProjectionError::MultipleAliases),
        };

        Ok(HeaderImport::new(
            self.range(),
            self.tree.form,
            project_use_route(&self.tree.prefix),
            self.visibility,
            alias,
        ))
    }
}

/// Why a use declaration cannot yet project to one header import fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum UseSingleProjectionError {
    NonSingleTerminal,
    MultipleAliases,
    Qualifiers,
}

/// One recursively composable `use` specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseTree<'source> {
    range: Range<usize>,
    form: HeaderImportForm,
    prefix: UsePath<'source>,
    terminal: UseTerminal<'source>,
    aliases: Vec<WordSpan<'source>>,
    qualifiers: UseQualifiers<'source>,
}

impl<'source> UseTree<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn form(&self) -> HeaderImportForm {
        self.form
    }

    pub(crate) fn prefix(&self) -> &UsePath<'source> {
        &self.prefix
    }

    pub(crate) fn terminal(&self) -> &UseTerminal<'source> {
        &self.terminal
    }

    pub(crate) fn aliases(&self) -> &[WordSpan<'source>] {
        &self.aliases
    }

    pub(crate) fn qualifiers(&self) -> &UseQualifiers<'source> {
        &self.qualifiers
    }
}

/// A separator-preserving path prefix of a use specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UsePath<'source> {
    segments: Vec<UseSegment<'source>>,
    separators: Vec<UseSeparator>,
}

impl<'source> UsePath<'source> {
    pub(crate) fn segments(&self) -> &[UseSegment<'source>] {
        &self.segments
    }

    pub(crate) fn separators(&self) -> &[UseSeparator] {
        &self.separators
    }
}

/// One path segment, retaining the distinction between words and operators.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UseSegment<'source> {
    Word(WordSpan<'source>),
    Operator {
        range: Range<usize>,
        text: &'source str,
    },
}

impl<'source> UseSegment<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        match self {
            Self::Word(word) => word.range(),
            Self::Operator { range, .. } => range.clone(),
        }
    }
}

fn project_use_route(path: &UsePath<'_>) -> HeaderImportRoute {
    let segments = path
        .segments()
        .iter()
        .map(|segment| match segment {
            UseSegment::Word(word) => word.text().to_owned(),
            UseSegment::Operator { text, .. } => (*text).to_owned(),
        })
        .collect();
    let separators = path
        .separators()
        .iter()
        .map(|separator| match separator {
            UseSeparator::ColonColon => HeaderImportRouteSeparator::ColonColon,
            UseSeparator::Slash => HeaderImportRouteSeparator::Slash,
        })
        .collect();

    HeaderImportRoute::new(segments, separators)
}

/// A route separator between two stored path segments.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum UseSeparator {
    ColonColon,
    Slash,
}

/// The terminating shape of a use tree.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UseTerminal<'source> {
    Single,
    Group {
        join: Option<UseSeparator>,
        items: Vec<UseTree<'source>>,
    },
    Glob {
        join: Option<UseSeparator>,
        without: Vec<UseExclusion<'source>>,
    },
}

/// Syntactic qualifiers whose resolution semantics are intentionally deferred.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct UseQualifiers<'source> {
    version: Option<UseVersion<'source>>,
    anchor: Option<UsePath<'source>>,
}

impl<'source> UseQualifiers<'source> {
    pub(crate) fn version(&self) -> Option<&UseVersion<'source>> {
        self.version.as_ref()
    }

    pub(crate) fn anchor(&self) -> Option<&UsePath<'source>> {
        self.anchor.as_ref()
    }

    fn is_empty(&self) -> bool {
        self.version.is_none() && self.anchor.is_none()
    }
}

/// A raw version suffix on a use specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseVersion<'source> {
    range: Range<usize>,
    text: &'source str,
}

/// An exclusion pattern attached to a glob terminal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UseExclusion<'source> {
    Segment(UseSegment<'source>),
    Glob {
        range: Range<usize>,
    },
    Group {
        range: Range<usize>,
        items: Vec<UseTree<'source>>,
    },
}

/// Parses one leading `use` declaration from the shared character stream.
pub(crate) fn parse_declaration<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<Declaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    input.choice((
        from_fn(|input| parse_use_declaration(input).map(Declaration::Use)),
        from_fn(|input| parse_binding_declaration(input).map(Declaration::Binding)),
        from_fn(|input| parse_operator_header(input).map(Declaration::OperatorHeader)),
    ))
}

fn parse_operator_header<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<OperatorHeaderDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = input.pos();
    let keyword = input.run(from_fn(scan_word))?;
    (keyword.text() == "infix").then_some(())?;
    inline_trivia(&mut input)?;
    let open = input.run(from_fn(scan_punctuation))?;
    (open.kind() == PunctuationKind::Open(Delimiter::Parenthesis)).then_some(())?;
    let name = parse_operator_name(&mut input)?;
    let close = input.run(from_fn(scan_punctuation))?;
    (close.kind() == PunctuationKind::Close(Delimiter::Parenthesis)).then_some(())?;
    inline_trivia(&mut input)?;
    let left_binding_power = input.run(from_fn(parse_integer_literal))?;
    inline_trivia(&mut input)?;
    let right_binding_power = input.run(from_fn(parse_integer_literal))?;
    inline_trivia(&mut input)?;
    input.skip(chasa::prelude::item('='))?;
    let end = input.pos();

    Some(OperatorHeaderDeclaration {
        range: start..end,
        name,
        left_binding_power,
        right_binding_power,
    })
}

fn parse_operator_name<'source, E>(
    input: &mut In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<&'source str>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = input.pos();
    while !input.input.remainder().starts_with(')') {
        input.input.next()?;
    }
    let end = input.pos();
    (start < end).then_some(&input.input.source()[start..end])
}

fn parse_binding_declaration<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<BindingDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = input.pos();
    let keyword = input.run(from_fn(scan_word))?;
    (keyword.text() == "my").then_some(())?;
    inline_trivia(&mut input)?;
    let name = input.run(from_fn(scan_word))?;
    inline_trivia(&mut input)?;
    input.skip(chasa::prelude::item('='))?;
    inline_trivia(&mut input)?;
    let value = input.run(from_fn(parse_expression))?;
    let end = value.range().end;

    Some(BindingDeclaration {
        range: start..end,
        name,
        value,
    })
}

fn parse_use_declaration<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<UseDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = input.pos();
    let keyword = input.run(from_fn(scan_word))?;
    (keyword.text() == "use").then_some(())?;
    inline_trivia(&mut input)?;

    let tree = parse_use_tree(&mut input)?;
    let end = tree.range().end;

    Some(UseDeclaration {
        range: start..end,
        visibility: Visibility::Private,
        tree,
    })
}

fn parse_use_tree<'source, E>(
    input: &mut In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<UseTree<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = input.pos();
    if input.maybe(from_fn(parse_open_brace))?.is_some() {
        let (terminal, terminal_end) = parse_use_group_terminal(input, None)?;
        let aliases = parse_use_aliases(input)?;
        let end = aliases
            .last()
            .map_or(terminal_end, |alias| alias.range().end);
        return Some(UseTree {
            range: start..end,
            form: HeaderImportForm::Plain,
            prefix: empty_use_path(),
            terminal,
            aliases,
            qualifiers: UseQualifiers::default(),
        });
    }

    let first = input.run(from_fn(scan_word))?;

    let (form, prefix, terminal, terminal_end) = if classify_use_form(first, None)
        == HeaderImportForm::Mod
    {
        inline_trivia(input)?;
        let first_segment = input.run(from_fn(scan_word))?;
        let (prefix, terminal, terminal_end) =
            parse_use_path_and_terminal(input, first_segment, None)?;
        (HeaderImportForm::Mod, prefix, terminal, terminal_end)
    } else {
        let following_separator = input.maybe(from_fn(parse_use_separator))?;
        match classify_use_form(first, following_separator) {
            HeaderImportForm::Realm | HeaderImportForm::Band => {
                let form = classify_use_form(first, following_separator);
                if input.maybe(from_fn(parse_open_brace))?.is_some() {
                    let (terminal, terminal_end) = parse_use_group_terminal(input, None)?;
                    (form, empty_use_path(), terminal, terminal_end)
                } else {
                    let first_segment = input.run(from_fn(scan_word))?;
                    let (prefix, terminal, terminal_end) =
                        parse_use_path_and_terminal(input, first_segment, None)?;
                    (form, prefix, terminal, terminal_end)
                }
            }
            HeaderImportForm::Plain => {
                let (prefix, terminal, terminal_end) =
                    parse_use_path_and_terminal(input, first, following_separator)?;
                (HeaderImportForm::Plain, prefix, terminal, terminal_end)
            }
            HeaderImportForm::Mod => unreachable!("mod is handled before separator classification"),
        }
    };
    let aliases = parse_use_aliases(input)?;
    let end = aliases
        .last()
        .map_or(terminal_end, |alias| alias.range().end);

    Some(UseTree {
        range: start..end,
        form,
        prefix,
        terminal,
        aliases,
        qualifiers: UseQualifiers::default(),
    })
}

fn classify_use_form(
    first: WordSpan<'_>,
    following_separator: Option<UseSeparator>,
) -> HeaderImportForm {
    if first.text() == "mod" {
        HeaderImportForm::Mod
    } else if first.text() == "realm" && following_separator == Some(UseSeparator::Slash) {
        HeaderImportForm::Realm
    } else if first.text() == "band" && following_separator == Some(UseSeparator::ColonColon) {
        HeaderImportForm::Band
    } else {
        HeaderImportForm::Plain
    }
}

fn parse_use_path_and_terminal<'source, E>(
    input: &mut In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
    first: WordSpan<'source>,
    first_separator: Option<UseSeparator>,
) -> Option<(UsePath<'source>, UseTerminal<'source>, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut path = UsePath {
        segments: vec![UseSegment::Word(first)],
        separators: Vec::new(),
    };
    let mut pending_separator = first_separator;

    loop {
        let Some(current) = pending_separator
            .take()
            .or(input.maybe(from_fn(parse_use_separator))?)
        else {
            break;
        };
        if input.maybe(from_fn(parse_open_brace))?.is_some() {
            let (terminal, terminal_end) = parse_use_group_terminal(input, Some(current))?;
            return Some((path, terminal, terminal_end));
        }
        path.separators.push(current);
        path.segments
            .push(UseSegment::Word(input.run(from_fn(scan_word))?));
    }

    debug_assert_eq!(
        path.separators.len(),
        path.segments.len().saturating_sub(1),
        "a use path has one separator between each stored segment"
    );
    let end = path
        .segments()
        .last()
        .expect("use paths always contain their first segment")
        .range()
        .end;
    Some((path, UseTerminal::Single, end))
}

fn parse_use_group_terminal<'source, E>(
    input: &mut In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
    join: Option<UseSeparator>,
) -> Option<(UseTerminal<'source>, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut items = Vec::new();

    loop {
        consume_group_trivia(input)?;
        if let Some(close) = input.maybe(from_fn(parse_close_brace))? {
            return Some((UseTerminal::Group { join, items }, close.end));
        }

        items.push(parse_use_tree(input)?);

        let separator_has_newline = consume_group_trivia(input)?;
        if let Some(close) = input.maybe(from_fn(parse_close_brace))? {
            return Some((UseTerminal::Group { join, items }, close.end));
        }
        if input.maybe(from_fn(parse_comma))?.is_some() || separator_has_newline {
            continue;
        }
        return None;
    }
}

fn parse_use_aliases<'source, E>(
    input: &mut In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<Vec<WordSpan<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut aliases = Vec::new();
    while let Some(alias) = input.maybe(from_fn(parse_use_alias))? {
        aliases.push(alias);
    }
    Some(aliases)
}

fn parse_use_alias<'source, E>(
    mut input: In<'_, SourceInput<'source>, (), &mut ParseLocal, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut input)?;
    let keyword = input.run(from_fn(scan_word))?;
    (keyword.text() == "as").then_some(())?;
    inline_trivia(&mut input)?;
    input.run(from_fn(scan_word))
}

fn empty_use_path<'source>() -> UsePath<'source> {
    UsePath {
        segments: Vec::new(),
        separators: Vec::new(),
    }
}

fn consume_group_trivia<E>(
    input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = input.run(from_fn(scan_trivia))?;
    Some(input.input.source()[trivia.range()].contains(['\r', '\n']))
}

fn parse_open_brace<E>(mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = input.run(from_fn(scan_punctuation))?;
    (punctuation.kind() == PunctuationKind::Open(Delimiter::Brace)).then_some(())
}

fn parse_close_brace<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = input.run(from_fn(scan_punctuation))?;
    (punctuation.kind() == PunctuationKind::Close(Delimiter::Brace)).then(|| punctuation.range())
}

fn parse_comma<E>(mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = input.run(from_fn(scan_punctuation))?;
    (punctuation.kind() == PunctuationKind::Comma).then_some(())
}

fn parse_use_separator<E>(
    mut input: In<'_, SourceInput<'_>, (), &mut ParseLocal, E>,
) -> Option<UseSeparator>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = input.run(from_fn(scan_punctuation))?;
    match punctuation.kind() {
        PunctuationKind::ColonColon => Some(UseSeparator::ColonColon),
        PunctuationKind::Slash => Some(UseSeparator::Slash),
        _ => None,
    }
}

fn inline_trivia<E>(input: &mut In<'_, SourceInput<'_>, (), &mut ParseLocal, E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = input.run(from_fn(scan_trivia))?;
    let text = &input.input.source()[trivia.range()];
    (!text.is_empty() && !text.contains(['\r', '\n'])).then_some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::input::IsCut;

    const LEADING_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-plain/main.yu"
    ));
    const LEADING_MOD_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-mod/main.yu"
    ));
    const LEADING_REALM_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-realm/main.yu"
    ));
    const LEADING_BAND_USE_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/leading-use-band/main.yu"
    ));
    const INFIX_OPERATOR_SOURCE: &[u8] = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/contracts/phase2-parser/v0/cases/infix-operator-header/main.yu"
    ));

    #[test]
    fn classifies_all_leading_use_fixtures() {
        let cases = [
            (
                LEADING_USE_SOURCE,
                HeaderImportForm::Plain,
                0..13,
                &["std", "data"] as &[_],
            ),
            (
                LEADING_MOD_USE_SOURCE,
                HeaderImportForm::Mod,
                0..19,
                &["math", "value"],
            ),
            (
                LEADING_REALM_USE_SOURCE,
                HeaderImportForm::Realm,
                0..23,
                &["tools", "format"],
            ),
            (
                LEADING_BAND_USE_SOURCE,
                HeaderImportForm::Band,
                0..24,
                &["support", "value"],
            ),
        ];

        for (bytes, form, range, path) in cases {
            let source = std::str::from_utf8(bytes).expect("fixture is UTF-8");
            let (declaration, remainder) = parse_use(source);

            assert_eq!(declaration.range(), range, "{source:?}");
            assert_eq!(declaration.visibility(), Visibility::Private, "{source:?}");
            assert_eq!(declaration.tree().form(), form, "{source:?}");
            assert_eq!(path_texts(declaration.tree().prefix()), path, "{source:?}");
            assert_eq!(remainder, "\nmy value = 1\n", "{source:?}");

            let import = declaration
                .project_single_import()
                .expect("fixture use declaration should project");
            assert_eq!(import.range(), &range, "{source:?}");
            assert_eq!(import.form(), form, "{source:?}");
            assert_eq!(import.path(), path, "{source:?}");
            assert_eq!(import.visibility(), Visibility::Private, "{source:?}");
            assert_eq!(import.alias(), None, "{source:?}");
        }
    }

    #[test]
    fn keeps_non_marker_paths_plain() {
        let cases = [
            (
                "use realm::x",
                &["realm", "x"] as &[_],
                &[UseSeparator::ColonColon][..],
            ),
            ("use band/x", &["band", "x"], &[UseSeparator::Slash][..]),
            (
                "use a/b::c",
                &["a", "b", "c"],
                &[UseSeparator::Slash, UseSeparator::ColonColon][..],
            ),
        ];

        for (source, path, separators) in cases {
            let (declaration, remainder) = parse_use(source);

            assert_eq!(
                declaration.tree().form(),
                HeaderImportForm::Plain,
                "{source}"
            );
            assert_eq!(path_texts(declaration.tree().prefix()), path, "{source}");
            assert_eq!(
                declaration.tree().prefix().separators(),
                separators,
                "{source}"
            );
            assert_eq!(remainder, "", "{source}");
        }
    }

    #[test]
    fn projects_a_single_explicit_alias() {
        let (declaration, remainder) = parse_use("use std::data as collection");
        let import = declaration
            .project_single_import()
            .expect("one alias should project");

        assert_eq!(import.range(), &(0..27));
        assert_eq!(import.path(), ["std", "data"]);
        assert_eq!(import.alias(), Some("collection"));
        assert_eq!(remainder, "");
    }

    #[test]
    fn projects_operator_segments_by_their_canonical_spelling() {
        let declaration = UseDeclaration {
            range: 0..8,
            visibility: Visibility::Private,
            tree: UseTree {
                range: 4..8,
                form: HeaderImportForm::Plain,
                prefix: UsePath {
                    segments: vec![UseSegment::Operator {
                        range: 5..7,
                        text: "+!",
                    }],
                    separators: Vec::new(),
                },
                terminal: UseTerminal::Single,
                aliases: Vec::new(),
                qualifiers: UseQualifiers::default(),
            },
        };

        let import = declaration
            .project_single_import()
            .expect("single operator segment should project");

        assert_eq!(import.path(), ["+!"]);
        assert!(import.route().separators().is_empty());
    }

    #[test]
    fn preserves_distinct_plain_routes_during_projection() {
        let (slash, _) = parse_use("use a/b::c");
        let (colon_colon, _) = parse_use("use a::b::c");
        let slash = slash
            .project_single_import()
            .expect("slash route should project");
        let colon_colon = colon_colon
            .project_single_import()
            .expect("double-colon route should project");

        assert_eq!(slash.path(), colon_colon.path());
        assert_eq!(
            slash.route().separators(),
            [
                HeaderImportRouteSeparator::Slash,
                HeaderImportRouteSeparator::ColonColon,
            ]
        );
        assert_eq!(
            colon_colon.route().separators(),
            [
                HeaderImportRouteSeparator::ColonColon,
                HeaderImportRouteSeparator::ColonColon,
            ]
        );
        assert_ne!(slash.route(), colon_colon.route());
    }

    #[test]
    fn parses_a_simple_group_after_a_common_prefix() {
        let (declaration, remainder) = parse_use("use std::io::{read, write}");

        assert_eq!(path_texts(declaration.tree().prefix()), ["std", "io"]);
        assert_eq!(
            declaration.tree().prefix().separators(),
            [UseSeparator::ColonColon]
        );
        assert_eq!(remainder, "");

        let (join, items) = group_parts(declaration.tree());
        assert_eq!(join, Some(UseSeparator::ColonColon));
        assert_eq!(items.len(), 2);
        assert_eq!(path_texts(items[0].prefix()), ["read"]);
        assert_eq!(path_texts(items[1].prefix()), ["write"]);
        assert!(matches!(items[0].terminal(), UseTerminal::Single));
        assert!(matches!(items[1].terminal(), UseTerminal::Single));
    }

    #[test]
    fn parses_nested_groups_in_source_order() {
        let (declaration, remainder) = parse_use("use std::{io::{read, write}, fs}");

        let (_, outer_items) = group_parts(declaration.tree());
        assert_eq!(outer_items.len(), 2);
        assert_eq!(path_texts(outer_items[0].prefix()), ["io"]);
        assert_eq!(path_texts(outer_items[1].prefix()), ["fs"]);

        let (join, inner_items) = group_parts(&outer_items[0]);
        assert_eq!(join, Some(UseSeparator::ColonColon));
        assert_eq!(
            inner_items
                .iter()
                .map(|item| path_texts(item.prefix()))
                .collect::<Vec<_>>(),
            [vec!["read"], vec!["write"]]
        );
        assert_eq!(remainder, "");
    }

    #[test]
    fn accepts_newlines_as_group_item_separators() {
        let (declaration, remainder) = parse_use("use std::{\n  read\n  write,\n}");

        let (_, items) = group_parts(declaration.tree());
        assert_eq!(items.len(), 2);
        assert_eq!(path_texts(items[0].prefix()), ["read"]);
        assert_eq!(path_texts(items[1].prefix()), ["write"]);
        assert_eq!(remainder, "");
    }

    #[test]
    fn root_group_items_classify_their_own_forms() {
        let (declaration, remainder) = parse_use("use {mod math, realm/tools, band::support, std}");

        assert!(declaration.tree().prefix().segments().is_empty());
        let (_, items) = group_parts(declaration.tree());
        assert_eq!(
            items.iter().map(UseTree::form).collect::<Vec<_>>(),
            [
                HeaderImportForm::Mod,
                HeaderImportForm::Realm,
                HeaderImportForm::Band,
                HeaderImportForm::Plain,
            ]
        );
        assert_eq!(path_texts(items[0].prefix()), ["math"]);
        assert_eq!(path_texts(items[1].prefix()), ["tools"]);
        assert_eq!(path_texts(items[2].prefix()), ["support"]);
        assert_eq!(path_texts(items[3].prefix()), ["std"]);
        assert_eq!(remainder, "");
    }

    #[test]
    fn retains_every_alias_and_its_range() {
        let source = "use std::io::{read as one as two}";
        let (declaration, remainder) = parse_use(source);

        let (_, items) = group_parts(declaration.tree());
        assert_eq!(items.len(), 1);
        assert_eq!(
            items[0]
                .aliases()
                .iter()
                .map(|alias| alias.text())
                .collect::<Vec<_>>(),
            ["one", "two"]
        );
        assert_eq!(
            items[0]
                .aliases()
                .iter()
                .map(|alias| alias.range())
                .collect::<Vec<_>>(),
            [22..25, 29..32]
        );
        assert_eq!(remainder, "");
    }

    fn parse_use(source: &str) -> (UseDeclaration<'_>, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = input
            .run(from_fn(parse_declaration))
            .expect("leading use declaration should parse");

        let Declaration::Use(declaration) = declaration else {
            panic!("expected use declaration");
        };
        (declaration, input.input.remainder())
    }

    fn path_texts<'source>(path: &UsePath<'source>) -> Vec<&'source str> {
        path.segments()
            .iter()
            .map(|segment| match segment {
                UseSegment::Word(word) => word.text(),
                UseSegment::Operator { text, .. } => *text,
            })
            .collect()
    }

    fn group_parts<'tree, 'source>(
        tree: &'tree UseTree<'source>,
    ) -> (Option<UseSeparator>, &'tree [UseTree<'source>]) {
        let UseTerminal::Group { join, items } = tree.terminal() else {
            panic!("expected use group terminal: {tree:#?}");
        };
        (*join, items)
    }

    #[test]
    fn parses_binding_with_minimal_expression_from_chasa_input() {
        let source = "my value = 123\n";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = input
            .run(from_fn(parse_declaration))
            .expect("binding declaration should parse");

        let Declaration::Binding(binding) = declaration else {
            panic!("expected binding declaration");
        };
        assert_eq!(binding.range(), 0..14);
        assert_eq!(binding.name().text(), "value");
        assert_eq!(binding.value().range(), 11..14);
        assert_eq!(input.input.remainder(), "\n");
    }

    #[test]
    fn parses_infix_operator_header_fixture_from_chasa_input() {
        let source = std::str::from_utf8(INFIX_OPERATOR_SOURCE).expect("fixture is UTF-8");
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut input = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = input
            .run(from_fn(parse_declaration))
            .expect("operator header should parse");

        let Declaration::OperatorHeader(header) = declaration else {
            panic!("expected operator header declaration");
        };
        assert_eq!(header.range(), 0..19);
        assert_eq!(header.name(), "<+>");
        assert_eq!(header.left_binding_power().text(), "50");
        assert_eq!(header.right_binding_power().text(), "51");
        assert_eq!(input.input.remainder(), " left\nmy value = 1\n");
    }
}
