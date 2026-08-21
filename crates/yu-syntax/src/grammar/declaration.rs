//! Shared grammar for source-leading declarations.

use std::ops::Range;

use chasa::{
    ErrorSink, Input as _,
    error::std::{Unexpected, UnexpectedEndOfInput},
    parser::Parser as _,
    prelude::from_fn,
};

use crate::{
    BindingPower as HeaderBindingPower, BindingPowers, HeaderImport, HeaderImportForm,
    HeaderImportRoute, HeaderImportRouteSeparator, HeaderOperator, Visibility,
    grammar::expression::{Expression, parse_expression},
    operator::{BindingPower, OperatorFixity},
    scan::{
        punctuation::{PunctuationKind, scan_punctuation},
        trivia::scan_trivia,
        word::{WordSpan, scan_word},
    },
    session::{Delimiter, SynIn},
};

/// One parsed source-leading declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum Declaration<'source> {
    Use(UseDeclaration<'source>),
    Binding(BindingDeclaration<'source>),
    OperatorHeader(OperatorHeaderDeclaration<'source>),
}

/// A declaration shape that can contribute a source-leading header fact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum HeaderDeclaration<'source> {
    Use(UseDeclaration<'source>),
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

/// An operator signature before its opaque header body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorHeaderDeclaration<'source> {
    range: Range<usize>,
    name: &'source str,
    visibility: Visibility,
    lazy: bool,
    fixity: OperatorFixity,
    left_binding_power: Option<BindingPower>,
    right_binding_power: Option<BindingPower>,
}

impl<'source> OperatorHeaderDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn name(&self) -> &'source str {
        self.name
    }

    pub(crate) fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub(crate) fn is_lazy(&self) -> bool {
        self.lazy
    }

    pub(crate) fn fixity(&self) -> OperatorFixity {
        self.fixity
    }

    pub(crate) fn left_binding_power(&self) -> Option<&BindingPower> {
        self.left_binding_power.as_ref()
    }

    pub(crate) fn right_binding_power(&self) -> Option<&BindingPower> {
        self.right_binding_power.as_ref()
    }

    pub(crate) fn to_header_operator(&self) -> HeaderOperator {
        let binding_power = match self.fixity {
            OperatorFixity::Prefix => BindingPowers::prefix(header_binding_power(
                self.right_binding_power
                    .as_ref()
                    .expect("prefix headers require a right binding power"),
            )),
            OperatorFixity::Infix => BindingPowers::infix(
                header_binding_power(
                    self.left_binding_power
                        .as_ref()
                        .expect("infix headers require a left binding power"),
                ),
                header_binding_power(
                    self.right_binding_power
                        .as_ref()
                        .expect("infix headers require a right binding power"),
                ),
            ),
            OperatorFixity::Suffix => BindingPowers::suffix(header_binding_power(
                self.left_binding_power
                    .as_ref()
                    .expect("suffix headers require a left binding power"),
            )),
            OperatorFixity::Nullfix => BindingPowers::nullfix(),
        };
        HeaderOperator::new(
            self.range(),
            self.name.to_owned(),
            self.fixity,
            self.visibility,
            self.lazy,
            binding_power,
        )
    }
}

fn header_binding_power(binding_power: &BindingPower) -> HeaderBindingPower {
    HeaderBindingPower::from_components(binding_power.components().to_vec())
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

    /// Expands every complete single-target leaf in source order.
    pub(crate) fn expand_header_imports(&self) -> Vec<Result<HeaderImport, UseExpansionError>> {
        expand_use_tree(
            &self.tree,
            HeaderImportForm::Plain,
            &HeaderImportRoute::new(Vec::new(), Vec::new()),
            None,
            self.visibility,
            Some(self.range()),
        )
    }
}

/// Why a use declaration cannot yet project to one header import fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum UseSingleProjectionError {
    NonSingleTerminal,
    MultipleAliases,
    Qualifiers,
}

/// Why one use-tree branch cannot produce a complete header import fact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum UseExpansionError {
    FormConflict {
        range: Range<usize>,
        inherited_form: HeaderImportForm,
        form: HeaderImportForm,
    },
    GroupAlias {
        range: Range<usize>,
    },
    MultipleAliases {
        range: Range<usize>,
    },
    Qualifiers {
        range: Range<usize>,
    },
    UnsupportedGlob {
        range: Range<usize>,
    },
    MissingRouteJoin {
        range: Range<usize>,
    },
    MissingTarget {
        range: Range<usize>,
    },
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

fn expand_use_tree(
    tree: &UseTree<'_>,
    inherited_form: HeaderImportForm,
    inherited_route: &HeaderImportRoute,
    pending_join: Option<UseSeparator>,
    visibility: Visibility,
    root_range: Option<Range<usize>>,
) -> Vec<Result<HeaderImport, UseExpansionError>> {
    let effective_form = if tree.form == HeaderImportForm::Plain {
        inherited_form
    } else if inherited_route.segments().is_empty() {
        tree.form
    } else {
        return vec![Err(UseExpansionError::FormConflict {
            range: tree.range(),
            inherited_form,
            form: tree.form,
        })];
    };
    if !tree.qualifiers.is_empty() {
        return vec![Err(UseExpansionError::Qualifiers {
            range: tree.range(),
        })];
    }

    let route = match concatenate_use_route(inherited_route, pending_join, &tree.prefix) {
        Ok(route) => route,
        Err(error) => return vec![Err(error)],
    };

    match &tree.terminal {
        UseTerminal::Single => {
            if route.segments().is_empty() {
                return vec![Err(UseExpansionError::MissingTarget {
                    range: tree.range(),
                })];
            }
            let alias = match tree.aliases.as_slice() {
                [] => None,
                [alias] => Some(alias.text().to_owned()),
                _ => {
                    return vec![Err(UseExpansionError::MultipleAliases {
                        range: tree.range(),
                    })];
                }
            };
            let range = root_range.unwrap_or_else(|| tree.range());
            vec![Ok(HeaderImport::new(
                range,
                effective_form,
                route,
                visibility,
                alias,
            ))]
        }
        UseTerminal::Group { join, items } => {
            if !tree.aliases.is_empty() {
                return vec![Err(UseExpansionError::GroupAlias {
                    range: tree.range(),
                })];
            }
            items
                .iter()
                .flat_map(|item| {
                    expand_use_tree(item, effective_form, &route, *join, visibility, None)
                })
                .collect()
        }
        UseTerminal::Glob { .. } => vec![Err(UseExpansionError::UnsupportedGlob {
            range: tree.range(),
        })],
    }
}

fn concatenate_use_route(
    inherited: &HeaderImportRoute,
    pending_join: Option<UseSeparator>,
    suffix: &UsePath<'_>,
) -> Result<HeaderImportRoute, UseExpansionError> {
    let mut segments = inherited.segments().to_vec();
    let mut separators = inherited.separators().to_vec();

    if !suffix.segments().is_empty() {
        if !segments.is_empty() {
            let Some(join) = pending_join else {
                return Err(UseExpansionError::MissingRouteJoin {
                    range: suffix.segments()[0].range(),
                });
            };
            separators.push(project_use_separator(join));
        }
        let suffix_route = project_use_route(suffix);
        segments.extend_from_slice(suffix_route.segments());
        separators.extend_from_slice(suffix_route.separators());
    }

    Ok(HeaderImportRoute::new(segments, separators))
}

fn project_use_separator(separator: UseSeparator) -> HeaderImportRouteSeparator {
    match separator {
        UseSeparator::ColonColon => HeaderImportRouteSeparator::ColonColon,
        UseSeparator::Slash => HeaderImportRouteSeparator::Slash,
    }
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

impl<'source> UseVersion<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn text(&self) -> &'source str {
        self.text
    }
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
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<Declaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.choice((
        parse_use_declaration.map(Declaration::Use),
        parse_binding_declaration.map(Declaration::Binding),
        parse_operator_header.map(Declaration::OperatorHeader),
    ))
}

/// Parses only declaration forms that are valid in the source-leading header.
///
/// Binding declarations intentionally remain absent: encountering one ends
/// header discovery without making it a syntax error.
pub(crate) fn parse_header_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<HeaderDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.choice((
        parse_use_declaration.map(HeaderDeclaration::Use),
        parse_operator_header.map(HeaderDeclaration::OperatorHeader),
    ))
}

fn parse_operator_header<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<OperatorHeaderDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let first = i.run(scan_word)?;
    let (visibility, fixity_keyword) = match first.text() {
        "pub" => (
            Visibility::Public,
            parse_operator_header_word_after_trivia(&mut i)?,
        ),
        "my" => (
            Visibility::Private,
            parse_operator_header_word_after_trivia(&mut i)?,
        ),
        "our" => (
            Visibility::Our,
            parse_operator_header_word_after_trivia(&mut i)?,
        ),
        _ => (Visibility::Private, first),
    };
    let (lazy, fixity_keyword) = if fixity_keyword.text() == "lazy" {
        (true, parse_operator_header_word_after_trivia(&mut i)?)
    } else {
        (false, fixity_keyword)
    };
    let fixity = parse_operator_fixity(fixity_keyword)?;

    optional_inline_trivia(&mut i)?;
    let open = i.run(scan_punctuation)?;
    (open.kind() == PunctuationKind::Open(Delimiter::Parenthesis)).then_some(())?;
    let name = parse_operator_name(&mut i)?;
    let close = i.run(scan_punctuation)?;
    (close.kind() == PunctuationKind::Close(Delimiter::Parenthesis)).then_some(())?;

    let (left_binding_power, right_binding_power) = match fixity {
        OperatorFixity::Nullfix => (None, None),
        OperatorFixity::Prefix => {
            optional_inline_trivia(&mut i)?;
            (None, Some(i.run(parse_binding_power)?))
        }
        OperatorFixity::Suffix => {
            optional_inline_trivia(&mut i)?;
            (Some(i.run(parse_binding_power)?), None)
        }
        OperatorFixity::Infix => {
            optional_inline_trivia(&mut i)?;
            let left = i.run(parse_binding_power)?;
            optional_inline_trivia(&mut i)?;
            let right = i.run(parse_binding_power)?;
            (Some(left), Some(right))
        }
    };
    optional_inline_trivia(&mut i)?;
    i.skip(chasa::prelude::item('='))?;
    let end = i.pos();

    Some(OperatorHeaderDeclaration {
        range: start..end,
        name,
        visibility,
        lazy,
        fixity,
        left_binding_power,
        right_binding_power,
    })
}

fn parse_operator_header_word_after_trivia<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(i)?;
    i.run(scan_word)
}

fn parse_operator_fixity(word: WordSpan<'_>) -> Option<OperatorFixity> {
    match word.text() {
        "prefix" => Some(OperatorFixity::Prefix),
        "infix" => Some(OperatorFixity::Infix),
        "suffix" => Some(OperatorFixity::Suffix),
        "nullfix" => Some(OperatorFixity::Nullfix),
        _ => None,
    }
}

fn parse_operator_name<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<&'source str>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    while let Some(character) = i.input.remainder().chars().next() {
        if character == ')' {
            break;
        }
        (!character.is_whitespace()
            && !matches!(
                character,
                '(' | '[' | ']' | '{' | '}' | '\\' | ',' | ';' | '"' | '\''
            ))
        .then_some(())?;
        i.input.next()?;
    }
    let end = i.pos();
    (start < end).then_some(&i.input.source()[start..end])
}

/// Parses the dot-separated binding-power vector used by operator headers.
fn parse_binding_power<E>(
    i: SynIn<E>,
) -> Option<BindingPower>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut components = Vec::new();

    loop {
        let start = i.pos();
        while i
            .input
            .remainder()
            .chars()
            .next()
            .is_some_and(|character| character.is_ascii_digit())
        {
            i.input.next()?;
        }
        let end = i.pos();
        (start < end).then_some(())?;
        components.push(i.input.source()[start..end].parse::<i8>().ok()?);

        if !i.input.remainder().starts_with('.') {
            break;
        }
        i.input.next()?;
    }

    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);

    let (first, rest) = components.split_first()?;
    Some(BindingPower::new(*first, rest.iter().copied()))
}

fn parse_binding_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<BindingDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let keyword = i.run(scan_word)?;
    (keyword.text() == "my").then_some(())?;
    inline_trivia(&mut i)?;
    let name = i.run(scan_word)?;
    inline_trivia(&mut i)?;
    i.skip(chasa::prelude::item('='))?;
    inline_trivia(&mut i)?;
    let value = i.run(parse_expression)?;
    let end = value.range().end;

    Some(BindingDeclaration {
        range: start..end,
        name,
        value,
    })
}

fn parse_use_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let keyword = i.run(scan_word)?;
    (keyword.text() == "use").then_some(())?;
    inline_trivia(&mut i)?;

    let tree = parse_use_tree(&mut i)?;
    let end = tree.range().end;

    Some(UseDeclaration {
        range: start..end,
        visibility: Visibility::Private,
        tree,
    })
}

fn parse_use_tree<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<UseTree<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    if i.maybe(from_fn(parse_open_brace))?.is_some() {
        let (terminal, terminal_end) = parse_use_group_terminal(i, None)?;
        let aliases = parse_use_aliases(i)?;
        let alias_end = aliases
            .last()
            .map_or(terminal_end, |alias| alias.range().end);
        let (qualifiers, qualifier_end) = parse_use_qualifiers(i)?;
        let end = qualifier_end.unwrap_or(alias_end);
        return Some(UseTree {
            range: start..end,
            form: HeaderImportForm::Plain,
            prefix: empty_use_path(),
            terminal,
            aliases,
            qualifiers,
        });
    }

    if let Some(first) = i.maybe(from_fn(parse_parenthesized_use_operator))? {
        let (prefix, terminal, terminal_end) = parse_use_path_and_terminal(i, first, None)?;
        return finish_use_tree(
            i,
            start,
            HeaderImportForm::Plain,
            prefix,
            terminal,
            terminal_end,
        );
    }

    let first = i.run(scan_word)?;

    let (form, prefix, mut terminal, terminal_end) = if classify_use_form(first, None)
        == HeaderImportForm::Mod
    {
        inline_trivia(i)?;
        let first_segment = parse_use_path_segment(i)?;
        let (prefix, terminal, terminal_end) = parse_use_path_and_terminal(i, first_segment, None)?;
        (HeaderImportForm::Mod, prefix, terminal, terminal_end)
    } else {
        let following_separator = i.maybe(from_fn(parse_use_separator))?;
        match classify_use_form(first, following_separator) {
            HeaderImportForm::Realm | HeaderImportForm::Band => {
                let form = classify_use_form(first, following_separator);
                if i.maybe(from_fn(parse_open_brace))?.is_some() {
                    let (terminal, terminal_end) = parse_use_group_terminal(i, None)?;
                    (form, empty_use_path(), terminal, terminal_end)
                } else {
                    let first_segment = parse_use_path_segment(i)?;
                    let (prefix, terminal, terminal_end) =
                        parse_use_path_and_terminal(i, first_segment, None)?;
                    (form, prefix, terminal, terminal_end)
                }
            }
            HeaderImportForm::Plain => {
                let (prefix, terminal, terminal_end) =
                    parse_use_path_and_terminal(i, UseSegment::Word(first), following_separator)?;
                (HeaderImportForm::Plain, prefix, terminal, terminal_end)
            }
            HeaderImportForm::Mod => unreachable!("mod is handled before separator classification"),
        }
    };
    finish_use_tree(i, start, form, prefix, terminal, terminal_end)
}

fn finish_use_tree<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
    start: usize,
    form: HeaderImportForm,
    prefix: UsePath<'source>,
    mut terminal: UseTerminal<'source>,
    terminal_end: usize,
) -> Option<UseTree<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let aliases = parse_use_aliases(i)?;
    let tail_end = aliases
        .last()
        .map_or(terminal_end, |alias| alias.range().end);
    let without_end = if let UseTerminal::Glob { without, .. } = &mut terminal {
        parse_use_without(i)?.map(|(parsed_without, end)| {
            *without = parsed_without;
            end
        })
    } else {
        None
    };
    let qualifier_input_end = without_end.unwrap_or(tail_end);
    let (qualifiers, qualifier_end) = parse_use_qualifiers(i)?;
    let end = qualifier_end.unwrap_or(qualifier_input_end);

    Some(UseTree {
        range: start..end,
        form,
        prefix,
        terminal,
        aliases,
        qualifiers,
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
    i: &mut SynIn<'_, 'source, '_, E>,
    first: UseSegment<'source>,
    first_separator: Option<UseSeparator>,
) -> Option<(UsePath<'source>, UseTerminal<'source>, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut path = UsePath {
        segments: vec![first],
        separators: Vec::new(),
    };
    let mut pending_separator = first_separator;

    loop {
        let Some(current) = pending_separator
            .take()
            .or(i.maybe(from_fn(parse_use_separator))?)
        else {
            break;
        };
        if i.maybe(from_fn(parse_open_brace))?.is_some() {
            let (terminal, terminal_end) = parse_use_group_terminal(i, Some(current))?;
            return Some((path, terminal, terminal_end));
        }
        if let Some(range) = i.maybe(from_fn(parse_use_glob))? {
            return Some((
                path,
                UseTerminal::Glob {
                    join: Some(current),
                    without: Vec::new(),
                },
                range.end,
            ));
        }
        path.separators.push(current);
        path.segments.push(parse_use_path_segment(i)?);
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
    i: &mut SynIn<'_, 'source, '_, E>,
    join: Option<UseSeparator>,
) -> Option<(UseTerminal<'source>, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut items = Vec::new();

    loop {
        consume_group_trivia(i)?;
        if let Some(close) = i.maybe(from_fn(parse_close_brace))? {
            return Some((UseTerminal::Group { join, items }, close.end));
        }

        items.push(parse_use_tree(i)?);

        let separator_has_newline = consume_group_trivia(i)?;
        if let Some(close) = i.maybe(from_fn(parse_close_brace))? {
            return Some((UseTerminal::Group { join, items }, close.end));
        }
        if i.maybe(from_fn(parse_comma))?.is_some() || separator_has_newline {
            continue;
        }
        return None;
    }
}

fn parse_use_aliases<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Vec<WordSpan<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut aliases = Vec::new();
    while let Some(alias) = i.maybe(from_fn(parse_use_alias))? {
        aliases.push(alias);
    }
    Some(aliases)
}

fn parse_use_alias<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut i)?;
    let keyword = i.run(scan_word)?;
    (keyword.text() == "as").then_some(())?;
    inline_trivia(&mut i)?;
    i.run(scan_word)
}

fn parse_use_qualifiers<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<(UseQualifiers<'source>, Option<usize>)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let version = i.maybe(from_fn(parse_use_version_suffix))?;
    let anchor = parse_use_anchor(i)?;
    let end = anchor
        .as_ref()
        .and_then(use_path_end)
        .or_else(|| version.as_ref().map(|version| version.range.end));

    Some((UseQualifiers { version, anchor }, end))
}

fn parse_use_version_suffix<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseVersion<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut i)?;
    i.run(scan_use_version)
}

fn scan_use_version<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseVersion<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    i.skip(chasa::prelude::item('v'))?;
    i.input
        .remainder()
        .chars()
        .next()
        .is_some_and(|character| character.is_ascii_digit())
        .then_some(())?;
    i.input.next()?;

    while i.input.remainder().chars().next().is_some_and(|character| {
        character.is_ascii_alphanumeric() || matches!(character, '.' | '-' | '+')
    }) {
        i.input.next()?;
    }

    let end = i.pos();
    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);

    Some(UseVersion {
        range: start..end,
        text: &i.input.source()[start..end],
    })
}

fn parse_use_anchor<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Option<UsePath<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let Some(()) = i.maybe(from_fn(parse_with_keyword))? else {
        return Some(None);
    };
    inline_trivia(i)?;

    let first = i.run(scan_word)?;
    let mut path = UsePath {
        segments: vec![UseSegment::Word(first)],
        separators: Vec::new(),
    };

    while let Some(separator) = i.maybe(from_fn(parse_use_separator))? {
        path.separators.push(separator);
        path.segments.push(UseSegment::Word(i.run(scan_word)?));
    }

    debug_assert_eq!(
        path.separators.len(),
        path.segments.len().saturating_sub(1),
        "an anchor path has one separator between each identifier segment"
    );
    Some(Some(path))
}

fn parse_with_keyword<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut i)?;
    let keyword = i.run(scan_word)?;
    (keyword.text() == "with").then_some(())
}

fn use_path_end(path: &UsePath<'_>) -> Option<usize> {
    path.segments().last().map(|segment| segment.range().end)
}

fn parse_use_without<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Option<(Vec<UseExclusion<'source>>, usize)>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.maybe(from_fn(parse_use_without_clause))
}

fn parse_use_without_clause<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<(Vec<UseExclusion<'source>>, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut i)?;
    let keyword = i.run(scan_word)?;
    (keyword.text() == "without").then_some(())?;
    inline_trivia(&mut i)?;

    let mut exclusions = vec![parse_use_exclusion(&mut i)?];
    while i.maybe(from_fn(parse_comma))?.is_some() {
        i.run(scan_trivia)?;
        exclusions.push(parse_use_exclusion(&mut i)?);
    }
    let end = exclusion_range(exclusions.last().expect("without has one exclusion")).end;

    Some((exclusions, end))
}

fn parse_use_exclusion<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<UseExclusion<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(segment) = i.maybe(from_fn(parse_parenthesized_use_operator))? {
        return Some(UseExclusion::Segment(segment));
    }
    if let Some(group) = i.maybe(from_fn(parse_use_exclusion_group))? {
        return Some(group);
    }
    if let Some(range) = i.maybe(from_fn(parse_use_glob))? {
        return Some(UseExclusion::Glob { range });
    }

    i.run(scan_word)
        .map(|word| UseExclusion::Segment(UseSegment::Word(word)))
}

fn parse_parenthesized_use_operator<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseSegment<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let open = i.run(scan_open_parenthesis)?;
    let start = i.pos();

    while let Some(character) = i.input.remainder().chars().next() {
        if character == ')' {
            break;
        }
        is_use_operator_character(character).then_some(())?;
        i.input.next()?;
    }

    let end = i.pos();
    (start < end).then_some(())?;
    i.run(scan_close_parenthesis)?;
    Some(UseSegment::Operator {
        range: open.start..i.pos(),
        text: &i.input.source()[start..end],
    })
}

/// Recognizes either spelling permitted in normal use-path segment slots.
///
/// Parenthesized operators are deliberately tried before words so `(+)` is
/// retained as one operator segment rather than being left to a terminal
/// group branch. Both the spec-start and separator-target callers use this
/// shared recognizer.
fn parse_use_path_segment<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<UseSegment<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(segment) = i.maybe(from_fn(parse_parenthesized_use_operator))? {
        return Some(segment);
    }
    i.run(scan_word).map(UseSegment::Word)
}

fn is_use_operator_character(character: char) -> bool {
    !character.is_whitespace()
        && character != '_'
        && !unicode_ident::is_xid_continue(character)
        && !matches!(
            character,
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';'
        )
}

fn parse_use_exclusion_group<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseExclusion<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let open = i.run(scan_punctuation)?;
    let delimiter = match open.kind() {
        PunctuationKind::Open(Delimiter::Parenthesis) => Delimiter::Parenthesis,
        PunctuationKind::Open(Delimiter::Brace) => Delimiter::Brace,
        _ => return None,
    };
    let start = open.range().start;
    let mut items = Vec::new();

    loop {
        consume_group_trivia(&mut i)?;
        if let Some(close) = i.maybe(from_fn(|i| parse_close_delimiter(delimiter, i)))? {
            return Some(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }

        items.push(parse_use_tree(&mut i)?);

        let separator_has_newline = consume_group_trivia(&mut i)?;
        if let Some(close) = i.maybe(from_fn(|i| parse_close_delimiter(delimiter, i)))? {
            return Some(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }
        if i.maybe(from_fn(parse_comma))?.is_some() || separator_has_newline {
            continue;
        }
        return None;
    }
}

fn parse_use_glob<E>(mut i: SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let start = i.pos();
    i.skip(chasa::prelude::item('*'))?;
    let end = i.pos();

    let mut line = i.local.line();
    line.at_line_start = false;
    i.local.set_line(line);

    Some(start..end)
}

fn exclusion_range(exclusion: &UseExclusion<'_>) -> Range<usize> {
    match exclusion {
        UseExclusion::Segment(segment) => segment.range(),
        UseExclusion::Glob { range } | UseExclusion::Group { range, .. } => range.clone(),
    }
}

fn empty_use_path<'source>() -> UsePath<'source> {
    UsePath {
        segments: Vec::new(),
        separators: Vec::new(),
    }
}

fn consume_group_trivia<E>(i: &mut SynIn<E>) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    Some(i.input.source()[trivia.range()].contains(['\r', '\n']))
}

fn parse_open_brace<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Open(Delimiter::Brace)).then_some(())
}

fn scan_open_parenthesis<E>(
    mut i: SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Open(Delimiter::Parenthesis))
        .then(|| punctuation.range())
}

fn scan_close_parenthesis<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Close(Delimiter::Parenthesis)).then_some(())
}

fn parse_close_delimiter<E>(
    delimiter: Delimiter,
    mut i: SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Close(delimiter)).then(|| punctuation.range())
}

fn parse_close_brace<E>(
    mut i: SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Close(Delimiter::Brace)).then(|| punctuation.range())
}

fn parse_comma<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Comma).then_some(())
}

fn parse_use_separator<E>(
    mut i: SynIn<E>,
) -> Option<UseSeparator>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    match punctuation.kind() {
        PunctuationKind::ColonColon => Some(UseSeparator::ColonColon),
        PunctuationKind::Slash => Some(UseSeparator::Slash),
        _ => None,
    }
}

fn inline_trivia<E>(i: &mut SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    let text = &i.input.source()[trivia.range()];
    (!text.is_empty() && !text.contains(['\r', '\n'])).then_some(())
}

fn optional_inline_trivia<E>(i: &mut SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    (!i.input.source()[trivia.range()].contains(['\r', '\n'])).then_some(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use chasa::{input::IsCut, prelude::In};

    use crate::{input::SourceInput, session::ParseLocal};

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
    fn parses_scalar_and_vector_operator_binding_powers() {
        for (source, expected) in [("50", &[50][..]), ("5.0.1", &[5, 0, 1][..])] {
            let (binding_power, remainder) = parse_operator_binding_power(source);

            assert_eq!(binding_power.components(), expected, "{source}");
            assert_eq!(remainder, "", "{source}");
        }
    }

    #[test]
    fn parses_every_operator_header_fixity_with_its_binding_power_shape() {
        let cases = [
            ("nullfix (+) = body", OperatorFixity::Nullfix, None, None),
            (
                "prefix (not) 7.0 = body",
                OperatorFixity::Prefix,
                None,
                Some(&[7, 0][..]),
            ),
            (
                "suffix (!) 8 = body",
                OperatorFixity::Suffix,
                Some(&[8][..]),
                None,
            ),
            (
                "infix (+) 5.0.0 5.0.1 = body",
                OperatorFixity::Infix,
                Some(&[5, 0, 0][..]),
                Some(&[5, 0, 1][..]),
            ),
        ];

        for (source, fixity, left, right) in cases {
            let (header, remainder) = parse_operator_header_declaration(source);

            assert_eq!(header.fixity(), fixity, "{source}");
            assert_eq!(
                header.left_binding_power().map(BindingPower::components),
                left,
                "{source}"
            );
            assert_eq!(
                header.right_binding_power().map(BindingPower::components),
                right,
                "{source}"
            );
            assert_eq!(remainder, " body", "{source}");
        }
    }

    #[test]
    fn parses_operator_header_visibility_and_lazy_modifier() {
        let (public, public_remainder) =
            parse_operator_header_declaration("pub lazy infix(and) 2.0.0 2.0.1 = body");
        let (private, private_remainder) =
            parse_operator_header_declaration("my prefix (-) 8 = body");
        let (our, our_remainder) = parse_operator_header_declaration("our suffix (!) 8 = body");

        assert_eq!(public.visibility(), Visibility::Public);
        assert!(public.is_lazy());
        assert_eq!(private.visibility(), Visibility::Private);
        assert!(!private.is_lazy());
        assert_eq!(our.visibility(), Visibility::Our);
        assert_eq!(public_remainder, " body");
        assert_eq!(private_remainder, " body");
        assert_eq!(our_remainder, " body");

        let projected = public.to_header_operator();
        assert_eq!(projected.range(), &(0..33));
        assert_eq!(projected.name(), "and");
        assert_eq!(projected.visibility(), Visibility::Public);
        assert!(projected.is_lazy());
        assert_eq!(
            projected
                .binding_power()
                .right()
                .map(HeaderBindingPower::components),
            Some(&[2, 0, 1][..])
        );
    }

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
    fn parses_a_glob_only_after_a_path_separator() {
        let (declaration, remainder) = parse_use("use std::*");

        assert_eq!(path_texts(declaration.tree().prefix()), ["std"]);
        let (join, without) = glob_parts(declaration.tree());
        assert_eq!(join, Some(UseSeparator::ColonColon));
        assert!(without.is_empty());
        assert_eq!(remainder, "");
        assert!(!parses_declaration("use *"));
    }

    #[test]
    fn parses_name_and_glob_exclusions_after_without() {
        let (name_declaration, _) = parse_use("use std::* without foo");
        let (_, name_without) = glob_parts(name_declaration.tree());
        assert_eq!(name_without.len(), 1);
        assert_eq!(exclusion_segment_text(&name_without[0]), Some("foo"));

        let (glob_declaration, _) = parse_use("use std::* without *");
        let (_, glob_without) = glob_parts(glob_declaration.tree());
        assert_eq!(glob_without.len(), 1);
        assert!(matches!(glob_without[0], UseExclusion::Glob { .. }));
    }

    #[test]
    fn retains_glob_aliases_before_parsing_without() {
        let (declaration, _) = parse_use("use std::* as all without foo");
        let (_, without) = glob_parts(declaration.tree());

        assert_eq!(
            declaration
                .tree()
                .aliases()
                .iter()
                .map(|alias| alias.text())
                .collect::<Vec<_>>(),
            ["all"]
        );
        assert_eq!(exclusion_segment_text(&without[0]), Some("foo"));
    }

    #[test]
    fn parses_parenthesized_exclusion_groups() {
        let (declaration, _) = parse_use("use std::* without (a, b)");
        let (_, without) = glob_parts(declaration.tree());

        let [UseExclusion::Group { items, .. }] = without else {
            panic!("expected one parenthesized exclusion group: {without:#?}");
        };
        assert_eq!(items.len(), 2);
        assert_eq!(path_texts(items[0].prefix()), ["a"]);
        assert_eq!(path_texts(items[1].prefix()), ["b"]);
    }

    #[test]
    fn parses_brace_exclusion_groups() {
        let (declaration, _) = parse_use("use std::* without {a, b}");
        let (_, without) = glob_parts(declaration.tree());

        let [UseExclusion::Group { items, .. }] = without else {
            panic!("expected one brace exclusion group: {without:#?}");
        };
        assert_eq!(
            items
                .iter()
                .map(|item| path_texts(item.prefix()))
                .collect::<Vec<_>>(),
            [vec!["a"], vec!["b"]]
        );
    }

    #[test]
    fn keeps_parenthesized_operator_names_distinct_from_glob_exclusions() {
        let (declaration, _) = parse_use("use std::* without (*)");
        let (_, without) = glob_parts(declaration.tree());

        let [UseExclusion::Segment(UseSegment::Operator { text, .. })] = without else {
            panic!("expected parenthesized star to remain an operator segment: {without:#?}");
        };
        assert_eq!(*text, "*");
    }

    #[test]
    fn accepts_parenthesized_operator_segments_at_normal_path_positions() {
        let (at_spec_start, remainder) = parse_use("use (+)::value");
        assert_eq!(remainder, "");
        let [
            UseSegment::Operator { range, text },
            UseSegment::Word(word),
        ] = at_spec_start.tree().prefix().segments()
        else {
            panic!("expected an operator followed by a word path segment");
        };
        assert_eq!(range, &(4..7));
        assert_eq!(*text, "+");
        assert_eq!(word.text(), "value");

        let (at_separator_target, remainder) = parse_use("use std::(+)::value");
        assert_eq!(remainder, "");
        assert_eq!(
            path_texts(at_separator_target.tree().prefix()),
            ["std", "+", "value"]
        );
        assert_eq!(
            at_separator_target.tree().prefix().separators(),
            [UseSeparator::ColonColon, UseSeparator::ColonColon]
        );
    }

    #[test]
    fn parses_a_typed_version_suffix() {
        let (declaration, remainder) = parse_use("use std::data v1.2.3");
        let qualifiers = declaration.tree().qualifiers();
        let version = qualifiers.version().expect("version suffix should parse");

        assert_eq!(version.text(), "v1.2.3");
        assert_eq!(version.range(), 14..20);
        assert!(qualifiers.anchor().is_none());
        assert_eq!(declaration.range(), 0..20);
        assert_eq!(remainder, "");
        assert_eq!(
            declaration.project_single_import(),
            Err(UseSingleProjectionError::Qualifiers)
        );
        assert!(matches!(
            declaration.expand_header_imports().as_slice(),
            [Err(UseExpansionError::Qualifiers { .. })]
        ));
    }

    #[test]
    fn preserves_the_full_version_token_spelling() {
        let (declaration, _) = parse_use("use std::data v1-alpha+build.2");

        assert_eq!(
            declaration
                .tree()
                .qualifiers()
                .version()
                .map(UseVersion::text),
            Some("v1-alpha+build.2")
        );
    }

    #[test]
    fn parses_an_identifier_path_anchor() {
        let (declaration, remainder) = parse_use("use std::data with program::ui");
        let qualifiers = declaration.tree().qualifiers();
        let anchor = qualifiers.anchor().expect("anchor should parse");

        assert!(qualifiers.version().is_none());
        assert_eq!(path_texts(anchor), ["program", "ui"]);
        assert_eq!(anchor.separators(), [UseSeparator::ColonColon]);
        assert_eq!(declaration.range(), 0..30);
        assert_eq!(remainder, "");
    }

    #[test]
    fn parses_version_then_anchor_in_source_order() {
        let (declaration, remainder) = parse_use("use std::data v1.2.3 with program::ui");
        let qualifiers = declaration.tree().qualifiers();

        assert_eq!(qualifiers.version().map(UseVersion::text), Some("v1.2.3"));
        assert_eq!(
            path_texts(qualifiers.anchor().expect("anchor should parse")),
            ["program", "ui"]
        );
        assert_eq!(declaration.range(), 0..37);
        assert_eq!(remainder, "");
    }

    #[test]
    fn parses_qualifiers_on_group_items_and_glob_tails() {
        let (group, _) = parse_use("use std::{read v1, write with program::ui}");
        let (_, items) = group_parts(group.tree());
        assert_eq!(
            items[0].qualifiers().version().map(UseVersion::text),
            Some("v1")
        );
        assert_eq!(
            path_texts(items[1].qualifiers().anchor().expect("anchor should parse")),
            ["program", "ui"]
        );
        assert_eq!(items[0].range(), 10..17);
        assert_eq!(items[1].range(), 19..41);

        let (glob, _) = parse_use("use std::* without foo v1.2.3 with program::ui");
        let (_, without) = glob_parts(glob.tree());
        assert_eq!(exclusion_segment_text(&without[0]), Some("foo"));
        assert_eq!(
            glob.tree().qualifiers().version().map(UseVersion::text),
            Some("v1.2.3")
        );
        assert_eq!(
            path_texts(
                glob.tree()
                    .qualifiers()
                    .anchor()
                    .expect("anchor should parse")
            ),
            ["program", "ui"]
        );
    }

    #[test]
    fn rejects_non_identifier_anchor_targets() {
        for source in [
            "use std::data with {program}",
            "use std::data with *",
            "use std::data with (*)",
        ] {
            assert!(!parses_declaration(source), "{source}");
        }
    }

    #[test]
    fn expands_a_common_prefix_group_into_independent_imports() {
        let (declaration, remainder) = parse_use("use std::io::{read, write}");
        let imports = complete_expansions(&declaration);

        assert_eq!(imports.len(), 2);
        assert_eq!(imports[0].range(), &(14..18));
        assert_eq!(imports[1].range(), &(20..25));
        assert_eq!(imports[0].path(), ["std", "io", "read"]);
        assert_eq!(imports[1].path(), ["std", "io", "write"]);
        assert!(imports.iter().all(|import| {
            import.route().separators()
                == [
                    HeaderImportRouteSeparator::ColonColon,
                    HeaderImportRouteSeparator::ColonColon,
                ]
        }));
        assert!(imports.iter().all(|import| import.alias().is_none()));
        assert!(
            imports
                .iter()
                .all(|import| import.visibility() == Visibility::Private)
        );
        assert_eq!(remainder, "");
    }

    #[test]
    fn expands_nested_groups_in_depth_first_source_order() {
        let (declaration, _) = parse_use("use std::{io::{read, write}, fs}");
        let imports = complete_expansions(&declaration);

        assert_eq!(
            imports.iter().map(HeaderImport::path).collect::<Vec<_>>(),
            [
                &["std".to_owned(), "io".to_owned(), "read".to_owned()][..],
                &["std".to_owned(), "io".to_owned(), "write".to_owned()][..],
                &["std".to_owned(), "fs".to_owned()][..],
            ]
        );
    }

    #[test]
    fn does_not_emit_records_for_an_empty_group() {
        let (declaration, remainder) = parse_use("use std::io::{}");

        assert!(declaration.expand_header_imports().is_empty());
        assert_eq!(remainder, "");
    }

    #[test]
    fn keeps_complete_siblings_when_one_group_item_has_a_form_conflict() {
        let (declaration, _) = parse_use("use std::{realm/tools, plain}");
        let results = declaration.expand_header_imports();

        assert!(matches!(
            results[0],
            Err(UseExpansionError::FormConflict {
                inherited_form: HeaderImportForm::Plain,
                form: HeaderImportForm::Realm,
                ..
            })
        ));
        let import = results[1]
            .as_ref()
            .expect("the complete sibling should still expand");
        assert_eq!(import.path(), ["std", "plain"]);
        assert_eq!(import.form(), HeaderImportForm::Plain);
    }

    #[test]
    fn rejects_an_alias_on_a_group_without_expanding_its_children() {
        let (declaration, _) = parse_use("use std::{read} as selected");

        assert_eq!(
            declaration.expand_header_imports(),
            vec![Err(UseExpansionError::GroupAlias { range: 4..27 })]
        );
    }

    #[test]
    fn rejects_repeated_aliases_on_a_single_branch() {
        let (declaration, _) = parse_use("use std::data as first as second");

        assert_eq!(
            declaration.expand_header_imports(),
            vec![Err(UseExpansionError::MultipleAliases { range: 4..32 })]
        );
    }

    #[test]
    fn keeps_complete_siblings_when_a_recovered_item_has_no_target() {
        let (mut declaration, _) = parse_use("use {missing, complete}");
        let UseTerminal::Group { items, .. } = &mut declaration.tree.terminal else {
            panic!("expected root group");
        };
        items[0].prefix = empty_use_path();

        let results = declaration.expand_header_imports();

        assert!(matches!(
            results[0],
            Err(UseExpansionError::MissingTarget { .. })
        ));
        assert_eq!(
            results[1]
                .as_ref()
                .expect("complete sibling should still expand")
                .path(),
            ["complete"]
        );
    }

    #[test]
    fn keeps_complete_siblings_when_a_group_item_is_a_glob() {
        let (mut declaration, _) = parse_use("use std::{glob, complete}");
        let UseTerminal::Group { items, .. } = &mut declaration.tree.terminal else {
            panic!("expected group terminal");
        };
        items[0].terminal = UseTerminal::Glob {
            join: None,
            without: Vec::new(),
        };

        let results = declaration.expand_header_imports();

        assert!(matches!(
            results[0],
            Err(UseExpansionError::UnsupportedGlob { .. })
        ));
        assert_eq!(
            results[1]
                .as_ref()
                .expect("complete sibling should still expand")
                .path(),
            ["std", "complete"]
        );
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
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = i
            .run(parse_declaration)
            .expect("leading use declaration should parse");

        let Declaration::Use(declaration) = declaration else {
            panic!("expected use declaration");
        };
        (declaration, i.input.remainder())
    }

    fn parse_operator_binding_power(source: &str) -> (BindingPower, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let binding_power = i
            .run(parse_binding_power)
            .expect("operator binding power should parse");
        (binding_power, i.input.remainder())
    }

    fn parse_operator_header_declaration(source: &str) -> (OperatorHeaderDeclaration<'_>, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = i
            .run(parse_declaration)
            .expect("operator header should parse");
        let Declaration::OperatorHeader(header) = declaration else {
            panic!("expected operator header");
        };
        (header, i.input.remainder())
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

    fn glob_parts<'tree, 'source>(
        tree: &'tree UseTree<'source>,
    ) -> (Option<UseSeparator>, &'tree [UseExclusion<'source>]) {
        let UseTerminal::Glob { join, without } = tree.terminal() else {
            panic!("expected use glob terminal: {tree:#?}");
        };
        (*join, without)
    }

    fn exclusion_segment_text<'source>(exclusion: &UseExclusion<'source>) -> Option<&'source str> {
        let UseExclusion::Segment(UseSegment::Word(word)) = exclusion else {
            return None;
        };
        Some(word.text())
    }

    fn parses_declaration(source: &str) -> bool {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        i.run(parse_declaration).is_some()
    }

    fn complete_expansions(declaration: &UseDeclaration<'_>) -> Vec<HeaderImport> {
        declaration
            .expand_header_imports()
            .into_iter()
            .collect::<Result<Vec<_>, _>>()
            .expect("all tested branches should expand")
    }

    #[test]
    fn parses_binding_with_minimal_expression_from_chasa_input() {
        let source = "my value = 123\n";
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = i
            .run(parse_declaration)
            .expect("binding declaration should parse");

        let Declaration::Binding(binding) = declaration else {
            panic!("expected binding declaration");
        };
        assert_eq!(binding.range(), 0..14);
        assert_eq!(binding.name().text(), "value");
        assert_eq!(binding.value().range(), 11..14);
        assert_eq!(i.input.remainder(), "\n");
    }

    #[test]
    fn parses_infix_operator_header_fixture_from_chasa_input() {
        let source = std::str::from_utf8(INFIX_OPERATOR_SOURCE).expect("fixture is UTF-8");
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);

        let declaration = i
            .run(parse_declaration)
            .expect("operator header should parse");

        let Declaration::OperatorHeader(header) = declaration else {
            panic!("expected operator header declaration");
        };
        assert_eq!(header.range(), 0..19);
        assert_eq!(header.name(), "<+>");
        assert_eq!(header.fixity(), OperatorFixity::Infix);
        assert_eq!(
            header.left_binding_power().map(BindingPower::components),
            Some(&[50][..])
        );
        assert_eq!(
            header.right_binding_power().map(BindingPower::components),
            Some(&[51][..])
        );
        assert_eq!(i.input.remainder(), " left\nmy value = 1\n");
    }
}
