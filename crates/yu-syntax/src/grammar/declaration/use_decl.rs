use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) use_keyword: WordSpan<'source>,
    pub(super) after_use: Option<TriviaRun>,
}

/// Emits the common committed-recovery shape for an import-owned mandatory
/// slot.  Use continuations select the narrow `ImportRole` at their call site;
/// the record construction itself stays shared with every such slot.
pub(super) fn emit_import_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ImportRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::Import(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role: grammar_role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role: grammar_role,
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

pub(super) fn emit_import_group_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    delimiter: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::ImportGroup,
            delimiter,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    delimiter,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

pub(super) fn emit_import_group_mismatched_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    actual: Delimiter,
    expected: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::ImportGroup,
            delimiter: expected,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::Punctuation(
                    crate::session::PunctuationEvidence::Close(actual),
                ),
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    expected,
                )),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

pub(super) fn emit_import_operator_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::OperatorName,
            delimiter: Delimiter::Parenthesis,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

/// Completes an accepted `use` introduction while emitting every source token
/// in the owning declaration or recursive tree node that introduces it.
pub(crate) fn commit_use_declaration<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: UseStatementIntro<'source>,
) -> Recovered<UseDeclaration<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UseDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::UseKw, intro.use_keyword.range());
    if let Some(trivia) = &intro.after_use {
        committed.emit_trivia(trivia);
    } else if commit_use_tree_candidate(committed) {
        emit_layout_missing(committed);
    }
    if !commit_use_tree_candidate(committed) && !use_tree_error_retry(committed) {
        emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Path);
        committed.finish_node();
        return Recovered::Incomplete;
    }
    let tree = match commit_use_tree(committed) {
        Recovered::Complete(tree) => tree,
        Recovered::Incomplete => {
            committed.finish_node();
            return Recovered::Incomplete;
        }
    };
    committed.finish_node();

    Recovered::Complete(UseDeclaration {
        range: intro.start..tree.range().end,
        visibility: intro
            .visibility
            .as_ref()
            .map_or(Visibility::Private, |prefix| prefix.visibility),
        tree,
    })
}

pub(super) fn commit_use_tree<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<UseTree<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed_position(committed);
    committed.start_node(SyntaxKind::UseTree);

    let (form, prefix, terminal, terminal_end, glob_aliases) = if let Some(open) =
        commit_maybe_character(committed, '{').flatten()
    {
        let (terminal, end) = match commit_use_group(committed, open) {
            Recovered::Complete(group) => group,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        (
            HeaderImportForm::Plain,
            empty_use_path(),
            terminal,
            end,
            Vec::new(),
        )
    } else if let Some(open) = commit_maybe_character(committed, '(').flatten() {
        let first = match commit_parenthesized_use_operator(committed, open) {
            Recovered::Complete(segment) => segment,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        match commit_use_path_and_terminal(committed, first, None, HeaderImportForm::Plain) {
            Recovered::Complete(result) => result,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        }
    } else {
        let Some(first) = commit_word(committed) else {
            emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Path);
            committed.finish_node();
            return Recovered::Incomplete;
        };
        if first.text() == "mod" {
            committed.token(SyntaxKind::ModKw, first.range());
            if let Some(trivia) = commit_required_inline_trivia(committed) {
                committed.emit_trivia(&trivia);
            } else if commit_word_candidate(committed) {
                emit_layout_missing(committed);
            }
            let Some(first_segment) = commit_word(committed).map(UseSegment::Word) else {
                emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Identifier);
                committed.finish_node();
                return Recovered::Incomplete;
            };
            match commit_use_path_and_terminal(
                committed,
                first_segment,
                None,
                HeaderImportForm::Mod,
            ) {
                Recovered::Complete(result) => result,
                Recovered::Incomplete => {
                    committed.finish_node();
                    return Recovered::Incomplete;
                }
            }
        } else {
            let following_separator = commit_maybe_use_separator(committed).flatten();
            let form = classify_use_form(
                first,
                following_separator
                    .as_ref()
                    .map(|(separator, _)| *separator),
            );
            match form {
                HeaderImportForm::Plain => match commit_use_path_and_terminal(
                    committed,
                    UseSegment::Word(first),
                    following_separator,
                    HeaderImportForm::Plain,
                ) {
                    Recovered::Complete(result) => result,
                    Recovered::Incomplete => {
                        committed.finish_node();
                        return Recovered::Incomplete;
                    }
                },
                HeaderImportForm::Realm | HeaderImportForm::Band => {
                    committed.token(
                        if form == HeaderImportForm::Realm {
                            SyntaxKind::RealmKw
                        } else {
                            SyntaxKind::BandKw
                        },
                        first.range(),
                    );
                    let (_, marker_range) = following_separator
                        .expect("realm and band forms require their marker separator");
                    committed.token(
                        separator_token_kind(form_marker_separator(form)),
                        marker_range,
                    );
                    if let Some(open) = commit_maybe_character(committed, '{').flatten() {
                        let (terminal, end) = match commit_use_group(committed, open) {
                            Recovered::Complete(group) => group,
                            Recovered::Incomplete => {
                                committed.finish_node();
                                return Recovered::Incomplete;
                            }
                        };
                        (form, empty_use_path(), terminal, end, Vec::new())
                    } else if let Some(star) = commit_maybe_character(committed, '*').flatten() {
                        let (terminal, end, aliases) = match commit_use_glob(committed, star) {
                            Recovered::Complete(glob) => glob,
                            Recovered::Incomplete => {
                                committed.finish_node();
                                return Recovered::Incomplete;
                            }
                        };
                        (form, empty_use_path(), terminal, end, aliases)
                    } else {
                        let first_segment = match commit_use_path_segment(committed) {
                            Recovered::Complete(segment) => segment,
                            Recovered::Incomplete => {
                                committed.finish_node();
                                return Recovered::Incomplete;
                            }
                        };
                        match commit_use_path_and_terminal(committed, first_segment, None, form) {
                            Recovered::Complete(result) => result,
                            Recovered::Incomplete => {
                                committed.finish_node();
                                return Recovered::Incomplete;
                            }
                        }
                    }
                }
                HeaderImportForm::Mod => {
                    unreachable!("mod was handled before marker classification")
                }
            }
        }
    };

    let aliases = match terminal {
        UseTerminal::Glob { .. } => glob_aliases,
        _ => match commit_use_aliases(committed) {
            Recovered::Complete(aliases) => aliases,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        },
    };
    let qualifiers = match commit_use_qualifiers(committed) {
        Recovered::Complete(qualifiers) => qualifiers,
        Recovered::Incomplete => {
            committed.finish_node();
            return Recovered::Incomplete;
        }
    };
    let end = qualifiers_end(&qualifiers).unwrap_or_else(|| {
        aliases
            .last()
            .map_or(terminal_end, |alias| alias.range().end)
    });
    committed.finish_node();

    Recovered::Complete(UseTree {
        range: start..end,
        form,
        prefix,
        terminal,
        aliases,
        qualifiers,
    })
}

pub(super) fn form_marker_separator(form: HeaderImportForm) -> UseSeparator {
    match form {
        HeaderImportForm::Realm => UseSeparator::Slash,
        HeaderImportForm::Band => UseSeparator::ColonColon,
        HeaderImportForm::Plain | HeaderImportForm::Mod => {
            unreachable!("only markers have a marker separator")
        }
    }
}

pub(super) fn commit_use_path_and_terminal<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    first: UseSegment<'source>,
    mut pending_separator: Option<(UseSeparator, Range<usize>)>,
    form: HeaderImportForm,
) -> Recovered<(
    HeaderImportForm,
    UsePath<'source>,
    UseTerminal<'source>,
    usize,
    Vec<WordSpan<'source>>,
)>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UsePath);
    emit_use_segment(committed, &first);
    let mut path = UsePath {
        segments: vec![first],
        separators: Vec::new(),
    };

    loop {
        let Some((separator, range)) = pending_separator
            .take()
            .or(commit_maybe_use_separator(committed).flatten())
        else {
            committed.finish_node();
            let end = path
                .segments()
                .last()
                .expect("use path has its first segment")
                .range()
                .end;
            return Recovered::Complete((form, path, UseTerminal::Single, end, Vec::new()));
        };
        if let Some(open) = commit_maybe_character(committed, '{').flatten() {
            committed.finish_node();
            committed.token(separator_token_kind(separator), range);
            let (terminal, end) = match commit_use_group(committed, open) {
                Recovered::Complete(group) => group,
                Recovered::Incomplete => return Recovered::Incomplete,
            };
            return Recovered::Complete((
                form,
                path,
                terminal_with_join(terminal, separator),
                end,
                Vec::new(),
            ));
        }
        if let Some(star) = commit_maybe_character(committed, '*').flatten() {
            committed.finish_node();
            committed.token(separator_token_kind(separator), range);
            let (terminal, end, aliases) = match commit_use_glob(committed, star) {
                Recovered::Complete(glob) => glob,
                Recovered::Incomplete => return Recovered::Incomplete,
            };
            return Recovered::Complete((
                form,
                path,
                terminal_with_join(terminal, separator),
                end,
                aliases,
            ));
        }
        committed.token(separator_token_kind(separator), range);
        path.separators.push(separator);
        let segment = match commit_use_path_segment(committed) {
            Recovered::Complete(segment) => segment,
            Recovered::Incomplete => {
                emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Path);
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        emit_use_segment(committed, &segment);
        path.segments.push(segment);
    }
}

pub(super) fn terminal_with_join<'source>(
    terminal: UseTerminal<'source>,
    join: UseSeparator,
) -> UseTerminal<'source> {
    match terminal {
        UseTerminal::Group { items, .. } => UseTerminal::Group {
            join: Some(join),
            items,
        },
        UseTerminal::Glob { without, .. } => UseTerminal::Glob {
            join: Some(join),
            without,
        },
        UseTerminal::Single => unreachable!("only terminal nodes can receive a join"),
    }
}

pub(super) fn separator_token_kind(separator: UseSeparator) -> SyntaxKind {
    match separator {
        UseSeparator::ColonColon => SyntaxKind::ColonColon,
        UseSeparator::Slash => SyntaxKind::Slash,
    }
}

pub(super) fn commit_use_path_segment<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<UseSegment<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(open) = commit_maybe_character(committed, '(').flatten() {
        return commit_parenthesized_use_operator(committed, open);
    }
    match commit_word(committed) {
        Some(word) => Recovered::Complete(UseSegment::Word(word)),
        None => {
            emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Path);
            Recovered::Incomplete
        }
    }
}

/// Once `(` selects an operator segment, it owns the operator-name node.  A
/// malformed spelling or absent `)` therefore cannot fall back into a group
/// arm and leave the direct CST unbalanced.
pub(super) fn commit_parenthesized_use_operator<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    open: Range<usize>,
) -> Recovered<UseSegment<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let spelling = committed.probe(|probe| {
        let i = probe.input();
        let start = i.pos();
        while let Some(character) = i.input.remainder().chars().next() {
            if !is_use_operator_character(character) {
                break;
            }
            i.input.next()?;
        }
        let end = i.pos();
        (start < end).then_some(start..end)
    });
    let Some(spelling) = spelling else {
        committed.start_node(SyntaxKind::OperatorName);
        committed.token(SyntaxKind::LParen, open);
        emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::OperatorName);
        committed.finish_node();
        return Recovered::Incomplete;
    };
    let Some(close) = commit_maybe_character(committed, ')').flatten() else {
        committed.start_node(SyntaxKind::OperatorName);
        committed.token(SyntaxKind::LParen, open);
        committed.token(SyntaxKind::Operator, spelling);
        emit_import_operator_close_missing(committed);
        committed.finish_node();
        return Recovered::Incomplete;
    };
    Recovered::Complete(UseSegment::Operator {
        range: open.start..close.end,
        text: &committed.probe(|probe| probe.input().input.source())[spelling],
    })
}

pub(super) fn emit_use_segment<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    segment: &UseSegment<'source>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    match segment {
        UseSegment::Word(word) => committed.token(SyntaxKind::Identifier, word.range()),
        UseSegment::Operator { range, .. } => {
            committed.start_node(SyntaxKind::OperatorName);
            committed.token(SyntaxKind::LParen, range.start..range.start + 1);
            committed.token(SyntaxKind::Operator, range.start + 1..range.end - 1);
            committed.token(SyntaxKind::RParen, range.end - 1..range.end);
            committed.finish_node();
        }
    }
}

pub(super) fn commit_use_group<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    open: Range<usize>,
) -> Recovered<(UseTerminal<'source>, usize)>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UseGroup);
    committed.token(SyntaxKind::LBrace, open);
    let mut items = Vec::new();
    loop {
        let trivia = commit_trivia(committed).expect("trivia scanning is total");
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, '}').flatten() {
            committed.token(SyntaxKind::RBrace, close.clone());
            committed.finish_node();
            return Recovered::Complete((UseTerminal::Group { join: None, items }, close.end));
        }
        if let Some(close) = commit_maybe_character(committed, ')').flatten() {
            emit_import_group_mismatched_close(
                committed,
                close,
                Delimiter::Parenthesis,
                Delimiter::Brace,
            );
            continue;
        }
        if committed_at_eof(committed) {
            emit_import_group_close_missing(committed, Delimiter::Brace);
            committed.finish_node();
            return Recovered::Complete((
                UseTerminal::Group { join: None, items },
                committed_position(committed),
            ));
        }
        if let Recovered::Complete(item) = commit_use_tree(committed) {
            items.push(item);
        }
        let trivia = commit_trivia(committed).expect("trivia scanning is total");
        let newline = trivia_has_newline(committed, &trivia);
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, '}').flatten() {
            committed.token(SyntaxKind::RBrace, close.clone());
            committed.finish_node();
            return Recovered::Complete((UseTerminal::Group { join: None, items }, close.end));
        }
        if let Some(close) = commit_maybe_character(committed, ')').flatten() {
            emit_import_group_mismatched_close(
                committed,
                close,
                Delimiter::Parenthesis,
                Delimiter::Brace,
            );
            continue;
        }
        if let Some(comma) = commit_maybe_character(committed, ',').flatten() {
            committed.token(SyntaxKind::Comma, comma);
        } else if committed_at_eof(committed) {
            emit_import_group_close_missing(committed, Delimiter::Brace);
            committed.finish_node();
            return Recovered::Complete((
                UseTerminal::Group { join: None, items },
                committed_position(committed),
            ));
        } else if commit_use_tree_candidate(committed) {
            // Two same-line tree atoms need an explicit comma.  Keep the
            // second atom at this position so the next group iteration can
            // recover it as an ordinary sibling.
            emit_import_missing(
                committed,
                ImportRole::GroupEntry,
                ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Comma),
            );
        } else if !newline {
            emit_import_group_close_missing(committed, Delimiter::Brace);
            committed.finish_node();
            return Recovered::Complete((
                UseTerminal::Group { join: None, items },
                committed_position(committed),
            ));
        }
    }
}

pub(super) fn commit_use_glob<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    star: Range<usize>,
) -> Recovered<(UseTerminal<'source>, usize, Vec<WordSpan<'source>>)>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::UseGlob);
    committed.token(SyntaxKind::Star, star.clone());
    let aliases = match commit_use_aliases(committed) {
        Recovered::Complete(aliases) => aliases,
        Recovered::Incomplete => {
            committed.finish_node();
            return Recovered::Incomplete;
        }
    };
    let mut end = aliases.last().map_or(star.end, |alias| alias.range().end);
    let mut without = Vec::new();
    if let Some(prefix) = commit_maybe_without_prefix(committed) {
        committed.emit_trivia(&prefix.leading);
        committed.token(SyntaxKind::WithoutKw, prefix.keyword.range());
        if let Some(trivia) = &prefix.after_keyword {
            committed.emit_trivia(trivia);
        } else if commit_use_exclusion_candidate(committed) {
            emit_layout_missing(committed);
        }
        match commit_use_exclusion(committed) {
            Recovered::Complete(exclusion) => {
                end = exclusion_range(&exclusion).end;
                without.push(exclusion);
            }
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        }
        while let Some(comma) = commit_maybe_character(committed, ',').flatten() {
            committed.token(SyntaxKind::Comma, comma);
            let trivia = commit_trivia(committed).expect("trivia scanning is total");
            committed.emit_trivia(&trivia);
            match commit_use_exclusion(committed) {
                Recovered::Complete(exclusion) => {
                    end = exclusion_range(&exclusion).end;
                    without.push(exclusion);
                }
                Recovered::Incomplete => break,
            }
        }
    }
    committed.finish_node();
    Recovered::Complete((
        UseTerminal::Glob {
            join: None,
            without,
        },
        end,
        aliases,
    ))
}

pub(super) fn commit_use_aliases<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Vec<WordSpan<'source>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut aliases = Vec::new();
    while let Some(alias) = commit_maybe_use_alias(committed) {
        committed.emit_trivia(&alias.leading);
        committed.start_node(SyntaxKind::UseAlias);
        committed.token(SyntaxKind::AsKw, alias.keyword.range());
        if let Some(trivia) = &alias.after_keyword {
            committed.emit_trivia(trivia);
        } else if commit_word_candidate(committed) {
            emit_layout_missing(committed);
        }
        let Some(name) = alias.name else {
            emit_import_missing(committed, ImportRole::Alias, ExpectedSyntax::Identifier);
            committed.finish_node();
            return Recovered::Incomplete;
        };
        committed.token(SyntaxKind::Identifier, name.range());
        committed.finish_node();
        aliases.push(name);
    }
    Recovered::Complete(aliases)
}

pub(super) fn commit_use_qualifiers<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<UseQualifiers<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let version = commit_maybe_version(committed);
    let anchor_prefix = commit_maybe_with_prefix(committed);
    if version.is_none() && anchor_prefix.is_none() {
        return Recovered::Complete(UseQualifiers::default());
    }
    committed.start_node(SyntaxKind::UseQualifiers);
    if let Some(version) = version {
        committed.emit_trivia(&version.leading);
        committed.start_node(SyntaxKind::UseVersion);
        committed.token(SyntaxKind::Version, version.value.range());
        committed.finish_node();
        let anchor = if let Some(prefix) = anchor_prefix {
            match commit_use_anchor(committed, prefix) {
                Recovered::Complete(anchor) => Some(anchor),
                Recovered::Incomplete => {
                    committed.finish_node();
                    return Recovered::Incomplete;
                }
            }
        } else {
            None
        };
        committed.finish_node();
        return Recovered::Complete(UseQualifiers {
            version: Some(version.value),
            anchor,
        });
    }
    let anchor =
        match commit_use_anchor(committed, anchor_prefix.expect("anchor prefix was checked")) {
            Recovered::Complete(anchor) => anchor,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
    committed.finish_node();
    Recovered::Complete(UseQualifiers {
        version: None,
        anchor: Some(anchor),
    })
}

pub(super) fn commit_use_anchor<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    prefix: WithPrefix<'source>,
) -> Recovered<UsePath<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.emit_trivia(&prefix.leading);
    committed.start_node(SyntaxKind::UseAnchor);
    committed.token(SyntaxKind::WithKw, prefix.keyword.range());
    if let Some(trivia) = &prefix.after_keyword {
        committed.emit_trivia(trivia);
    } else if commit_word_candidate(committed) {
        emit_layout_missing(committed);
    }
    committed.start_node(SyntaxKind::UsePath);
    let Some(first) = commit_word(committed) else {
        emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Identifier);
        committed.finish_node();
        committed.finish_node();
        return Recovered::Incomplete;
    };
    committed.token(SyntaxKind::Identifier, first.range());
    let mut path = UsePath {
        segments: vec![UseSegment::Word(first)],
        separators: Vec::new(),
    };
    while let Some((separator, range)) = commit_maybe_use_separator(committed).flatten() {
        let Some(segment) = commit_word(committed) else {
            emit_import_missing(committed, ImportRole::Path, ExpectedSyntax::Identifier);
            committed.finish_node();
            committed.finish_node();
            return Recovered::Incomplete;
        };
        committed.token(separator_token_kind(separator), range);
        committed.token(SyntaxKind::Identifier, segment.range());
        path.separators.push(separator);
        path.segments.push(UseSegment::Word(segment));
    }
    committed.finish_node();
    committed.finish_node();
    Recovered::Complete(path)
}

pub(super) fn commit_use_exclusion<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<UseExclusion<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = committed_position(committed);
    committed.start_node(SyntaxKind::UseExclusion);
    if let Some(open) = commit_maybe_character(committed, '(').flatten() {
        if commit_parenthesized_use_operator_candidate(committed) {
            let group = match commit_parenthesized_use_operator(committed, open) {
                Recovered::Complete(segment) => UseExclusion::Segment(segment),
                Recovered::Incomplete => {
                    committed.finish_node();
                    return Recovered::Incomplete;
                }
            };
            let UseExclusion::Segment(segment) = &group else {
                unreachable!("operator parsing always returns a segment");
            };
            emit_use_segment(committed, segment);
            committed.finish_node();
            return Recovered::Complete(group);
        }
        let group = match commit_use_exclusion_group(committed, open, '(', ')') {
            Recovered::Complete(group) => group,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        committed.finish_node();
        return Recovered::Complete(group);
    }
    if let Some(open) = commit_maybe_character(committed, '{').flatten() {
        let group = match commit_use_exclusion_group(committed, open, '{', '}') {
            Recovered::Complete(group) => group,
            Recovered::Incomplete => {
                committed.finish_node();
                return Recovered::Incomplete;
            }
        };
        committed.finish_node();
        return Recovered::Complete(group);
    }
    if let Some(star) = commit_maybe_character(committed, '*').flatten() {
        committed.token(SyntaxKind::Star, star.clone());
        committed.finish_node();
        return Recovered::Complete(UseExclusion::Glob { range: star });
    }
    let Some(word) = commit_word(committed) else {
        emit_import_missing(
            committed,
            ImportRole::GroupEntry,
            ExpectedSyntax::Identifier,
        );
        committed.finish_node();
        return Recovered::Incomplete;
    };
    committed.token(SyntaxKind::Identifier, word.range());
    committed.finish_node();
    debug_assert_eq!(word.range().start, start);
    Recovered::Complete(UseExclusion::Segment(UseSegment::Word(word)))
}

pub(super) fn commit_use_exclusion_group<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    open: Range<usize>,
    opening: char,
    closing: char,
) -> Recovered<UseExclusion<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = open.start;
    committed.start_node(SyntaxKind::UseExclusionGroup);
    committed.token(
        if opening == '(' {
            SyntaxKind::LParen
        } else {
            SyntaxKind::LBrace
        },
        open,
    );
    let mut items = Vec::new();
    loop {
        let trivia = commit_trivia(committed).expect("trivia scanning is total");
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, closing).flatten() {
            committed.token(
                if closing == ')' {
                    SyntaxKind::RParen
                } else {
                    SyntaxKind::RBrace
                },
                close.clone(),
            );
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }
        let mismatched = if closing == ')' { '}' } else { ')' };
        if let Some(close) = commit_maybe_character(committed, mismatched).flatten() {
            emit_import_group_mismatched_close(
                committed,
                close,
                if mismatched == ')' {
                    Delimiter::Parenthesis
                } else {
                    Delimiter::Brace
                },
                if closing == ')' {
                    Delimiter::Parenthesis
                } else {
                    Delimiter::Brace
                },
            );
            continue;
        }
        if committed_at_eof(committed) {
            let delimiter = if closing == ')' {
                Delimiter::Parenthesis
            } else {
                Delimiter::Brace
            };
            emit_import_group_close_missing(committed, delimiter);
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..committed_position(committed),
                items,
            });
        }
        match commit_use_tree(committed) {
            Recovered::Complete(item) => items.push(item),
            Recovered::Incomplete => {}
        }
        let trivia = commit_trivia(committed).expect("trivia scanning is total");
        let newline = trivia_has_newline(committed, &trivia);
        committed.emit_trivia(&trivia);
        if let Some(close) = commit_maybe_character(committed, closing).flatten() {
            committed.token(
                if closing == ')' {
                    SyntaxKind::RParen
                } else {
                    SyntaxKind::RBrace
                },
                close.clone(),
            );
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..close.end,
                items,
            });
        }
        let mismatched = if closing == ')' { '}' } else { ')' };
        if let Some(close) = commit_maybe_character(committed, mismatched).flatten() {
            emit_import_group_mismatched_close(
                committed,
                close,
                if mismatched == ')' {
                    Delimiter::Parenthesis
                } else {
                    Delimiter::Brace
                },
                if closing == ')' {
                    Delimiter::Parenthesis
                } else {
                    Delimiter::Brace
                },
            );
            continue;
        }
        if committed_at_eof(committed) {
            let delimiter = if closing == ')' {
                Delimiter::Parenthesis
            } else {
                Delimiter::Brace
            };
            emit_import_group_close_missing(committed, delimiter);
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..committed_position(committed),
                items,
            });
        }
        if let Some(comma) = commit_maybe_character(committed, ',').flatten() {
            committed.token(SyntaxKind::Comma, comma);
        } else if !newline {
            let delimiter = if closing == ')' {
                Delimiter::Parenthesis
            } else {
                Delimiter::Brace
            };
            emit_import_group_close_missing(committed, delimiter);
            committed.finish_node();
            return Recovered::Complete(UseExclusion::Group {
                range: start..committed_position(committed),
                items,
            });
        }
    }
}

#[derive(Clone)]
pub(super) struct AliasPrefix<'source> {
    pub(super) leading: TriviaRun,
    pub(super) keyword: WordSpan<'source>,
    pub(super) after_keyword: Option<TriviaRun>,
    pub(super) name: Option<WordSpan<'source>>,
}

#[derive(Clone)]
pub(super) struct VersionPrefix<'source> {
    pub(super) leading: TriviaRun,
    pub(super) value: UseVersion<'source>,
}

#[derive(Clone)]
pub(super) struct WithPrefix<'source> {
    pub(super) leading: TriviaRun,
    pub(super) keyword: WordSpan<'source>,
    pub(super) after_keyword: Option<TriviaRun>,
}

#[derive(Clone)]
pub(super) struct WithoutPrefix<'source> {
    pub(super) leading: TriviaRun,
    pub(super) keyword: WordSpan<'source>,
    pub(super) after_keyword: Option<TriviaRun>,
}

pub(super) fn commit_maybe_use_alias<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<AliasPrefix<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let Some(leading) = scan_required_inline_trivia(i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        if keyword.text() != "as" {
            i.rollback(checkpoint);
            return None;
        }
        let after_keyword = scan_maybe_required_inline_trivia(i);
        let name = after_keyword.as_ref().and_then(|_| i.run(scan_word));
        Some(AliasPrefix {
            leading,
            keyword,
            after_keyword,
            name,
        })
    })
}

pub(super) fn commit_maybe_version<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<VersionPrefix<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = (|| {
            let leading = scan_required_inline_trivia(i)?;
            let value = i.run(scan_use_version)?;
            Some(VersionPrefix { leading, value })
        })();
        if result.is_none() {
            i.rollback(checkpoint);
        }
        result
    })
}

pub(super) fn commit_maybe_with_prefix<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<WithPrefix<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let Some(leading) = scan_required_inline_trivia(i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        if keyword.text() != "with" {
            i.rollback(checkpoint);
            return None;
        }
        let after_keyword = scan_maybe_required_inline_trivia(i);
        Some(WithPrefix {
            leading,
            keyword,
            after_keyword,
        })
    })
}

pub(super) fn commit_maybe_without_prefix<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<WithoutPrefix<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let Some(leading) = scan_required_inline_trivia(i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        if keyword.text() != "without" {
            i.rollback(checkpoint);
            return None;
        }
        let after_keyword = scan_maybe_required_inline_trivia(i);
        Some(WithoutPrefix {
            leading,
            keyword,
            after_keyword,
        })
    })
}

pub(super) fn qualifiers_end(qualifiers: &UseQualifiers<'_>) -> Option<usize> {
    qualifiers
        .anchor()
        .and_then(use_path_end)
        .or_else(|| qualifiers.version().map(|version| version.range().end))
}

/// A sink-free test for the first `UseTree` atom.  It intentionally does not
/// scan the whole tree: this is only the local-candidate decision used by the
/// declaration-head recovery rule.
pub(super) fn commit_use_tree_candidate<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let candidate = i.input.remainder().starts_with('{')
            || i.input.remainder().starts_with('(')
            || i.run(scan_word).is_some()
            || i.run(parse_parenthesized_use_operator).is_some();
        i.rollback(checkpoint);
        candidate
    })
}

pub(super) fn commit_parenthesized_use_operator_candidate<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| {
        probe
            .input()
            .input
            .remainder()
            .chars()
            .next()
            .is_some_and(is_use_operator_character)
    })
}

pub(super) fn commit_use_exclusion_candidate<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        matches!(i.input.remainder().chars().next(), Some('(' | '{' | '*'))
            || i.run(scan_word).is_some()
    })
}

/// Consumes one contiguous invalid use-tree head episode, then leaves a later
/// locally-recognizable tree atom for the same slot to retry.  Statement and
/// group boundaries remain untouched for their owners.
pub(super) fn use_tree_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, '\r' | '\n' | ';' | ',' | '}' | ')') {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            let candidate = i.input.remainder().starts_with('{')
                || i.input
                    .remainder()
                    .chars()
                    .next()
                    .is_some_and(|next| next == '_' || next.is_alphabetic());
            if candidate {
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Import(ImportRole::Path));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Path,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
    retry
}

pub(super) fn commit_maybe_use_separator<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Option<(UseSeparator, Range<usize>)>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = i
            .run(scan_punctuation)
            .and_then(|punctuation| match punctuation.kind() {
                PunctuationKind::ColonColon => {
                    Some((UseSeparator::ColonColon, punctuation.range()))
                }
                PunctuationKind::Slash => Some((UseSeparator::Slash, punctuation.range())),
                _ => None,
            });
        if result.is_none() {
            i.rollback(checkpoint);
        }
        Some(result)
    })
}

pub(super) fn commit_maybe_operator_segment<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<Option<UseSegment<'source>>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = i.run(parse_parenthesized_use_operator);
        if result.is_none() {
            i.rollback(checkpoint);
        }
        Some(result)
    })
}

/// A parsed `use` declaration before syntax planning resolves it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseDeclaration<'source> {
    pub(super) range: Range<usize>,
    pub(super) visibility: Visibility,
    pub(super) tree: UseTree<'source>,
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
    pub(super) range: Range<usize>,
    pub(super) form: HeaderImportForm,
    pub(super) prefix: UsePath<'source>,
    pub(super) terminal: UseTerminal<'source>,
    pub(super) aliases: Vec<WordSpan<'source>>,
    pub(super) qualifiers: UseQualifiers<'source>,
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
    pub(super) segments: Vec<UseSegment<'source>>,
    pub(super) separators: Vec<UseSeparator>,
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

pub(super) fn project_use_route(path: &UsePath<'_>) -> HeaderImportRoute {
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

pub(super) fn expand_use_tree(
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

pub(super) fn concatenate_use_route(
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

pub(super) fn project_use_separator(separator: UseSeparator) -> HeaderImportRouteSeparator {
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
    pub(super) version: Option<UseVersion<'source>>,
    pub(super) anchor: Option<UsePath<'source>>,
}

impl<'source> UseQualifiers<'source> {
    pub(crate) fn version(&self) -> Option<&UseVersion<'source>> {
        self.version.as_ref()
    }

    pub(crate) fn anchor(&self) -> Option<&UsePath<'source>> {
        self.anchor.as_ref()
    }

    pub(super) fn is_empty(&self) -> bool {
        self.version.is_none() && self.anchor.is_none()
    }
}

/// A raw version suffix on a use specification.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct UseVersion<'source> {
    pub(super) range: Range<usize>,
    pub(super) text: &'source str,
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

pub(crate) fn parse_use_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<UseDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let first = i.run(scan_word)?;
    let visibility = if let Some(visibility) = visibility_prefix(first) {
        inline_trivia(&mut i)?;
        let keyword = i.run(scan_word)?;
        (keyword.text() == "use").then_some(visibility.visibility)?
    } else {
        (first.text() == "use").then_some(Visibility::Private)?
    };
    inline_trivia(&mut i)?;

    let tree = parse_use_tree(&mut i)?;
    let end = tree.range().end;

    Some(UseDeclaration {
        range: start..end,
        visibility,
        tree,
    })
}

pub(super) fn parse_use_tree<'source, E>(
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

pub(super) fn finish_use_tree<'source, E>(
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

pub(super) fn classify_use_form(
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

pub(super) fn parse_use_path_and_terminal<'source, E>(
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

pub(super) fn parse_use_group_terminal<'source, E>(
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

pub(super) fn parse_use_aliases<'source, E>(
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

pub(super) fn parse_use_alias<'source, E>(
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

pub(super) fn parse_use_qualifiers<'source, E>(
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

pub(super) fn parse_use_version_suffix<'source, E>(
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

pub(super) fn scan_use_version<'source, E>(
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

pub(super) fn parse_use_anchor<'source, E>(
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

pub(super) fn parse_with_keyword<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    inline_trivia(&mut i)?;
    let keyword = i.run(scan_word)?;
    (keyword.text() == "with").then_some(())
}

pub(super) fn use_path_end(path: &UsePath<'_>) -> Option<usize> {
    path.segments().last().map(|segment| segment.range().end)
}

pub(super) fn parse_use_without<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Option<(Vec<UseExclusion<'source>>, usize)>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.maybe(from_fn(parse_use_without_clause))
}

pub(super) fn parse_use_without_clause<'source, E>(
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

pub(super) fn parse_use_exclusion<'source, E>(
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

pub(super) fn parse_parenthesized_use_operator<'source, E>(
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
pub(super) fn parse_use_path_segment<'source, E>(
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

pub(super) fn is_use_operator_character(character: char) -> bool {
    !character.is_whitespace()
        && character != '_'
        && !unicode_ident::is_xid_continue(character)
        && !matches!(
            character,
            '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | '/' | ';'
        )
}

pub(super) fn parse_use_exclusion_group<'source, E>(
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

pub(super) fn parse_use_glob<E>(mut i: SynIn<E>) -> Option<Range<usize>>
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

pub(super) fn exclusion_range(exclusion: &UseExclusion<'_>) -> Range<usize> {
    match exclusion {
        UseExclusion::Segment(segment) => segment.range(),
        UseExclusion::Glob { range } | UseExclusion::Group { range, .. } => range.clone(),
    }
}

pub(super) fn empty_use_path<'source>() -> UsePath<'source> {
    UsePath {
        segments: Vec::new(),
        separators: Vec::new(),
    }
}

pub(super) fn consume_group_trivia<E>(i: &mut SynIn<E>) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia)?;
    Some(i.input.source()[trivia.range()].contains(['\r', '\n']))
}

pub(super) fn parse_open_brace<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Open(Delimiter::Brace)).then_some(())
}

pub(super) fn scan_open_parenthesis<E>(mut i: SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Open(Delimiter::Parenthesis))
        .then(|| punctuation.range())
}

pub(super) fn scan_close_parenthesis<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Close(Delimiter::Parenthesis)).then_some(())
}

pub(super) fn parse_close_delimiter<E>(
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

pub(super) fn parse_close_brace<E>(mut i: SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Close(Delimiter::Brace)).then(|| punctuation.range())
}

pub(super) fn parse_comma<E>(mut i: SynIn<E>) -> Option<()>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
{
    let punctuation = i.run(scan_punctuation)?;
    (punctuation.kind() == PunctuationKind::Comma).then_some(())
}

pub(super) fn parse_use_separator<E>(mut i: SynIn<E>) -> Option<UseSeparator>
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
