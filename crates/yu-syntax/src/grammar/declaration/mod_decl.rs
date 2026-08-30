use super::*;

/// The sink-free prefix shared by root and canonical-statement Mod parsing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ModStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) mod_keyword: WordSpan<'source>,
}

pub(super) fn recognize_mod_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ModStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(base, &mut i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(keyword) = i.run(scan_word) else {
            i.rollback(checkpoint);
            return None;
        };
        (Some(visibility), Some(trivia), keyword)
    } else {
        (None, None, first)
    };
    if keyword.text() != "mod" {
        i.rollback(checkpoint);
        return None;
    }
    Some(ModStatementIntro {
        start,
        visibility,
        after_visibility,
        mod_keyword: keyword,
    })
}

/// Commits the total Mod continuation selected by the shared statement intro.
/// Identity and body slots stay local to this node so root and nested callers
/// cannot accidentally assign their boundary recovery to different owners.
pub(crate) fn commit_mod_declaration<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ModStatementIntro<'source>,
) -> Recovered<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::ModDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
        let base = committed.probe(|probe| {
            probe
                .input()
                .local
                .indentation_baseline()
                .map_or(0, |baseline| baseline.column)
        });
        let _ = base;
    }
    committed.token(SyntaxKind::ModKw, intro.mod_keyword.range());
    let mod_base = committed.probe(|probe| {
        probe
            .input()
            .local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column)
    });
    if let Some(trivia) = committed.probe(|probe| mod_trivia(mod_base, probe.input())) {
        committed.emit_trivia(&trivia);
    }

    let mut identity_missing = false;
    let mut identity_error = false;
    let first =
        commit_word(committed).or_else(|| match mod_word_error_retry(committed, ModRole::Name) {
            Some(true) => commit_word(committed),
            Some(false) => {
                identity_error = true;
                None
            }
            None => None,
        });
    let is_test = first.as_ref().is_some_and(|word| word.text() == "test");
    if is_test {
        let marker = first.expect("checked above");
        committed.start_node(SyntaxKind::TestModuleMarker);
        committed.token(SyntaxKind::Identifier, marker.range());
        committed.finish_node();
        let anonymous = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let result = mod_trivia(mod_base, i).is_some() && mod_body_starter_pending(i);
            i.rollback(checkpoint);
            result
        });
        if !anonymous {
            if let Some(trivia) = committed.probe(|probe| mod_trivia(mod_base, probe.input())) {
                committed.emit_trivia(&trivia);
            }
            let name = commit_word(committed).or_else(|| {
                match mod_word_error_retry(committed, ModRole::TestName) {
                    Some(true) => commit_word(committed),
                    Some(false) => {
                        identity_error = true;
                        None
                    }
                    None => None,
                }
            });
            if let Some(name) = name {
                committed.token(SyntaxKind::Identifier, name.range());
            } else if !identity_error {
                emit_mod_missing(committed, ModRole::TestName, ExpectedSyntax::Identifier);
                identity_missing = true;
            } else {
                identity_missing = true;
            }
        }
    } else if let Some(name) = first {
        committed.token(SyntaxKind::Identifier, name.range());
    } else if !identity_error {
        emit_mod_missing(committed, ModRole::Name, ExpectedSyntax::Identifier);
        identity_missing = true;
    } else {
        identity_missing = true;
    }

    if let Some(trivia) = committed.probe(|probe| mod_trivia(mod_base, probe.input())) {
        committed.emit_trivia(&trivia);
    }
    let mut body_starter = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let starter = i
            .run(scan_punctuation)
            .and_then(|punctuation| match punctuation.kind() {
                PunctuationKind::Semicolon => Some(PunctuationKind::Semicolon),
                PunctuationKind::Open(Delimiter::Brace) => {
                    Some(PunctuationKind::Open(Delimiter::Brace))
                }
                PunctuationKind::Colon => Some(PunctuationKind::Colon),
                _ => None,
            });
        i.rollback(checkpoint);
        starter
    });
    let mut body_introducer_error = false;
    if body_starter.is_none() && !identity_missing {
        let statement_pending = committed.probe(|probe| {
            crate::grammar::expression::direct_canonical_statement_candidate(
                operators,
                LeadingTrivia::None,
                probe,
            )
        });
        if !statement_pending && mod_body_introducer_error_retry(operators, committed).is_some() {
            body_introducer_error = true;
            body_starter = committed.probe(|probe| {
                let i = probe.input();
                let checkpoint = i.checkpoint();
                let starter =
                    i.run(scan_punctuation)
                        .and_then(|punctuation| match punctuation.kind() {
                            PunctuationKind::Semicolon => Some(PunctuationKind::Semicolon),
                            PunctuationKind::Open(Delimiter::Brace) => {
                                Some(PunctuationKind::Open(Delimiter::Brace))
                            }
                            PunctuationKind::Colon => Some(PunctuationKind::Colon),
                            _ => None,
                        });
                i.rollback(checkpoint);
                starter
            });
        }
    }
    match body_starter {
        Some(PunctuationKind::Semicolon) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("accepted starter remains");
            committed.token(SyntaxKind::Semicolon, punctuation.range());
        }
        Some(PunctuationKind::Open(Delimiter::Brace)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("accepted starter remains");
            commit_braced_statement_block_expression(operators, punctuation.range(), committed);
        }
        Some(PunctuationKind::Colon) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("accepted starter remains");
            committed.token(SyntaxKind::Colon, punctuation.range());
            commit_mod_colon_body(operators, mod_base, committed);
        }
        Some(_) | None => {
            if identity_missing {
                committed.finish_node();
                return Recovered::Complete(());
            }
            let candidate = committed.probe(|probe| {
                crate::grammar::expression::direct_canonical_statement_candidate(
                    operators,
                    LeadingTrivia::None,
                    probe,
                )
            });
            if candidate {
                if !body_introducer_error {
                    emit_mod_missing(
                        committed,
                        ModRole::BodyIntroducer,
                        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
                    );
                }
                let _ = commit_mod_inline_statement(operators, committed);
            } else if !body_introducer_error {
                emit_mod_body_introducer_missing(committed);
            }
        }
    }
    committed.finish_node();
    Recovered::Complete(())
}

/// Commits the selected Struct declaration through the derives-aware
/// promotion core. The selected keyword is never returned to later choices.
pub(super) fn commit_mod_colon_body<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    mod_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia is total");
    let newline = committed
        .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
    if newline && committed.probe(|probe| probe.input().local.line().line_indent <= mod_base) {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_mod_missing(committed, ModRole::Body, ExpectedSyntax::Statement);
        return;
    }
    if newline {
        let indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_mod_body(operators, trivia, mod_base, indent, committed);
        return;
    }
    committed.emit_trivia(&trivia);
    commit_mod_inline_colon_body(operators, committed);
}

pub(super) fn commit_mod_inline_colon_body<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::ModColonBody,
            )
    });
    let mut statement_committed =
        commit_canonical_statement(operators, LeadingTrivia::None, committed);
    if !statement_committed {
        match mod_body_error_retry(operators, committed) {
            Some(true) => {
                commit_canonical_statement(operators, LeadingTrivia::None, committed)
                    .then_some(())
                    .expect("a retried Mod colon body must commit");
                statement_committed = true;
            }
            Some(false) => {}
            None => {
                emit_mod_missing(committed, ModRole::Body, ExpectedSyntax::Statement);
            }
        }
    }
    if statement_committed && let Some(semicolon) = commit_character(committed, ';') {
        committed.token(SyntaxKind::Semicolon, semicolon);
    }
    committed.probe(|probe| {
        assert_eq!(
            probe.input().local.pop_ambient_owner_scope(),
            Some(ambient_scope),
        );
    });
}

pub(super) fn commit_mod_inline_statement<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::ModColonBody,
            )
    });
    let committed_statement = commit_canonical_statement(operators, LeadingTrivia::None, committed);
    committed.probe(|probe| {
        assert_eq!(
            probe.input().local.pop_ambient_owner_scope(),
            Some(ambient_scope),
        );
    });
    committed_statement
}

pub(super) fn emit_mod_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ModRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::Mod(role));
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

pub(super) fn emit_mod_body_introducer_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Mod(ModRole::BodyIntroducer));
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: at..at,
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range: at..at,
                    sources: source,
                },
            ]),
            0,
        )
    });
    committed.emit_missing(record);
}

/// Recover one malformed raw-name episode without stealing a Mod body starter
/// or a caller-owned statement boundary.  The caller decides whether a later
/// raw word is a first name or a test-module second name.
pub(super) fn mod_word_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ModRole,
) -> Option<bool>
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
            if matches!(character, '\r' | '\n' | ';' | ',' | ')' | ']' | '}')
                || matches!(character, '{' | ':')
            {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            let checkpoint = i.checkpoint();
            let candidate = i.run(scan_word).is_some();
            i.rollback(checkpoint);
            if candidate {
                return Some((start..end, true));
            }
        }
    })?;
    let (range, retry) = recovered;
    let record = committed.probe(|probe| {
        let i = probe.input();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::Mod(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role: grammar_role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role: grammar_role,
                expected: ExpectedSyntax::Identifier,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
    Some(retry)
}

/// Keep a malformed Mod body-introducer episode local.  A subsequent body
/// starter or canonical statement remains at the same position for the Mod
/// continuation; caller-owned boundaries are deliberately left untouched.
pub(super) fn mod_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
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
            let character = probe.input().input.remainder().chars().next()?;
            if matches!(
                character,
                '\r' | '\n' | ';' | ',' | ')' | ']' | '}' | '{' | ':'
            ) {
                return (start < end).then_some((start..end, false));
            }
            {
                let i = probe.input();
                i.input.next()?;
                end = i.pos();
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_canonical_statement_candidate(
                operators,
                LeadingTrivia::None,
                probe,
            ) {
                return Some((start..end, true));
            }
        }
    })?;
    let (range, retry) = recovered;
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Mod(ModRole::BodyIntroducer));
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
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
            Arc::from([
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Semicolon,
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range,
                    sources: source,
                },
            ]),
            0,
        )
    });
    committed.emit_error(record);
    Some(retry)
}

/// Recover one malformed inline colon-body episode without consuming the
/// caller's statement boundary.  A subsequent canonical statement retries
/// the same body slot.
pub(super) fn mod_body_error_retry<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
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
            let character = probe.input().input.remainder().chars().next()?;
            if matches!(
                character,
                '\r' | '\n' | ';' | ',' | ')' | ']' | '}' | '{' | ':'
            ) {
                return (start < end).then_some((start..end, false));
            }
            {
                let i = probe.input();
                i.input.next()?;
                end = i.pos();
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_canonical_statement_candidate(
                operators,
                LeadingTrivia::None,
                probe,
            ) {
                return Some((start..end, true));
            }
        }
    })?;
    let (range, retry) = recovered;
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Mod(ModRole::Body));
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
                expected: ExpectedSyntax::Statement,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
    Some(retry)
}

/// statement sequence; only its caller supplies a different wrapper.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ModDeclaration<'source> {
    pub(super) visibility: Visibility,
    pub(super) test_marker: Option<WordSpan<'source>>,
    pub(super) name: Option<Recovered<WordSpan<'source>>>,
    pub(super) body: Recovered<ModBody<'source>>,
    pub(super) range: Range<usize>,
}

impl<'source> ModDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModBody<'source> {
    Bodyless {
        semicolon: Range<usize>,
    },
    Braced {
        block: BracedStatementBlockExpression<'source>,
    },
    Colon {
        colon: Recovered<Range<usize>>,
        body: Recovered<ModColonBody<'source>>,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ModColonBody<'source> {
    Inline {
        statement: Box<Statement<'source>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

pub(crate) fn parse_mod_declaration_with_operators<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ModDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let first = i.run(scan_word)?;
    let mod_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, mod_keyword) = if let Some(prefix) = visibility_prefix(first) {
        mod_trivia(mod_base, &mut i)?;
        let keyword = i.run(scan_word)?;
        (prefix.visibility, keyword)
    } else {
        (Visibility::Private, first)
    };
    (mod_keyword.text() == "mod").then_some(())?;
    mod_trivia(mod_base, &mut i)?;

    let first_name = i.run(scan_word);
    let (test_marker, name) = match first_name {
        Some(word) if word.text() == "test" => {
            let marker = word;
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(mod_base, &mut i);
            let anonymous = trivia.is_some() && mod_body_starter_pending(&mut i);
            i.rollback(checkpoint);
            if anonymous {
                (Some(marker), None)
            } else {
                let _ = mod_trivia(mod_base, &mut i);
                let name = i
                    .run(scan_word)
                    .map_or(Recovered::Incomplete, Recovered::Complete);
                (Some(marker), Some(name))
            }
        }
        Some(word) => (None, Some(Recovered::Complete(word))),
        None => (None, Some(Recovered::Incomplete)),
    };

    let identity_missing = matches!(name, Some(Recovered::Incomplete));
    let body = parse_mod_body_ast(table, mod_base, !identity_missing, &mut i)
        .map_or(Recovered::Incomplete, Recovered::Complete);
    let end = match &body {
        Recovered::Complete(ModBody::Bodyless { semicolon }) => semicolon.end,
        Recovered::Complete(ModBody::Braced { block }) => block.range().end,
        Recovered::Complete(ModBody::Colon { .. }) => i.pos(),
        Recovered::Incomplete => i.pos(),
    };
    Some(ModDeclaration {
        visibility,
        test_marker,
        name,
        body,
        range: start..end,
    })
}

pub(super) fn parse_mod_inline_statement_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<Statement<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
        crate::session::InlineStatementOwnerKind::ModColonBody,
    );
    let statement = i.run(from_fn(|i| parse_canonical_statement(table, i)));
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    statement
}

pub(super) fn parse_mod_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    mod_base: usize,
    allow_missing_colon_retry: bool,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ModBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let checkpoint = i.checkpoint();
    let _trivia = mod_trivia(mod_base, i)?;
    let punctuation = i.run(scan_punctuation);
    let Some(punctuation) = punctuation else {
        if !allow_missing_colon_retry {
            i.rollback(checkpoint);
            return None;
        }
        if let Some(statement) = parse_mod_inline_statement_ast(table, i) {
            return Some(ModBody::Colon {
                colon: Recovered::Incomplete,
                body: Recovered::Complete(ModColonBody::Inline {
                    statement: Box::new(statement),
                }),
            });
        }
        if mod_statement_error_retry_ast(table, i).is_some_and(|retry| retry) {
            let statement = parse_mod_inline_statement_ast(table, i)?;
            return Some(ModBody::Colon {
                colon: Recovered::Incomplete,
                body: Recovered::Complete(ModColonBody::Inline {
                    statement: Box::new(statement),
                }),
            });
        }
        if i.pos() == start {
            i.rollback(checkpoint);
        }
        return None;
    };
    match punctuation.kind() {
        PunctuationKind::Semicolon => Some(ModBody::Bodyless {
            semicolon: punctuation.range(),
        }),
        PunctuationKind::Open(Delimiter::Brace) => Some(ModBody::Braced {
            block: parse_braced_statement_block_expression(table, punctuation.range(), i),
        }),
        PunctuationKind::Colon => Some(ModBody::Colon {
            colon: Recovered::Complete(punctuation.range()),
            body: parse_mod_colon_body_ast(table, mod_base, i)
                .map_or(Recovered::Incomplete, Recovered::Complete),
        }),
        _ => {
            i.rollback(checkpoint);
            if !allow_missing_colon_retry {
                return None;
            }
            if let Some(statement) = parse_mod_inline_statement_ast(table, i) {
                return Some(ModBody::Colon {
                    colon: Recovered::Incomplete,
                    body: Recovered::Complete(ModColonBody::Inline {
                        statement: Box::new(statement),
                    }),
                });
            }
            if mod_statement_error_retry_ast(table, i).is_some_and(|retry| retry) {
                let statement = parse_mod_inline_statement_ast(table, i)?;
                return Some(ModBody::Colon {
                    colon: Recovered::Incomplete,
                    body: Recovered::Complete(ModColonBody::Inline {
                        statement: Box::new(statement),
                    }),
                });
            }
            None
        }
    }
}

pub(super) fn parse_mod_colon_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    mod_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ModColonBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    let has_newline = i.input.source()[trivia.range()].contains(['\r', '\n']);
    if has_newline {
        if i.local.line().line_indent <= mod_base {
            i.rollback(checkpoint);
            return None;
        }
        let block_indent = i.local.line().line_indent;
        return Some(ModColonBody::Indented {
            block: parse_indented_mod_body(table, trivia, mod_base, block_indent, i),
        });
    }
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
        crate::session::InlineStatementOwnerKind::ModColonBody,
    );
    let statement = if let Some(statement) = i.run(from_fn(|i| parse_canonical_statement(table, i)))
    {
        Some(statement)
    } else if mod_statement_error_retry_ast(table, i).is_some_and(|retry| retry) {
        i.run(from_fn(|i| parse_canonical_statement(table, i)))
    } else {
        None
    };
    let body = statement.map(|statement| {
        let terminal = i.checkpoint();
        if i.run(scan_punctuation)
            .is_none_or(|punctuation| punctuation.kind() != PunctuationKind::Semicolon)
        {
            i.rollback(terminal);
        }
        ModColonBody::Inline {
            statement: Box::new(statement),
        }
    });
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    body
}

/// AST parsing keeps recovery diagnostics in the direct-CST channel, but it
/// must consume and retry the same malformed episode so both paths agree on
/// the following statement boundary and the recovered Mod body shape.
pub(super) fn mod_statement_error_retry_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        let character = i.input.remainder().chars().next()?;
        if matches!(
            character,
            '\r' | '\n' | ';' | ',' | ')' | ']' | '}' | '{' | ':'
        ) {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let checkpoint = i.checkpoint();
        let candidate = i
            .run(from_fn(|i| parse_canonical_statement(table, i)))
            .is_some();
        i.rollback(checkpoint);
        if candidate {
            return Some(true);
        }
    }
}

pub(super) fn mod_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon
        )
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn mod_trivia<E>(mod_base: usize, i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n'])
        && i.local.line().line_indent <= mod_base
    {
        i.rollback(checkpoint);
        return None;
    }
    Some(trivia)
}
