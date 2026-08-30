use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) lazy_keyword: Option<WordSpan<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) after_lazy: Option<TriviaRun>,
    /// A fixity recognized before commitment.  `lazy` deliberately leaves
    /// this slot to the continuation so a missing discriminator can recover.
    pub(super) fixity_keyword: Option<WordSpan<'source>>,
    pub(super) after_fixity: Option<TriviaRun>,
}

/// Completes an accepted operator-header introduction while building its AST
/// and direct CST from the same scans.
pub(crate) fn commit_operator_header<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: OperatorStatementIntro<'source>,
) -> Recovered<OperatorHeaderDeclaration<'source>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::OperatorHeader);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    if let Some(lazy_keyword) = intro.lazy_keyword {
        committed.token(SyntaxKind::LazyKw, lazy_keyword.range());
        if let Some(trivia) = &intro.after_lazy {
            committed.emit_trivia(trivia);
        } else if commit_operator_fixity_candidate(committed) {
            emit_layout_missing(committed);
        }
    }
    let fixity = match intro.fixity_keyword {
        Some(keyword) => {
            let fixity = parse_operator_fixity(keyword)
                .expect("operator intro stores only a recognized fixity");
            committed.token(fixity_token_kind(fixity), keyword.range());
            Recovered::Complete(fixity)
        }
        None => commit_operator_fixity(committed),
    };
    let fixity = match fixity {
        Recovered::Complete(fixity) => fixity,
        Recovered::Incomplete => {
            committed.finish_node();
            return Recovered::Incomplete;
        }
    };

    if let Some(trivia) = &intro.after_fixity {
        committed.emit_trivia(trivia);
    } else {
        emit_optional_inline_trivia(committed);
    }
    let name = match commit_operator_name(committed) {
        Recovered::Complete(name) => Some(name),
        Recovered::Incomplete => None,
    };
    let (left_binding_power, right_binding_power, binding_powers_complete) = match fixity {
        OperatorFixity::Nullfix => (None, None, true),
        OperatorFixity::Prefix => {
            emit_optional_inline_trivia(committed);
            let right = commit_binding_power(committed, OperatorHeaderRole::RightBindingPower);
            let complete = matches!(right, Recovered::Complete(_));
            (None, recovered_binding_power(right), complete)
        }
        OperatorFixity::Suffix => {
            emit_optional_inline_trivia(committed);
            let left = commit_binding_power(committed, OperatorHeaderRole::LeftBindingPower);
            let complete = matches!(left, Recovered::Complete(_));
            (recovered_binding_power(left), None, complete)
        }
        OperatorFixity::Infix => {
            emit_optional_inline_trivia(committed);
            let left = commit_binding_power(committed, OperatorHeaderRole::LeftBindingPower);
            emit_optional_inline_trivia(committed);
            let right = commit_binding_power(committed, OperatorHeaderRole::RightBindingPower);
            let complete =
                matches!(left, Recovered::Complete(_)) && matches!(right, Recovered::Complete(_));
            (
                recovered_binding_power(left),
                recovered_binding_power(right),
                complete,
            )
        }
    };
    emit_optional_inline_trivia(committed);
    let equals = commit_operator_definition_introducer(committed);
    committed.finish_node();

    match (name, binding_powers_complete, equals) {
        (Some(name), true, Recovered::Complete(equals)) => {
            Recovered::Complete(OperatorHeaderDeclaration {
                range: intro.start..equals.end,
                name,
                visibility: intro
                    .visibility
                    .as_ref()
                    .map_or(Visibility::Private, |prefix| prefix.visibility),
                lazy: intro.lazy_keyword.is_some(),
                fixity,
                left_binding_power,
                right_binding_power,
            })
        }
        _ => Recovered::Incomplete,
    }
}

/// Continues a complete [`commit_operator_header`] in a full parse session.
///
/// The header has already closed its `OperatorHeader` node and produced its
/// header fact before this function starts.  Consequently a missing or
/// malformed body can only produce the full-origin body recovery below; it
/// cannot retract or alter that fact.  The future root driver calls this only
/// after `commit_operator_header` returned [`Recovered::Complete`].
pub(crate) fn commit_operator_definition_body<'parse, 'source, 'local, E>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, FullCstOutput<'source>>,
) -> Recovered<ParsedExpression<rowan::Checkpoint>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let after_equals = commit_required_inline_trivia(committed);
    let leading = if after_equals.as_ref().is_none_or(TriviaRun::is_empty) {
        LeadingTrivia::None
    } else {
        LeadingTrivia::Present
    };
    if let Some(after_equals) = &after_equals {
        committed.emit_trivia(after_equals);
    }
    if after_equals.as_ref().is_none_or(TriviaRun::is_empty)
        && direct_expression_candidate(operators, leading, committed)
    {
        emit_layout_missing(committed);
    }

    if let Some(body) = parse_direct_expression_with_operators(operators, leading, committed) {
        return Recovered::Complete(body);
    }
    if direct_expression_error_retry(
        operators,
        GrammarRole::Statement(StatementRole::OperatorDefinitionBody),
        committed,
    ) {
        if let Some(body) =
            parse_direct_expression_with_operators(operators, LeadingTrivia::None, committed)
        {
            return Recovered::Complete(body);
        }
    }

    emit_operator_definition_body_missing(committed);
    Recovered::Incomplete
}

pub(super) fn emit_operator_definition_body_missing<'parse, 'source, 'local, E>(
    committed: &mut Committed<'parse, 'source, 'local, E, FullCstOutput<'source>>,
) where
    E: ErrorSink<usize>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Statement(StatementRole::OperatorDefinitionBody);
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
                expected: ExpectedSyntax::Expression,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

pub(super) fn recovered_binding_power(value: Recovered<BindingPower>) -> Option<BindingPower> {
    match value {
        Recovered::Complete(value) => Some(value),
        Recovered::Incomplete => None,
    }
}

pub(super) fn fixity_token_kind(fixity: OperatorFixity) -> SyntaxKind {
    match fixity {
        OperatorFixity::Prefix => SyntaxKind::PrefixKw,
        OperatorFixity::Infix => SyntaxKind::InfixKw,
        OperatorFixity::Suffix => SyntaxKind::SuffixKw,
        OperatorFixity::Nullfix => SyntaxKind::NullfixKw,
    }
}

pub(super) fn commit_operator_fixity<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<OperatorFixity>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !commit_operator_fixity_candidate(committed) && !operator_fixity_error_retry(committed) {
        emit_operator_fixity_missing(committed);
        return Recovered::Incomplete;
    }
    let keyword = commit_word(committed).expect("sink-free candidate must still scan a word");
    let fixity = parse_operator_fixity(keyword).expect("candidate recognizes only a fixity");
    committed.token(fixity_token_kind(fixity), keyword.range());
    Recovered::Complete(fixity)
}

/// Fixity is the header shape discriminator.  A malformed spelling owns one
/// Error episode and may retry only at a later recognized discriminator;
/// otherwise the continuation stops without inventing a BP arity.
pub(super) fn operator_fixity_error_retry<'parse, 'source, 'local, E, O>(
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
            if matches!(character, '\r' | '\n' | ';') {
                return (start < end).then_some((start..end, false));
            }
            let checkpoint = i.checkpoint();
            let candidate = i.run(scan_word).and_then(parse_operator_fixity).is_some();
            i.rollback(checkpoint);
            if candidate {
                return (start < end).then_some((start..end, true));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    emit_operator_error(
        committed,
        OperatorHeaderRole::Fixity,
        ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Prefix),
        range,
        crate::session::UnexpectedCategory::Word,
    );
    retry
}

pub(super) fn commit_operator_fixity_candidate<'parse, 'source, 'local, E, O>(
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
        let candidate = i.run(scan_word).and_then(parse_operator_fixity).is_some();
        i.rollback(checkpoint);
        candidate
    })
}

pub(super) fn emit_operator_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: OperatorHeaderRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::OperatorHeader(role));
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

pub(super) fn emit_operator_fixity_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role =
            GrammarRole::Declaration(DeclarationRole::OperatorHeader(OperatorHeaderRole::Fixity));
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
                    expected: ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Prefix),
                    range: at..at,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Infix),
                    range: at..at,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Suffix),
                    range: at..at,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Keyword(crate::session::KeywordEvidence::Nullfix),
                    range: at..at,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                },
            ]),
            0,
        )
    });
    committed.emit_missing(record);
}

pub(super) fn emit_operator_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: OperatorHeaderRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
    category: crate::session::UnexpectedCategory,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::OperatorHeader(role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role: grammar_role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category,
            }]),
            Arc::from([SyntaxExpectation {
                role: grammar_role,
                expected,
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

pub(super) fn emit_operator_name_close_missing<'parse, 'source, 'local, E, O>(
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

pub(super) fn commit_operator_definition_introducer<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(equals) = commit_character(committed, '=') {
        committed.token(SyntaxKind::Equals, equals.clone());
        return Recovered::Complete(equals);
    }
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some(start..end);
            };
            if matches!(character, '\r' | '\n' | ';' | '=') {
                return (start < end).then_some(start..end);
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    });
    if let Some(range) = recovered {
        emit_operator_error(
            committed,
            OperatorHeaderRole::DefinitionIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Equals),
            range,
            crate::session::UnexpectedCategory::OtherCharacter,
        );
        if let Some(equals) = commit_character(committed, '=') {
            committed.token(SyntaxKind::Equals, equals.clone());
            // The punctuation is present after an Error episode, but that
            // episode means this mandatory slot cannot contribute a complete
            // header fact.
            return Recovered::Incomplete;
        }
    }
    emit_operator_missing(
        committed,
        OperatorHeaderRole::DefinitionIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Equals),
    );
    Recovered::Incomplete
}

pub(super) fn commit_operator_name<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<&'source str>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::OperatorName);
    let open = if let Some(open) = commit_character(committed, '(') {
        committed.token(SyntaxKind::LParen, open);
        true
    } else {
        emit_operator_missing(
            committed,
            OperatorHeaderRole::Name,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
        );
        false
    };
    if !open {
        committed.finish_node();
        return Recovered::Incomplete;
    }

    let spelling = committed.probe(|probe| {
        let i = probe.input();
        let start = i.pos();
        while let Some(character) = i.input.remainder().chars().next() {
            if character == ')' {
                break;
            }
            if character.is_whitespace()
                || matches!(
                    character,
                    '(' | '[' | ']' | '{' | '}' | '\\' | ',' | ';' | '"' | '\''
                )
            {
                break;
            }
            i.input.next()?;
        }
        let end = i.pos();
        (start < end).then_some((&i.input.source()[start..end], start..end))
    });
    let Some((name, range)) = spelling else {
        emit_operator_missing(
            committed,
            OperatorHeaderRole::Name,
            ExpectedSyntax::OperatorName,
        );
        if let Some(close) = commit_character(committed, ')') {
            committed.token(SyntaxKind::RParen, close);
        } else {
            emit_operator_name_close_missing(committed);
        }
        committed.finish_node();
        return Recovered::Incomplete;
    };
    committed.token(SyntaxKind::Operator, range);
    let close = if let Some(close) = commit_character(committed, ')') {
        committed.token(SyntaxKind::RParen, close);
        true
    } else {
        emit_operator_name_close_missing(committed);
        false
    };
    committed.finish_node();
    close
        .then_some(name)
        .map_or(Recovered::Incomplete, Recovered::Complete)
}

pub(super) fn commit_binding_power<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: OperatorHeaderRole,
) -> Recovered<BindingPower>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    enum BindingPowerScan {
        Complete(BindingPower, Vec<Range<usize>>, Vec<Range<usize>>),
        Invalid(Range<usize>),
    }

    let scan = committed.probe(|probe| {
        let i = probe.input();
        let mut values = Vec::new();
        let mut components = Vec::new();
        let mut dots = Vec::new();
        let start = i.pos();

        loop {
            let component_start = i.pos();
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
            if component_start == end {
                return (start < end).then_some(BindingPowerScan::Invalid(start..end));
            }
            let Ok(value) = i.input.source()[component_start..end].parse::<i8>() else {
                return Some(BindingPowerScan::Invalid(start..end));
            };
            values.push(value);
            components.push(component_start..end);

            if !i.input.remainder().starts_with('.') {
                break;
            }
            dots.push(scan_character(i, '.')?);
        }

        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let (first, rest) = values.split_first()?;
        Some(BindingPowerScan::Complete(
            BindingPower::new(*first, rest.iter().copied()),
            components,
            dots,
        ))
    });

    match scan {
        Some(BindingPowerScan::Complete(binding_power, components, dots)) => {
            committed.start_node(SyntaxKind::BindingPower);
            for (index, component) in components.into_iter().enumerate() {
                if index > 0 {
                    committed.token(SyntaxKind::Dot, dots[index - 1].clone());
                }
                committed.token(SyntaxKind::Integer, component);
            }
            committed.finish_node();
            Recovered::Complete(binding_power)
        }
        Some(BindingPowerScan::Invalid(range)) => {
            emit_operator_error(
                committed,
                role,
                ExpectedSyntax::BindingPower,
                range,
                crate::session::UnexpectedCategory::DecimalInteger,
            );
            Recovered::Incomplete
        }
        None => {
            if binding_power_error_retry(committed, role) {
                commit_binding_power(committed, role)
            } else {
                emit_operator_missing(committed, role, ExpectedSyntax::BindingPower);
                Recovered::Incomplete
            }
        }
    }
}

/// A binding-power slot retries only at a later digit vector.  Words are a
/// body-NUD safe point, so they stay for the operator-definition continuation
/// rather than becoming a fabricated binding power here.
pub(super) fn binding_power_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: OperatorHeaderRole,
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
            if matches!(character, '\r' | '\n' | ';' | '=') {
                return (start < end).then_some((start..end, false));
            }
            if character.is_ascii_digit() {
                return (start < end).then_some((start..end, true));
            }
            let checkpoint = i.checkpoint();
            let body_nud = i.run(scan_word).is_some();
            i.rollback(checkpoint);
            if body_nud {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    });
    let Some((range, retry)) = recovered else {
        return false;
    };
    emit_operator_error(
        committed,
        role,
        ExpectedSyntax::BindingPower,
        range,
        crate::session::UnexpectedCategory::OtherCharacter,
    );
    retry
}

/// An operator signature before its opaque header body.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct OperatorHeaderDeclaration<'source> {
    pub(super) range: Range<usize>,
    pub(super) name: &'source str,
    pub(super) visibility: Visibility,
    pub(super) lazy: bool,
    pub(super) fixity: OperatorFixity,
    pub(super) left_binding_power: Option<BindingPower>,
    pub(super) right_binding_power: Option<BindingPower>,
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

pub(super) fn header_binding_power(binding_power: &BindingPower) -> HeaderBindingPower {
    HeaderBindingPower::from_components(binding_power.components().to_vec())
}

pub(super) fn parse_operator_header<'source, E>(
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

pub(super) fn parse_operator_header_word_after_trivia<'source, E>(
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

pub(super) fn parse_operator_fixity(word: WordSpan<'_>) -> Option<OperatorFixity> {
    match word.text() {
        "prefix" => Some(OperatorFixity::Prefix),
        "infix" => Some(OperatorFixity::Infix),
        "suffix" => Some(OperatorFixity::Suffix),
        "nullfix" => Some(OperatorFixity::Nullfix),
        _ => None,
    }
}

pub(super) fn parse_operator_name<'source, E>(
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
pub(super) fn parse_binding_power<E>(i: SynIn<E>) -> Option<BindingPower>
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
