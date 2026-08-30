use super::*;

/// The committed prefix of a direct binding declaration.
///
/// The continuation owns the Pattern target and optional exact-equals body;
/// keeping both out of this sink-free prefix lets every statement owner cut at
/// the visibility word before recovery is selected.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: VisibilityPrefix<'source>,
}

pub(crate) struct ParsedBindingDeclaration<'source, C> {
    pub(super) visibility: Visibility,
    pub(super) range: Range<usize>,
    pub(super) target: Recovered<ParsedPattern<C>>,
    pub(super) definition: Option<ParsedBindingDefinition<C>>,
    pub(super) marker: std::marker::PhantomData<&'source str>,
}

pub(crate) struct ParsedBindingDefinition<C> {
    pub(super) equals: Range<usize>,
    pub(super) body: Recovered<ParsedBindingBody<C>>,
    pub(super) range: Range<usize>,
}

pub(crate) struct ParsedBindingBody<C> {
    pub(super) range: Range<usize>,
    pub(super) marker: std::marker::PhantomData<C>,
}

impl<'source, C> ParsedBindingDeclaration<'source, C> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub(crate) fn target(&self) -> &Recovered<ParsedPattern<C>> {
        &self.target
    }

    pub(crate) fn definition(&self) -> Option<&ParsedBindingDefinition<C>> {
        self.definition.as_ref()
    }
}

impl<C> ParsedBindingDefinition<C> {
    pub(crate) fn body(&self) -> &Recovered<ParsedBindingBody<C>> {
        &self.body
    }
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

impl<C> ParsedBindingBody<C> {
    pub(super) fn new(range: Range<usize>) -> Self {
        Self {
            range,
            marker: std::marker::PhantomData,
        }
    }
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

/// Recognizes one visibility prefix of a binding statement without giving the
/// speculative branch access to a CST or recovery sink.
pub(crate) fn recognize_binding_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<BindingStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let keyword = i.run(scan_word)?;
    let visibility = visibility_prefix(keyword)?;
    Some(BindingStatementIntro { start, visibility })
}

/// Commits one binding declaration without reconstructing its AST from CST.
pub(crate) fn commit_binding_declaration<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: BindingStatementIntro<'source>,
) -> Recovered<ParsedBindingDeclaration<'source, O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::BindingStatement);
    committed.start_node(SyntaxKind::BindingHeader);
    emit_visibility(committed, &intro.visibility);
    let binding_base = committed.probe(|probe| {
        probe
            .input()
            .local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column)
    });
    let target_trivia = committed.probe(|probe| binding_trivia(binding_base, probe.input()));
    if let Some(trivia) = &target_trivia {
        committed.emit_trivia(trivia);
    }
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .with(StopKind::Equal)
    });
    committed.probe(|probe| probe.input().local.push_stop_set(stops));
    let target = parse_direct_pattern_with_outer_missing_role(
        operators,
        LeadingTrivia::None,
        Some(GrammarRole::Declaration(DeclarationRole::Binding(
            BindingRole::Target,
        ))),
        committed,
    )
    .map_or_else(
        || {
            emit_binding_missing(committed, BindingRole::Target, ExpectedSyntax::Pattern);
            Recovered::Incomplete
        },
        Recovered::Complete,
    );
    committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops)));
    let definition_intro = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let Some(trivia) = binding_trivia(binding_base, i) else {
            i.rollback(checkpoint);
            return None;
        };
        let Some(equals) = i.run(scan_declaration_exact_equals) else {
            i.rollback(checkpoint);
            return None;
        };
        Some((trivia, equals))
    });
    if let Some((trivia, equals)) = &definition_intro {
        committed.emit_trivia(trivia);
        committed.token(SyntaxKind::Equals, equals.clone());
    }
    committed.finish_node();

    let definition = definition_intro.map(|(_trivia, equals)| {
        committed.start_node(SyntaxKind::BindingBody);
        let body = commit_binding_body(operators, binding_base, committed);
        let end = match &body {
            Recovered::Complete(body) => body.range().end,
            Recovered::Incomplete => equals.end,
        };
        committed.finish_node();
        ParsedBindingDefinition {
            equals: equals.clone(),
            body,
            range: equals.start..end,
        }
    });
    let end = definition.as_ref().map_or_else(
        || match &target {
            Recovered::Complete(target) => target.range().end,
            Recovered::Incomplete => committed.probe(|probe| probe.input().pos()),
        },
        |definition| definition.range.end,
    );
    committed.finish_node();
    Recovered::Complete(ParsedBindingDeclaration {
        visibility: intro.visibility.visibility,
        range: intro.start..end,
        target,
        definition,
        marker: std::marker::PhantomData,
    })
}

pub(super) fn commit_binding_body<'parse, 'source, 'local, E, O>(
    operators: &crate::operator::OperatorTable,
    binding_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<ParsedBindingBody<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let body_start = committed.probe(|probe| probe.input().pos());
    commit_binding_style_body(
        operators,
        binding_base,
        GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body)),
        |expression| ParsedBindingBody::new(expression.range()),
        |trivia, block_indent, committed| {
            commit_indented_binding_body(operators, trivia, binding_base, block_indent, committed);
            let end = committed.probe(|probe| probe.input().pos());
            ParsedBindingBody::new(body_start..end)
        },
        |committed| {
            direct_expression_error_retry(
                operators,
                GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body)),
                committed,
            )
            .then_some(BindingStyleInlineRecovery::Retry)
            .unwrap_or(BindingStyleInlineRecovery::None)
        },
        committed,
    )
}

pub(super) fn emit_binding_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: BindingRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let grammar_role = GrammarRole::Declaration(DeclarationRole::Binding(role));
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

/// A visibility-prefixed binding declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingDeclaration<'source> {
    pub(super) visibility: Visibility,
    pub(super) target: Recovered<Pattern<'source>>,
    pub(super) definition: Option<BindingDefinition<'source>>,
    pub(super) range: Range<usize>,
}

impl<'source> BindingDeclaration<'source> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }

    pub(crate) fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub(crate) fn target(&self) -> &Recovered<Pattern<'source>> {
        &self.target
    }

    pub(crate) fn definition(&self) -> Option<&BindingDefinition<'source>> {
        self.definition.as_ref()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct BindingDefinition<'source> {
    pub(super) equals: Range<usize>,
    pub(super) body: Recovered<BindingBody<'source>>,
    pub(super) range: Range<usize>,
}

impl<'source> BindingDefinition<'source> {
    pub(crate) fn equals(&self) -> Range<usize> {
        self.equals.clone()
    }
    pub(crate) fn body(&self) -> &Recovered<BindingBody<'source>> {
        &self.body
    }
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum BindingBody<'source> {
    Inline {
        expression: OperatorChain<'source>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

pub(super) fn parse_binding_declaration<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<BindingDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let table = crate::operator::OperatorTable::empty();
    parse_binding_declaration_with_operators(&table, i)
}

pub(crate) fn parse_binding_declaration_with_operators<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<BindingDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let keyword = i.run(scan_word)?;
    let visibility = visibility_prefix(keyword)?.visibility;
    let binding_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    binding_trivia(binding_base, &mut i)?;
    let stops = i.local.stop_set().unwrap_or_default().with(StopKind::Equal);
    i.local.push_stop_set(stops);
    let target_role = GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Target));
    let target = i.run(from_fn(|i| {
        parse_pattern_with_outer_missing_role(table, Some(target_role), i)
    }));
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    let target = target.map_or(Recovered::Incomplete, Recovered::Complete);
    let mut end = match &target {
        Recovered::Complete(pattern) => pattern.range().end,
        Recovered::Incomplete => i.pos(),
    };

    let definition = {
        let checkpoint = i.checkpoint();
        if binding_trivia(binding_base, &mut i).is_none() {
            i.rollback(checkpoint);
            None
        } else if let Some(equals) = i.run(scan_declaration_exact_equals) {
            let body_start = equals.start;
            let body = parse_binding_body_ast(table, binding_base, &mut i)
                .map_or(Recovered::Incomplete, Recovered::Complete);
            let body_end = match &body {
                Recovered::Complete(BindingBody::Inline { expression }) => expression.range().end,
                Recovered::Complete(BindingBody::Indented { block }) => block.range().end,
                Recovered::Incomplete => i.pos(),
            };
            end = body_end.max(equals.end);
            Some(BindingDefinition {
                equals,
                body,
                range: body_start..end,
            })
        } else {
            i.rollback(checkpoint);
            None
        }
    };

    Some(BindingDeclaration {
        visibility,
        target,
        definition,
        range: start..end,
    })
}

pub(super) fn parse_binding_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    binding_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<BindingBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_binding_style_body(
        binding_base,
        |_trivia, i| {
            i.run(from_fn(|i| parse_expression_with_operators(table, i)))
                .map(|expression| BindingBody::Inline { expression })
        },
        |trivia, block_indent, i| BindingBody::Indented {
            block: parse_indented_binding_body(table, trivia, binding_base, block_indent, i),
        },
        i,
    )
}

pub(super) fn binding_trivia<E>(binding_base: usize, i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n'])
        && i.local.line().line_indent <= binding_base
    {
        i.rollback(checkpoint);
        return None;
    }
    Some(trivia)
}
