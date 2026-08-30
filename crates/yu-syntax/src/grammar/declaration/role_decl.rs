use super::*;
/// A standalone Role declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition and body
/// parsing remain unreachable until their later dedicated gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RoleDeclaration<'source> {
    pub(super) visibility: Visibility,
    pub(super) head: Recovered<Box<TypeExpression<'source>>>,
    pub(super) body: Recovered<RoleBody<'source>>,
    pub(super) range: Range<usize>,
}

impl RoleDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RoleBody<'source> {
    Bodyless {
        semicolon: Range<usize>,
    },
    Braced {
        block: BracedStatementBlockExpression<'source>,
    },
    Colon {
        colon: Range<usize>,
        body: Recovered<RoleColonBody<'source>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum RoleColonBody<'source> {
    Inline {
        statement: Box<Statement<'source>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

/// The sink-free prefix reserved for standalone Role declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 9 connects it to shared statement dispatch.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct RoleStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) role_keyword: WordSpan<'source>,
    pub(super) role_base: usize,
}

/// Recognizes the sink-free prefix reserved for a standalone Role declaration.
///
/// This remains deliberately separate from `recognize_statement_intro` until
/// the later dispatch gate. An exact `role` keyword establishes declaration
/// authority without probing its mandatory head or body.
#[allow(dead_code)]
pub(super) fn recognize_role_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<RoleStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let role_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(role_base, &mut i).filter(|trivia| !trivia.is_empty()) else {
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
    if keyword.text() != "role" {
        i.rollback(checkpoint);
        return None;
    }
    Some(RoleStatementIntro {
        start,
        visibility,
        after_visibility,
        role_keyword: keyword,
        role_base,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct RoleHeadTypeExpressionEpisodeSpec {
    pub(super) stops: StopSet,
    pub(super) scoped_frame: TypeExpressionScopedStopFrame,
    pub(super) policy: TypeExpressionEpisodePolicy,
    pub(super) outer_role: GrammarRole,
}

/// One outer Role head owns body punctuation only in its logical
/// TypeExpression episode. Recursive TypeExpression episodes retain the raw
/// stop bits while the scoped frame suspends Role's authority there.
pub(super) fn role_head_type_expression_episode_spec(
    incoming: StopSet,
    current_episode_depth: usize,
) -> RoleHeadTypeExpressionEpisodeSpec {
    let scoped_stops = StopSet::default()
        .with(StopKind::Colon)
        .with(StopKind::LeftBrace)
        .with(StopKind::Semicolon);
    RoleHeadTypeExpressionEpisodeSpec {
        stops: incoming
            .with(StopKind::Colon)
            .with(StopKind::LeftBrace)
            .with(StopKind::Semicolon),
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default(),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role: GrammarRole::Declaration(DeclarationRole::Role(
            crate::session::RoleDeclarationRole::Head,
        )),
    }
}

pub(super) fn parse_required_role_head_type_expression_isolated<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = role_head_type_expression_episode_spec(
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("the mandatory Role head TypeExpression entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    match parsed {
        Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

pub(super) fn commit_required_role_head_type_expression_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = committed.probe(|probe| {
        let i = probe.input();
        role_head_type_expression_episode_spec(
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
        )
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    });
    let parsed = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = parsed.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

/// Parses one accepted Role continuation without making Role reachable from
/// the public statement dispatcher.  The prefix, head episode, and body
/// punctuation each retain their own authority so Gate 9 can promote this
/// exact adapter atomically.
pub(crate) fn parse_role_declaration_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<RoleDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let declaration = (|| {
        let intro = i.run(recognize_role_statement_intro)?;
        let visibility = intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility);
        let head = if any_ambient_owner_claims(&mut i) {
            Recovered::Incomplete
        } else {
            let checkpoint = i.checkpoint();
            if mod_trivia(intro.role_base, &mut i).is_some() {
                parse_required_role_head_type_expression_isolated(&mut i)
            } else {
                i.rollback(checkpoint);
                Recovered::Incomplete
            }
        };
        let body = parse_role_body_ast(table, intro.role_base, &mut i);
        let end = i.pos();
        Some(RoleDeclaration {
            visibility,
            head,
            body,
            range: intro.start..end,
        })
    })();
    i.errors_rollback(errors_checkpoint);
    declaration
}

pub(super) fn parse_role_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    role_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<RoleBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(role_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    };
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        if role_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
            return parse_role_body_ast(table, role_base, i);
        }
        return Recovered::Incomplete;
    };
    match punctuation.kind() {
        PunctuationKind::Semicolon => Recovered::Complete(RoleBody::Bodyless {
            semicolon: punctuation.range(),
        }),
        PunctuationKind::Open(Delimiter::Brace) => Recovered::Complete(RoleBody::Braced {
            block: parse_braced_statement_block_expression(table, punctuation.range(), i),
        }),
        PunctuationKind::Colon => Recovered::Complete(RoleBody::Colon {
            colon: punctuation.range(),
            body: parse_role_colon_body_ast(table, role_base, i)
                .map_or(Recovered::Incomplete, Recovered::Complete),
        }),
        _ => {
            i.rollback(checkpoint);
            if role_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
                parse_role_body_ast(table, role_base, i)
            } else {
                Recovered::Incomplete
            }
        }
    }
}

pub(super) fn parse_role_colon_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    role_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<RoleColonBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n']) {
        if i.local.line().line_indent <= role_base {
            i.rollback(checkpoint);
            return None;
        }
        let block_indent = i.local.line().line_indent;
        return Some(RoleColonBody::Indented {
            block: parse_indented_role_body(table, trivia, role_base, block_indent, i),
        });
    }
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
        crate::session::InlineStatementOwnerKind::RoleColonBody,
    );
    let statement = i
        .run(from_fn(|i| parse_canonical_statement(table, i)))
        .or_else(|| {
            role_body_error_retry_ast(table, i)
                .is_some_and(|retry| retry)
                .then(|| i.run(from_fn(|i| parse_canonical_statement(table, i))))
                .flatten()
        });
    let body = statement.map(|statement| {
        let terminal = i.checkpoint();
        if i.run(scan_punctuation)
            .is_none_or(|punctuation| punctuation.kind() != PunctuationKind::Semicolon)
        {
            i.rollback(terminal);
        }
        RoleColonBody::Inline {
            statement: Box::new(statement),
        }
    });
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    body
}

pub(super) fn role_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
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

pub(super) fn role_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Comma
                | PunctuationKind::Close(
                    Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                )
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon
                | PunctuationKind::Semicolon
        )
    });
    i.rollback(checkpoint);
    pending
}

/// AST half of the one maximal Role body-introducer invalid run.  The direct
/// emission is deliberately deferred to Gate 5, but starter/boundary input
/// ownership already matches that future committed path.
pub(super) fn role_body_introducer_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if role_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if role_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

pub(super) fn role_body_error_retry_ast<'source, E>(
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
        if role_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
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

/// Direct-CST counterpart of [`parse_role_declaration_isolated`].  Like the
/// AST adapter, it remains deliberately outside statement dispatch until the
/// Gate 9 atomic promotion.
pub(crate) fn commit_role_declaration_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: RoleStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::RoleDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::RoleKw, intro.role_keyword.range());

    let head_terminated_incomplete = if committed
        .probe(|probe| any_ambient_owner_claims(probe.input()))
    {
        true
    } else if let Some(trivia) = committed.probe(|probe| mod_trivia(intro.role_base, probe.input()))
    {
        committed.emit_trivia(&trivia);
        matches!(
            commit_required_role_head_type_expression_isolated(committed),
            Recovered::Incomplete
        )
    } else {
        true
    };

    commit_role_body_isolated(
        table,
        intro.role_base,
        committed,
        head_terminated_incomplete,
    );
    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    Recovered::Complete(intro.start..end)
}

#[derive(Clone)]
pub(super) enum RoleBodyStarter {
    Bodyless(Range<usize>),
    Braced(Range<usize>),
    Colon(Range<usize>),
}

pub(super) fn commit_role_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    role_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    head_terminated_incomplete: bool,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        return;
    }
    let starter = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let starter = mod_trivia(role_base, i).and_then(|trivia| {
            let punctuation = i.run(scan_punctuation)?;
            let starter = match punctuation.kind() {
                PunctuationKind::Semicolon => RoleBodyStarter::Bodyless(punctuation.range()),
                PunctuationKind::Open(Delimiter::Brace) => {
                    RoleBodyStarter::Braced(punctuation.range())
                }
                PunctuationKind::Colon => RoleBodyStarter::Colon(punctuation.range()),
                _ => return None,
            };
            Some((trivia, starter))
        });
        i.rollback(checkpoint);
        starter
    });
    let Some((trivia, starter)) = starter else {
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(role_base, i);
            i.rollback(checkpoint);
            trivia
        });
        let Some(trivia) = trivia else {
            if !head_terminated_incomplete {
                emit_role_body_introducer_missing(committed);
            }
            return;
        };
        let newline = committed
            .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
        if newline {
            if !head_terminated_incomplete {
                emit_role_body_introducer_missing(committed);
            }
            return;
        }
        let consumed_trivia = committed
            .probe(|probe| mod_trivia(role_base, probe.input()))
            .expect("the Role body-introducer recovery leaves its leading trivia at the cursor");
        assert_eq!(consumed_trivia.range(), trivia.range());
        committed.emit_trivia(&consumed_trivia);
        match role_body_introducer_error_retry(committed) {
            Some(true) => {
                commit_role_body_isolated(table, role_base, committed, head_terminated_incomplete);
            }
            Some(false) => {}
            None if !head_terminated_incomplete => emit_role_body_introducer_missing(committed),
            None => {}
        }
        return;
    };

    let consumed_trivia = committed
        .probe(|probe| mod_trivia(role_base, probe.input()))
        .expect("the accepted Role body starter leaves its leading trivia at the cursor");
    assert_eq!(consumed_trivia.range(), trivia.range());
    committed.emit_trivia(&consumed_trivia);
    let punctuation = committed
        .probe(|probe| probe.input().run(scan_punctuation))
        .expect("the accepted Role body starter remains at the cursor");
    match starter {
        RoleBodyStarter::Bodyless(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
        }
        RoleBodyStarter::Braced(range) => {
            assert_eq!(punctuation.range(), range);
            commit_braced_statement_block_expression(table, range, committed);
        }
        RoleBodyStarter::Colon(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range);
            commit_role_colon_body_isolated(table, role_base, committed);
        }
    }
}

pub(super) fn commit_role_colon_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    role_base: usize,
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
        .expect("trivia scan is total");
    let newline = committed
        .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
    if newline && committed.probe(|probe| probe.input().local.line().line_indent <= role_base) {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_role_body_missing(committed);
        return;
    }
    if newline {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_role_body(table, trivia, role_base, block_indent, committed);
        return;
    }
    committed.emit_trivia(&trivia);
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::RoleColonBody,
            )
    });
    let statement_committed = if commit_canonical_statement(table, LeadingTrivia::None, committed) {
        true
    } else {
        match role_body_error_retry(table, committed) {
            Some(true) => commit_canonical_statement(table, LeadingTrivia::None, committed),
            Some(false) => false,
            None => {
                emit_role_body_missing(committed);
                false
            }
        }
    };
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

pub(super) fn role_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
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
        loop {
            let i = probe.input();
            if role_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if role_body_boundary_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let character = i.input.remainder().chars().next()?;
            if matches!(character, '\r' | '\n') {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            i.input.next()?;
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    })?;
    emit_role_error(
        committed,
        crate::session::RoleDeclarationRole::BodyIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        recovered.0,
    );
    Some(recovered.1)
}

pub(super) fn role_body_error_retry<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
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
        loop {
            {
                let i = probe.input();
                if role_body_boundary_pending(i) {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                let character = i.input.remainder().chars().next()?;
                if matches!(character, '\r' | '\n') {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                i.input.next()?;
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_canonical_statement_candidate(
                table,
                LeadingTrivia::None,
                probe,
            ) {
                let end = probe.input().pos();
                return Some((start..end, true));
            }
        }
    })?;
    emit_role_error(
        committed,
        crate::session::RoleDeclarationRole::Body,
        ExpectedSyntax::Statement,
        recovered.0,
    );
    Some(recovered.1)
}

/// Emits the one outer-body recovery owned by an accepted Role declaration.
pub(super) fn emit_role_body_introducer_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Role(
            crate::session::RoleDeclarationRole::BodyIntroducer,
        ));
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

pub(super) fn emit_role_body_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_role_missing(
        committed,
        crate::session::RoleDeclarationRole::Body,
        ExpectedSyntax::Statement,
    );
}

pub(super) fn emit_role_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::RoleDeclarationRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Role(role));
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
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

pub(super) fn emit_role_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::RoleDeclarationRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Role(role));
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
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}
