use super::*;

/// The sink-free prefix reserved for standalone Act declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 10 connects it to shared statement dispatch.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ActStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) act_keyword: WordSpan<'source>,
    pub(super) act_base: usize,
}

/// Recognizes the sink-free prefix reserved for a standalone Act declaration.
///
/// Unlike the other visibility-prefixed declaration introductions, `my act`
/// preserves Yulang2's local-binding collision. It becomes an Act only when
/// a raw TypeExpression name is visible after the keyword; the lookahead is
/// rolled back so the later head episode owns the same bytes.
#[allow(dead_code)]
pub(super) fn recognize_act_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ActStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let act_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(act_base, &mut i).filter(|trivia| !trivia.is_empty()) else {
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
    if keyword.text() != "act" {
        i.rollback(checkpoint);
        return None;
    }
    if matches!(
        visibility,
        Some(VisibilityPrefix {
            visibility: Visibility::Private,
            ..
        })
    ) {
        let head_checkpoint = i.checkpoint();
        let head_candidate =
            mod_trivia(act_base, &mut i).is_some() && act_raw_type_head_candidate(&mut i);
        i.rollback(head_checkpoint);
        if !head_candidate {
            i.rollback(checkpoint);
            return None;
        }
    }
    Some(ActStatementIntro {
        start,
        visibility,
        after_visibility,
        act_keyword: keyword,
        act_base,
    })
}

/// Peeks exactly the raw TypeExpression-name forms relevant to ACT-J.
///
/// This deliberately matches `scan_type_name`'s lexical admission without
/// invoking a TypeExpression episode: ordinary words and apostrophe sigils
/// qualify, while `$` and `&` stay outside the current TypeExpression grammar.
pub(super) fn act_raw_type_head_candidate<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let candidate = i
        .run(scan_path_segment)
        .is_some_and(|name| !matches!(name.text().chars().next(), Some('$' | '&')));
    i.rollback(checkpoint);
    candidate
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ActTypeExpressionSlot {
    Head,
    Source,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ActTypeExpressionEpisodeSpec {
    pub(super) stops: StopSet,
    pub(super) scoped_frame: TypeExpressionScopedStopFrame,
    pub(super) policy: TypeExpressionEpisodePolicy,
    pub(super) outer_role: GrammarRole,
}

/// One outer Act head owns its source/body punctuation only in its logical
/// TypeExpression episode. Recursive TypeExpression episodes retain the raw
/// stop bits while the scoped frame suspends Act's authority there.
pub(super) fn act_type_expression_episode_spec(
    slot: ActTypeExpressionSlot,
    incoming: StopSet,
    current_episode_depth: usize,
) -> ActTypeExpressionEpisodeSpec {
    let scoped_stops = match slot {
        ActTypeExpressionSlot::Head => StopSet::default().with(StopKind::Equal),
        ActTypeExpressionSlot::Source => StopSet::default(),
    }
    .with(StopKind::Colon)
    .with(StopKind::LeftBrace)
    .with(StopKind::Semicolon)
    .with(StopKind::Derives);
    let stops = match slot {
        ActTypeExpressionSlot::Head => incoming.with(StopKind::Equal),
        ActTypeExpressionSlot::Source => incoming,
    }
    .with(StopKind::Colon)
    .with(StopKind::LeftBrace)
    .with(StopKind::Semicolon)
    .with(StopKind::Derives);
    let act_role = match slot {
        ActTypeExpressionSlot::Head => crate::session::ActDeclarationRole::Head,
        ActTypeExpressionSlot::Source => crate::session::ActDeclarationRole::Source,
    };
    ActTypeExpressionEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default().with(StopKind::Derives),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role: GrammarRole::Declaration(DeclarationRole::Act(act_role)),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ActDeclarationCompanionTail {
    PostHead,
    PostSource,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ActTypeExpressionWithTail<T> {
    pub(super) value: Recovered<T>,
    pub(super) tail: Option<ActDeclarationCompanionTail>,
}

fn act_companion_type_expression_episode_spec(
    slot: ActTypeExpressionSlot,
    incoming: StopSet,
    current_episode_depth: usize,
) -> ActTypeExpressionEpisodeSpec {
    let ordinary = act_type_expression_episode_spec(slot, incoming, current_episode_depth);
    ActTypeExpressionEpisodeSpec {
        stops: ordinary.stops.with(StopKind::With),
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: ordinary.scoped_frame.stops.with(StopKind::With),
            ..ordinary.scoped_frame
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: ordinary
                .policy
                .fresh_primary_locally_owned_stops
                .with(StopKind::With),
            ..ordinary.policy
        },
        outer_role: ordinary.outer_role,
    }
}

fn act_companion_tail(slot: ActTypeExpressionSlot) -> ActDeclarationCompanionTail {
    match slot {
        ActTypeExpressionSlot::Head => ActDeclarationCompanionTail::PostHead,
        ActTypeExpressionSlot::Source => ActDeclarationCompanionTail::PostSource,
    }
}

pub(super) fn parse_required_act_type_expression_with_companion_handoff_isolated<'source, E>(
    slot: ActTypeExpressionSlot,
    act_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ActTypeExpressionWithTail<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if recognize_declaration_companion_handoff(act_base, i).is_some() {
        return ActTypeExpressionWithTail {
            value: Recovered::Incomplete,
            tail: Some(act_companion_tail(slot)),
        };
    }
    let trivia_checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(act_base, i) else {
        i.rollback(trivia_checkpoint);
        return ActTypeExpressionWithTail {
            value: Recovered::Incomplete,
            tail: None,
        };
    };
    let episode = act_companion_type_expression_episode_spec(
        slot,
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_handoff_recovery_isolated(
                    Some(episode.outer_role),
                    episode.policy,
                    |i| recognize_declaration_companion_handoff(act_base, i).is_some(),
                    i,
                ),
            )
        }))
        .expect("the isolated companion-aware Act TypeExpression entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    ActTypeExpressionWithTail {
        value: match parsed {
            Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
            Recovered::Incomplete => Recovered::Incomplete,
        },
        tail: recognize_declaration_companion_handoff(act_base, i)
            .is_some()
            .then_some(act_companion_tail(slot)),
    }
}

pub(super) fn commit_required_act_type_expression_with_companion_handoff_isolated<
    'parse,
    'source,
    'local,
    E,
    O,
>(
    slot: ActTypeExpressionSlot,
    act_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ActTypeExpressionWithTail<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(with) =
        committed.probe(|probe| recognize_declaration_companion_handoff(act_base, probe.input()))
    {
        emit_act_companion_slot_missing(slot, with.start, committed);
        return ActTypeExpressionWithTail {
            value: Recovered::Incomplete,
            tail: Some(act_companion_tail(slot)),
        };
    }
    let trivia = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = mod_trivia(act_base, i);
        if trivia.is_none() {
            i.rollback(checkpoint);
        }
        trivia
    });
    let Some(trivia) = trivia else {
        return ActTypeExpressionWithTail {
            value: Recovered::Incomplete,
            tail: None,
        };
    };
    committed.emit_trivia(&trivia);
    let episode = committed.probe(|probe| {
        let i = probe.input();
        act_companion_type_expression_episode_spec(
            slot,
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
    let parsed = commit_direct_type_expression_with_handoff_recovery_isolated(
        Some(episode.outer_role),
        episode.policy,
        |i| recognize_declaration_companion_handoff(act_base, i).is_some(),
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
    let tail = committed
        .probe(|probe| recognize_declaration_companion_handoff(act_base, probe.input()))
        .is_some()
        .then_some(act_companion_tail(slot));
    let range = parsed.range();
    ActTypeExpressionWithTail {
        value: if range.is_empty() {
            Recovered::Incomplete
        } else {
            Recovered::Complete(range)
        },
        tail,
    }
}

fn emit_act_companion_slot_missing<'parse, 'source, 'local, E, O>(
    slot: ActTypeExpressionSlot,
    at: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let act_role = match slot {
        ActTypeExpressionSlot::Head => crate::session::ActDeclarationRole::Head,
        ActTypeExpressionSlot::Source => crate::session::ActDeclarationRole::Source,
    };
    let role = GrammarRole::Declaration(DeclarationRole::Act(act_role));
    let record = committed.probe(|probe| {
        CommittedRecoveryRecord::new(
            probe.input().local,
            RecoverySiteKey {
                role,
                range: at..at,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::TypeExpression,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

pub(super) fn parse_required_act_head_type_expression_isolated<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = act_type_expression_episode_spec(
        ActTypeExpressionSlot::Head,
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
        .expect("the mandatory Act head TypeExpression entry is total");
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

pub(super) fn commit_required_act_head_type_expression_isolated<'parse, 'source, 'local, E, O>(
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
        act_type_expression_episode_spec(
            ActTypeExpressionSlot::Head,
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

pub(super) fn parse_required_act_source_type_expression_isolated<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = act_type_expression_episode_spec(
        ActTypeExpressionSlot::Source,
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
        .expect("the mandatory Act source TypeExpression entry is total");
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

pub(super) fn commit_required_act_source_type_expression_isolated<'parse, 'source, 'local, E, O>(
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
        act_type_expression_episode_spec(
            ActTypeExpressionSlot::Source,
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

/// Parses an optional Act copy source after the completed or recovered head.
/// A non-equals tail is rolled back intact for Gate 5's body-form judge.
pub(super) fn parse_act_source_clause_after_head_isolated<'source, E>(
    act_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ActSourceClause<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return None;
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(act_base, i) else {
        i.rollback(checkpoint);
        return None;
    };
    let Some(equals) = i.run(scan_declaration_exact_equals) else {
        i.rollback(checkpoint);
        return None;
    };
    let source_gap = i.checkpoint();
    let source = if mod_trivia(act_base, i).is_some() {
        parse_required_act_source_type_expression_isolated(i)
    } else {
        i.rollback(source_gap);
        parse_required_act_source_type_expression_isolated(i)
    };
    let end = match &source {
        Recovered::Complete(source) => source.range().end,
        Recovered::Incomplete => equals.end,
    };
    Some(ActSourceClause {
        equals: equals.clone(),
        source,
        range: equals.start..end,
    })
}

/// Direct-CST counterpart of [`parse_act_source_clause_after_head_isolated`].
/// It emits only actual head/source gaps and the equals token; an absent
/// equals leaves the full original tail untouched for Gate 5.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CommittedActSourceClause {
    pub(super) equals: Range<usize>,
    pub(super) source: Recovered<Range<usize>>,
    pub(super) range: Range<usize>,
}

pub(super) fn commit_act_source_clause_after_head_isolated<'parse, 'source, 'local, E, O>(
    act_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<CommittedActSourceClause>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let equals = committed.probe(|probe| {
        let i = probe.input();
        if any_ambient_owner_claims(i) {
            return None;
        }
        let checkpoint = i.checkpoint();
        let equals = mod_trivia(act_base, i).and_then(|_| i.run(scan_declaration_exact_equals));
        i.rollback(checkpoint);
        equals
    })?;
    let head_gap = committed
        .probe(|probe| mod_trivia(act_base, probe.input()))
        .expect("the committed Act equals was already classified");
    committed.emit_trivia(&head_gap);
    let actual_equals = committed
        .probe(|probe| probe.input().run(scan_declaration_exact_equals))
        .expect("the committed Act equals remains at the cursor");
    debug_assert_eq!(actual_equals, equals);
    committed.token(SyntaxKind::Equals, actual_equals.clone());

    let source_gap = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = mod_trivia(act_base, i);
        i.rollback(checkpoint);
        trivia
    });
    if let Some(source_gap) = source_gap {
        let consumed = committed
            .probe(|probe| mod_trivia(act_base, probe.input()))
            .expect("the committed Act source gap was already classified");
        assert_eq!(consumed.range(), source_gap.range());
        committed.emit_trivia(&consumed);
    }
    let source = commit_required_act_source_type_expression_isolated(committed);
    let end = match &source {
        Recovered::Complete(range) => range.end,
        Recovered::Incomplete => actual_equals.end,
    };
    Some(CommittedActSourceClause {
        equals: actual_equals.clone(),
        source,
        range: actual_equals.start..end,
    })
}

fn parse_act_source_clause_with_companion_handoff<'source, E>(
    act_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (
    Option<ActSourceClause<'source>>,
    Option<ActDeclarationCompanionTail>,
)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return (None, None);
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(act_base, i) else {
        i.rollback(checkpoint);
        return (None, None);
    };
    let Some(equals) = i.run(scan_declaration_exact_equals) else {
        i.rollback(checkpoint);
        return (None, None);
    };
    let parsed = parse_required_act_type_expression_with_companion_handoff_isolated(
        ActTypeExpressionSlot::Source,
        act_base,
        i,
    );
    let end = match &parsed.value {
        Recovered::Complete(source) => source.range().end,
        Recovered::Incomplete => equals.end,
    };
    (
        Some(ActSourceClause {
            equals: equals.clone(),
            source: parsed.value,
            range: equals.start..end,
        }),
        parsed.tail,
    )
}

fn commit_act_source_clause_with_companion_handoff<'parse, 'source, 'local, E, O>(
    act_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> (
    Option<CommittedActSourceClause>,
    Option<ActDeclarationCompanionTail>,
)
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let equals = committed.probe(|probe| {
        let i = probe.input();
        if any_ambient_owner_claims(i) {
            return None;
        }
        let checkpoint = i.checkpoint();
        let equals = mod_trivia(act_base, i).and_then(|_| i.run(scan_declaration_exact_equals));
        i.rollback(checkpoint);
        equals
    });
    let Some(equals) = equals else {
        return (None, None);
    };
    let head_gap = committed
        .probe(|probe| mod_trivia(act_base, probe.input()))
        .expect("the committed Act equals was already classified");
    committed.emit_trivia(&head_gap);
    let actual_equals = committed
        .probe(|probe| probe.input().run(scan_declaration_exact_equals))
        .expect("the committed Act equals remains at the cursor");
    debug_assert_eq!(actual_equals, equals);
    committed.token(SyntaxKind::Equals, actual_equals.clone());
    let parsed = commit_required_act_type_expression_with_companion_handoff_isolated(
        ActTypeExpressionSlot::Source,
        act_base,
        committed,
    );
    let end = match &parsed.value {
        Recovered::Complete(range) => range.end,
        Recovered::Incomplete => actual_equals.end,
    };
    (
        Some(CommittedActSourceClause {
            equals: actual_equals.clone(),
            source: parsed.value,
            range: actual_equals.start..end,
        }),
        parsed.tail,
    )
}

/// Parses one accepted Act continuation without making Act reachable from
/// the public statement dispatcher. The Head/Source slots and the body-form
/// judge remain distinct after Gate 10's atomic promotion.
pub(crate) fn parse_act_declaration_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ActDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let declaration = (|| {
        let intro = i.run(recognize_act_statement_intro)?;
        let visibility = intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility);
        let parsed_head = if any_ambient_owner_claims(&mut i) {
            ActTypeExpressionWithTail {
                value: Recovered::Incomplete,
                tail: None,
            }
        } else {
            parse_required_act_type_expression_with_companion_handoff_isolated(
                ActTypeExpressionSlot::Head,
                intro.act_base,
                &mut i,
            )
        };
        let head = parsed_head.value;
        let mut derives = Vec::new();
        let head_derives = if matches!(head, Recovered::Complete(_)) {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Act,
                DerivesAttachmentPosition::Header,
                intro.act_base,
                &mut i,
            )
            .map(|start| parse_derives_attachments_with_companion_handoff_isolated(start, &mut i))
        } else {
            None
        };
        let head_derives_tail = head_derives.as_ref().and_then(|parsed| parsed.tail);
        if let Some(parsed) = head_derives {
            derives.extend(parsed.attachments);
        }
        let post_head_companion = matches!(
            parsed_head.tail,
            Some(ActDeclarationCompanionTail::PostHead)
        ) || head_derives_tail.is_some();
        if let Some(tail) = head_derives_tail {
            debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Act);
            debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
        }

        let mut companion = None;
        let (source, body) = if post_head_companion {
            companion = Some(parse_act_declaration_companion_after_handoff(
                table,
                intro.act_base,
                &mut i,
            ));
            (None, Recovered::Incomplete)
        } else {
            let (source, source_tail) =
                parse_act_source_clause_with_companion_handoff(intro.act_base, &mut i);
            let source_derives = if source
                .as_ref()
                .is_some_and(|clause| matches!(clause.source, Recovered::Complete(_)))
            {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Act,
                    DerivesAttachmentPosition::Header,
                    intro.act_base,
                    &mut i,
                )
                .map(|start| {
                    parse_derives_attachments_with_companion_handoff_isolated(start, &mut i)
                })
            } else {
                None
            };
            let source_derives_tail = source_derives.as_ref().and_then(|parsed| parsed.tail);
            if let Some(parsed) = source_derives {
                derives.extend(parsed.attachments);
            }
            let post_source_companion =
                matches!(source_tail, Some(ActDeclarationCompanionTail::PostSource))
                    || source_derives_tail.is_some();
            if let Some(tail) = source_derives_tail {
                debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Act);
                debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
            }
            if post_source_companion {
                companion = Some(parse_act_declaration_companion_after_handoff(
                    table,
                    intro.act_base,
                    &mut i,
                ));
                (source, Recovered::Incomplete)
            } else {
                let head_and_source_complete = matches!(head, Recovered::Complete(_))
                    && source
                        .as_ref()
                        .is_none_or(|clause| matches!(clause.source, Recovered::Complete(_)));
                let body =
                    parse_act_body_ast(table, intro.act_base, head_and_source_complete, &mut i);
                if act_body_has_actual_trailing_close(&body)
                    && let Some(start) = recognize_derives_attachment_start(
                        DerivesAttachmentOwner::Act,
                        DerivesAttachmentPosition::Trailing,
                        intro.act_base,
                        &mut i,
                    )
                {
                    derives.extend(parse_derives_attachments_isolated(start, &mut i));
                }
                (source, body)
            }
        };
        let end = i.pos();
        Some(ActDeclaration {
            visibility,
            head,
            source,
            derives,
            companion,
            body,
            range: intro.start..end,
        })
    })();
    i.errors_rollback(errors_checkpoint);
    declaration
}

pub(super) fn parse_act_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
    head_and_source_complete: bool,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<ActBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return head_and_source_complete
            .then_some(ActBody::Bodyless { semicolon: None })
            .map_or(Recovered::Incomplete, Recovered::Complete);
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(act_base, i) else {
        i.rollback(checkpoint);
        if head_and_source_complete && act_body_implicit_boundary_pending(act_base, i) {
            return Recovered::Complete(ActBody::Bodyless { semicolon: None });
        }
        return Recovered::Incomplete;
    };
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        if head_and_source_complete && act_body_implicit_boundary_pending(act_base, i) {
            return Recovered::Complete(ActBody::Bodyless { semicolon: None });
        }
        if act_body_introducer_error_retry_ast(act_base, i).is_some_and(|retry| retry) {
            return parse_act_body_ast(table, act_base, head_and_source_complete, i);
        }
        return Recovered::Incomplete;
    };
    match punctuation.kind() {
        PunctuationKind::Semicolon => Recovered::Complete(ActBody::Bodyless {
            semicolon: Some(punctuation.range()),
        }),
        PunctuationKind::Open(Delimiter::Brace) => Recovered::Complete(ActBody::Braced {
            block: parse_braced_statement_block_expression(table, punctuation.range(), i),
        }),
        PunctuationKind::Colon => Recovered::Complete(ActBody::Colon {
            colon: punctuation.range(),
            body: parse_act_colon_body_ast(table, act_base, i)
                .map_or(Recovered::Incomplete, Recovered::Complete),
        }),
        _ => {
            i.rollback(checkpoint);
            if head_and_source_complete && act_body_implicit_boundary_pending(act_base, i) {
                return Recovered::Complete(ActBody::Bodyless { semicolon: None });
            }
            if act_body_introducer_error_retry_ast(act_base, i).is_some_and(|retry| retry) {
                parse_act_body_ast(table, act_base, head_and_source_complete, i)
            } else {
                Recovered::Incomplete
            }
        }
    }
}

pub(super) fn parse_act_colon_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ActColonBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n']) {
        if i.local.line().line_indent <= act_base {
            i.rollback(checkpoint);
            return None;
        }
        let block_indent = i.local.line().line_indent;
        return Some(ActColonBody::Indented {
            block: parse_indented_act_body(table, trivia, act_base, block_indent, i),
        });
    }
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
        crate::session::InlineStatementOwnerKind::ActColonBody,
    );
    let statement = i
        .run(from_fn(|i| parse_canonical_statement(table, i)))
        .or_else(|| {
            act_body_error_retry_ast(table, i)
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
        ActColonBody::Inline {
            statement: Box::new(statement),
        }
    });
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    body
}

pub(super) fn act_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
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

/// Tests an Act tail without consuming it. Unlike Role's mandatory body,
/// this recognizes the caller-owned boundary that completes tail-nothing.
pub(super) fn act_body_implicit_boundary_pending<E>(act_base: usize, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) || i.input.remainder().is_empty() {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = match mod_trivia(act_base, i) {
        None => i
            .run(scan_trivia)
            .is_some_and(|trivia| i.input.source()[trivia.range()].contains(['\r', '\n'])),
        Some(_) if i.input.remainder().is_empty() => true,
        Some(_) => i.run(scan_punctuation).is_some_and(|punctuation| {
            matches!(
                punctuation.kind(),
                PunctuationKind::Comma
                    | PunctuationKind::Close(
                        Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                    )
            )
        }),
    };
    i.rollback(checkpoint);
    pending
}

pub(super) fn act_colon_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
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
            PunctuationKind::Semicolon
                | PunctuationKind::Comma
                | PunctuationKind::Close(
                    Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                )
        )
    });
    i.rollback(checkpoint);
    pending
}

/// AST half of the one maximal Act body-introducer invalid run. Direct-CST
/// emission is intentionally left to Gate 6; this only preserves the same
/// starter and boundary ownership for the AST adapter.
pub(super) fn act_body_introducer_error_retry_ast<'source, E>(
    act_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if act_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if act_body_implicit_boundary_pending(act_base, i) {
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

pub(super) fn act_body_error_retry_ast<'source, E>(
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
        if act_colon_body_boundary_pending(i) {
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

/// Direct-CST counterpart of [`parse_act_declaration_isolated`]. Gate 10
/// promotes this exact adapter into shared statement dispatch.
pub(crate) fn commit_act_declaration_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ActStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::ActDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::ActKw, intro.act_keyword.range());

    let parsed_head = if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        ActTypeExpressionWithTail {
            value: Recovered::Incomplete,
            tail: None,
        }
    } else {
        commit_required_act_type_expression_with_companion_handoff_isolated(
            ActTypeExpressionSlot::Head,
            intro.act_base,
            committed,
        )
    };
    let head_terminated_incomplete = matches!(parsed_head.value, Recovered::Incomplete);
    let head_derives = if !head_terminated_incomplete {
        committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Act,
                DerivesAttachmentPosition::Header,
                intro.act_base,
                probe.input(),
            )
        })
    } else {
        None
    }
    .map(|start| commit_derives_attachments_with_companion_handoff_isolated(start, committed));
    let head_derives_tail = head_derives.as_ref().and_then(|parsed| parsed.tail);
    let post_head_companion = matches!(
        parsed_head.tail,
        Some(ActDeclarationCompanionTail::PostHead)
    ) || head_derives_tail.is_some();
    if let Some(tail) = head_derives_tail {
        debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Act);
        debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
    }

    if post_head_companion {
        let _ = commit_act_declaration_companion_after_handoff(table, intro.act_base, committed);
    } else {
        let (source, source_tail) =
            commit_act_source_clause_with_companion_handoff(intro.act_base, committed);
        let source_terminated_incomplete = source
            .as_ref()
            .is_some_and(|source| matches!(source.source, Recovered::Incomplete));
        let source_derives = if source
            .as_ref()
            .is_some_and(|source| matches!(source.source, Recovered::Complete(_)))
        {
            committed.probe(|probe| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Act,
                    DerivesAttachmentPosition::Header,
                    intro.act_base,
                    probe.input(),
                )
            })
        } else {
            None
        }
        .map(|start| commit_derives_attachments_with_companion_handoff_isolated(start, committed));
        let source_derives_tail = source_derives.as_ref().and_then(|parsed| parsed.tail);
        let post_source_companion =
            matches!(source_tail, Some(ActDeclarationCompanionTail::PostSource))
                || source_derives_tail.is_some();
        if let Some(tail) = source_derives_tail {
            debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Act);
            debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
        }
        if post_source_companion {
            let _ =
                commit_act_declaration_companion_after_handoff(table, intro.act_base, committed);
        } else {
            let has_actual_braced_close = commit_act_body_isolated(
                table,
                intro.act_base,
                !head_terminated_incomplete && !source_terminated_incomplete,
                committed,
            );
            if has_actual_braced_close
                && let Some(start) = committed.probe(|probe| {
                    recognize_derives_attachment_start(
                        DerivesAttachmentOwner::Act,
                        DerivesAttachmentPosition::Trailing,
                        intro.act_base,
                        probe.input(),
                    )
                })
            {
                let _ = commit_derives_attachments_isolated(start, committed);
            }
        }
    }
    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    Recovered::Complete(intro.start..end)
}

fn parse_act_declaration_companion_after_handoff<'source, E>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DeclarationCompanion<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    mod_trivia(act_base, i).expect("an accepted Act companion handoff preserves its owner gap");
    parse_declaration_companion_isolated(table, act_base, i)
        .expect("an accepted Act companion handoff preserves exact `with`")
}

fn commit_act_declaration_companion_after_handoff<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Range<usize>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = committed
        .probe(|probe| mod_trivia(act_base, probe.input()))
        .expect("an accepted Act companion handoff preserves its owner gap");
    committed.emit_trivia(&leading);
    commit_declaration_companion_isolated(table, act_base, committed)
        .expect("an accepted Act companion handoff preserves exact `with`")
}

#[derive(Clone)]
pub(super) enum ActBodyStarter {
    Bodyless(Range<usize>),
    Braced(Range<usize>),
    Colon(Range<usize>),
}

pub(super) fn commit_act_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
    head_and_source_complete: bool,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        return false;
    }
    let starter = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let starter = mod_trivia(act_base, i).and_then(|trivia| {
            let punctuation = i.run(scan_punctuation)?;
            let starter = match punctuation.kind() {
                PunctuationKind::Semicolon => ActBodyStarter::Bodyless(punctuation.range()),
                PunctuationKind::Open(Delimiter::Brace) => {
                    ActBodyStarter::Braced(punctuation.range())
                }
                PunctuationKind::Colon => ActBodyStarter::Colon(punctuation.range()),
                _ => return None,
            };
            Some((trivia, starter))
        });
        i.rollback(checkpoint);
        starter
    });
    let Some((trivia, starter)) = starter else {
        if head_and_source_complete
            && committed.probe(|probe| act_body_implicit_boundary_pending(act_base, probe.input()))
        {
            // Tail-nothing is a completed body form. It deliberately emits
            // neither a recovery node nor a synthetic semicolon/token.
            return false;
        }
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(act_base, i);
            i.rollback(checkpoint);
            trivia
        });
        let Some(trivia) = trivia else {
            if !head_and_source_complete {
                return false;
            }
            emit_act_body_introducer_missing(committed);
            return false;
        };
        let newline = committed
            .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
        if newline {
            if !head_and_source_complete {
                return false;
            }
            emit_act_body_introducer_missing(committed);
            return false;
        }
        let consumed_trivia = committed
            .probe(|probe| mod_trivia(act_base, probe.input()))
            .expect("the Act body-introducer recovery leaves its leading trivia at the cursor");
        assert_eq!(consumed_trivia.range(), trivia.range());
        committed.emit_trivia(&consumed_trivia);
        match act_body_introducer_error_retry(act_base, committed) {
            Some(true) => {
                return commit_act_body_isolated(
                    table,
                    act_base,
                    head_and_source_complete,
                    committed,
                );
            }
            Some(false) => {}
            None if head_and_source_complete => emit_act_body_introducer_missing(committed),
            None => {}
        }
        return false;
    };

    let consumed_trivia = committed
        .probe(|probe| mod_trivia(act_base, probe.input()))
        .expect("the accepted Act body starter leaves its leading trivia at the cursor");
    assert_eq!(consumed_trivia.range(), trivia.range());
    committed.emit_trivia(&consumed_trivia);
    let punctuation = committed
        .probe(|probe| probe.input().run(scan_punctuation))
        .expect("the accepted Act body starter remains at the cursor");
    match starter {
        ActBodyStarter::Bodyless(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
            false
        }
        ActBodyStarter::Braced(range) => {
            assert_eq!(punctuation.range(), range);
            commit_braced_statement_block_expression(table, range, committed);
            committed_act_body_has_actual_trailing_close(committed)
        }
        ActBodyStarter::Colon(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range);
            commit_act_colon_body_isolated(table, act_base, committed);
            false
        }
    }
}

pub(super) fn committed_act_body_has_actual_trailing_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| {
        let i = probe.input();
        i.pos() > 0 && i.input.source().as_bytes().get(i.pos() - 1) == Some(&b'}')
    })
}

pub(super) fn commit_act_colon_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    act_base: usize,
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
    if newline && committed.probe(|probe| probe.input().local.line().line_indent <= act_base) {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_act_body_missing(committed);
        return;
    }
    if newline {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_act_body(table, trivia, act_base, block_indent, committed);
        return;
    }
    committed.emit_trivia(&trivia);
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::ActColonBody,
            )
    });
    let statement_committed = if commit_canonical_statement(table, LeadingTrivia::None, committed) {
        true
    } else {
        match act_body_error_retry(table, committed) {
            Some(true) => commit_canonical_statement(table, LeadingTrivia::None, committed),
            Some(false) => false,
            None => {
                emit_act_body_missing(committed);
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

pub(super) fn act_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    act_base: usize,
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
            if act_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if act_body_implicit_boundary_pending(act_base, i) {
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
    emit_act_error(
        committed,
        crate::session::ActDeclarationRole::BodyIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        recovered.0,
    );
    Some(recovered.1)
}

pub(super) fn act_body_error_retry<'parse, 'source, 'local, E, O>(
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
                if act_colon_body_boundary_pending(i) {
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
    emit_act_error(
        committed,
        crate::session::ActDeclarationRole::Body,
        ExpectedSyntax::Statement,
        recovered.0,
    );
    Some(recovered.1)
}

/// Emits the one outer-body recovery owned by an accepted Act declaration.
/// A complete Act tail-nothing form never reaches this emitter: it is a
/// successful implicit bodyless form, not a missing body introducer.
pub(super) fn emit_act_body_introducer_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Act(
            crate::session::ActDeclarationRole::BodyIntroducer,
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

pub(super) fn emit_act_body_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_act_missing(
        committed,
        crate::session::ActDeclarationRole::Body,
        ExpectedSyntax::Statement,
    );
}

pub(super) fn emit_act_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    act_role: crate::session::ActDeclarationRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Act(act_role));
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

pub(super) fn emit_act_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    act_role: crate::session::ActDeclarationRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Act(act_role));
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

/// A standalone Act declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition and body
/// parsing remain unreachable until their later dedicated gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ActDeclaration<'source> {
    pub(super) visibility: Visibility,
    pub(super) head: Recovered<Box<TypeExpression<'source>>>,
    pub(super) source: Option<ActSourceClause<'source>>,
    pub(super) derives: Vec<DerivesAttachment<'source>>,
    pub(super) companion: Option<DeclarationCompanion<'source>>,
    pub(super) body: Recovered<ActBody<'source>>,
    pub(super) range: Range<usize>,
}

impl ActDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ActSourceClause<'source> {
    pub(super) equals: Range<usize>,
    pub(super) source: Recovered<Box<TypeExpression<'source>>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ActBody<'source> {
    Bodyless {
        semicolon: Option<Range<usize>>,
    },
    Braced {
        block: BracedStatementBlockExpression<'source>,
    },
    Colon {
        colon: Range<usize>,
        body: Recovered<ActColonBody<'source>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ActColonBody<'source> {
    Inline {
        statement: Box<Statement<'source>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}
