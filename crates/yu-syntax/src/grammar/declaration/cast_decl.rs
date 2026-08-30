use super::*;

/// The sink-free prefix reserved for standalone Cast declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 8 connects it to shared statement dispatch.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CastStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) cast_keyword: WordSpan<'source>,
    pub(super) cast_base: usize,
}

/// Recognizes the sink-free prefix reserved for a standalone Cast declaration.
///
/// This remains deliberately separate from `recognize_statement_intro` until
/// the later dispatch gate. An exact `cast` keyword establishes declaration
/// authority without probing its mandatory Pattern, target, or body.
#[allow(dead_code)]
pub(super) fn recognize_cast_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<CastStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let cast_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(cast_base, &mut i).filter(|trivia| !trivia.is_empty()) else {
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
    if keyword.text() != "cast" {
        i.rollback(checkpoint);
        return None;
    }
    Some(CastStatementIntro {
        start,
        visibility,
        after_visibility,
        cast_keyword: keyword,
        cast_base,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct CastTargetEpisodeSpec {
    pub(super) stops: StopSet,
    pub(super) scoped_frame: TypeExpressionScopedStopFrame,
    pub(super) policy: TypeExpressionEpisodePolicy,
    pub(super) outer_role: GrammarRole,
}

/// The target type sees Cast's form punctuation only for its own outer
/// TypeExpression episode. Recursive TypeExpression owners retain the raw
/// bits, while the scoped frame suspends the Cast authority beneath them.
pub(super) fn cast_target_episode_spec(
    incoming: StopSet,
    current_episode_depth: usize,
    ambient_newline_owner: Option<DeclarationBracedNewlineOwner>,
) -> CastTargetEpisodeSpec {
    let mut stops = incoming.with(StopKind::Equal).with(StopKind::Semicolon);
    let mut scoped_stops = StopSet::default()
        .with(StopKind::Equal)
        .with(StopKind::Semicolon);
    if ambient_newline_owner.is_some() {
        stops = stops.with(StopKind::Newline);
        scoped_stops = scoped_stops.with(StopKind::Newline);
    }
    CastTargetEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy::default(),
        outer_role: GrammarRole::Declaration(DeclarationRole::Cast(CastRole::TargetType)),
    }
}

pub(super) fn parse_required_cast_target_type_isolated<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = cast_target_episode_spec(
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
        declaration_braced_newline_owner_for_physical_newline(i.local),
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
        .expect("the mandatory Cast target type entry is total");
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

pub(super) fn commit_required_cast_target_type_isolated<'parse, 'source, 'local, E, O>(
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
        cast_target_episode_spec(
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
            declaration_braced_newline_owner_for_physical_newline(i.local),
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

pub(super) fn cast_pattern_policy() -> PatternMandatorySlotPolicy {
    PatternMandatorySlotPolicy {
        fresh_primary_recovery_stops: StopSet::default()
            .with(StopKind::Colon)
            .with(StopKind::Equal),
        recovered_primary_tail_stops: StopSet::default().with(StopKind::Colon),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CastPrefixPhase {
    PatternIntroducer,
    PatternClose,
    TargetIntroducer,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CastPrefixTarget {
    OpenPattern,
    Pattern,
    LocalPatternClose,
    OuterPatternClose,
    TargetColon,
    TargetType,
    Form,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CastPrefixInvalidRun {
    pub(super) range: Range<usize>,
    pub(super) target: CastPrefixTarget,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CastPatternHandoff {
    Target,
    Form,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedCastPatternPhase<'source> {
    pub(super) pattern: Recovered<CastPattern<'source>>,
    pub(super) handoff: CastPatternHandoff,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CommittedCastPatternPhase {
    pub(super) pattern: Recovered<Range<usize>>,
    pub(super) handoff: CastPatternHandoff,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CommittedCastPatternValue {
    pub(super) range: Range<usize>,
    pub(super) complete: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum CastTargetHandoff {
    Form,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedCastTargetPhase<'source> {
    pub(super) target: Recovered<CastTarget<'source>>,
    pub(super) handoff: CastTargetHandoff,
}

/// The already-decided Cast prefix shared by Gate 3b's signature fixtures and
/// Gate 4b's form-aware AST adapter.  The boolean preserves whether the
/// prefix lattice established positive form-starter authority without making
/// the form judge re-probe Pattern or TypeExpression decisions.
pub(super) struct ParsedCastSignature<'source> {
    pub(super) visibility: Visibility,
    pub(super) pattern: Recovered<CastPattern<'source>>,
    pub(super) target: Recovered<CastTarget<'source>>,
    pub(super) form_handoff: bool,
}

/// The direct-CST counterpart of [`ParsedCastSignature`].  Keeping the
/// already-decided form handoff out of the direct form judge means the latter
/// never re-probes a Pattern or TypeExpression boundary.
pub(super) struct CommittedCastSignature {
    pub(super) form_handoff: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct CommittedCastTargetPhase {
    pub(super) target: Recovered<Range<usize>>,
    pub(super) handoff: CastTargetHandoff,
}

pub(super) fn cast_target_type_candidate_input<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let errors_checkpoint = i.errors_checkpoint();
    let candidate = i.run(parse_type_expression).is_some();
    i.rollback(checkpoint);
    i.errors_rollback(errors_checkpoint);
    candidate
}

pub(super) fn cast_prefix_outer_boundary_pending<E>(cast_base: usize, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() || any_ambient_owner_claims(i) {
        return true;
    }
    if i.input.remainder().starts_with([',', ']', '}']) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let continues = mod_trivia(cast_base, i).is_some();
    i.rollback(checkpoint);
    !continues
}

pub(super) fn cast_prefix_target<E>(
    phase: CastPrefixPhase,
    cast_base: usize,
    has_local_pattern_frame: bool,
    i: &mut SynIn<E>,
) -> Option<CastPrefixTarget>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if phase == CastPrefixPhase::PatternIntroducer {
        if i.input.remainder().starts_with('(') {
            return Some(CastPrefixTarget::OpenPattern);
        }
        // Composite Pattern NUDs such as `:symbol` outrank Cast's target
        // colon exactly as the neutral fresh-primary policy requires.
        if pattern_nud_candidate_input(i) {
            return Some(CastPrefixTarget::Pattern);
        }
    }
    if phase == CastPrefixPhase::TargetIntroducer && i.input.remainder().starts_with(':') {
        return Some(CastPrefixTarget::TargetColon);
    }
    if i.input.remainder().starts_with(')') {
        return Some(
            if has_local_pattern_frame && i.local.delimiter() == Some(Delimiter::Parenthesis) {
                CastPrefixTarget::LocalPatternClose
            } else {
                CastPrefixTarget::OuterPatternClose
            },
        );
    }
    if i.input.remainder().starts_with(':') {
        return Some(CastPrefixTarget::TargetColon);
    }
    if i.input.remainder().starts_with([';', '=']) {
        return Some(CastPrefixTarget::Form);
    }
    if phase == CastPrefixPhase::TargetIntroducer && cast_target_type_candidate_input(i) {
        return Some(CastPrefixTarget::TargetType);
    }
    cast_prefix_outer_boundary_pending(cast_base, i).then_some(CastPrefixTarget::Boundary)
}

/// Advances one prefix-slot invalid episode but leaves the first actual
/// retry candidate or downstream punctuation untouched. Trivia after the
/// first malformed byte belongs to the same Error range; a caller-owned
/// equal-or-shallower newline remains non-consuming.
pub(super) fn scan_cast_prefix_invalid_run<E>(
    phase: CastPrefixPhase,
    cast_base: usize,
    has_local_pattern_frame: bool,
    i: &mut SynIn<E>,
) -> CastPrefixInvalidRun
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if let Some(target) = cast_prefix_target(phase, cast_base, has_local_pattern_frame, i) {
            return CastPrefixInvalidRun {
                range: start..i.pos(),
                target,
            };
        }
        let trivia_checkpoint = i.checkpoint();
        if let Some(trivia) = i.run(scan_trivia).filter(|trivia| !trivia.is_empty()) {
            debug_assert!(trivia.range().start >= start);
            continue;
        }
        i.rollback(trivia_checkpoint);
        i.input
            .next()
            .expect("a non-boundary Cast invalid byte remains available");
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

pub(super) fn cast_pattern_handoff(target: CastPrefixTarget) -> CastPatternHandoff {
    match target {
        CastPrefixTarget::LocalPatternClose | CastPrefixTarget::TargetColon => {
            CastPatternHandoff::Target
        }
        CastPrefixTarget::Form => CastPatternHandoff::Form,
        CastPrefixTarget::OuterPatternClose | CastPrefixTarget::Boundary => {
            CastPatternHandoff::Boundary
        }
        CastPrefixTarget::OpenPattern
        | CastPrefixTarget::Pattern
        | CastPrefixTarget::TargetType => {
            unreachable!("a completed Cast pattern phase cannot hand off to this target")
        }
    }
}

pub(super) fn emit_cast_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: GrammarRole,
    expected: ExpectedSyntax,
    kind: RecoveryKind,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let unexpected = match kind {
            RecoveryKind::Missing => Arc::from([]),
            RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            kind,
            unexpected,
            Arc::from([SyntaxExpectation {
                role,
                expected,
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    match kind {
        RecoveryKind::Missing => committed.emit_missing(record),
        RecoveryKind::Error => committed.emit_error(record),
    }
}

pub(super) fn emit_cast_slot_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: CastRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let kind = if range.is_empty() {
        RecoveryKind::Missing
    } else {
        RecoveryKind::Error
    };
    emit_cast_recovery(
        committed,
        GrammarRole::Declaration(DeclarationRole::Cast(role)),
        expected,
        kind,
        range,
    );
}

/// `;` and an exact declaration `=` are both positive, Cast-owned evidence
/// for the form slot.  Keep the two alternatives in its one recovery record
/// instead of making a malformed run manufacture two independent misses.
pub(super) fn emit_cast_body_introducer_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let kind = if range.is_empty() {
        RecoveryKind::Missing
    } else {
        RecoveryKind::Error
    };
    let role = GrammarRole::Declaration(DeclarationRole::Cast(CastRole::BodyIntroducer));
    let record = committed.probe(|probe| {
        let i = probe.input();
        let unexpected = match kind {
            RecoveryKind::Missing => Arc::from([]),
            RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
        };
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            kind,
            unexpected,
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
                        crate::session::PunctuationEvidence::Equals,
                    ),
                    range: range.clone(),
                    sources: source,
                },
            ]),
            0,
        )
    });
    match kind {
        RecoveryKind::Missing => committed.emit_missing(record),
        RecoveryKind::Error => committed.emit_error(record),
    }
}

pub(super) fn emit_cast_pattern_close_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let kind = if range.is_empty() {
        RecoveryKind::Missing
    } else {
        RecoveryKind::Error
    };
    emit_cast_recovery(
        committed,
        GrammarRole::ClosingDelimiter {
            owner: ConstructRole::CastPattern,
            delimiter: Delimiter::Parenthesis,
        },
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
            Delimiter::Parenthesis,
        )),
        kind,
        range,
    );
}

pub(super) fn parse_required_cast_pattern_value_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<Pattern<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.run(from_fn(|i| {
        Some(parse_required_pattern_with_outer_missing_role_and_policy(
            table,
            Some(GrammarRole::Declaration(DeclarationRole::Cast(
                CastRole::Pattern,
            ))),
            cast_pattern_policy(),
            i,
        ))
    }))
    .expect("the mandatory Cast pattern entry is total")
}

pub(super) fn commit_required_cast_pattern_value_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CommittedCastPatternValue
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let parsed = commit_direct_pattern_with_outer_missing_role_and_policy(
        table,
        LeadingTrivia::None,
        Some(GrammarRole::Declaration(DeclarationRole::Cast(
            CastRole::Pattern,
        ))),
        cast_pattern_policy(),
        committed,
    );
    CommittedCastPatternValue {
        range: parsed.range(),
        complete: parsed.is_complete(),
    }
}

pub(super) fn parse_cast_pattern_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    cast_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedCastPatternPhase<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading_checkpoint = i.checkpoint();
    if mod_trivia(cast_base, i).is_none() {
        i.rollback(leading_checkpoint);
        return ParsedCastPatternPhase {
            pattern: Recovered::Incomplete,
            handoff: CastPatternHandoff::Boundary,
        };
    }
    let introducer =
        scan_cast_prefix_invalid_run(CastPrefixPhase::PatternIntroducer, cast_base, false, i);
    let has_group_evidence = matches!(
        introducer.target,
        CastPrefixTarget::OpenPattern | CastPrefixTarget::Pattern
    );
    if !has_group_evidence {
        return ParsedCastPatternPhase {
            pattern: Recovered::Incomplete,
            handoff: cast_pattern_handoff(introducer.target),
        };
    }
    let open = if introducer.target == CastPrefixTarget::OpenPattern {
        i.run(from_fn(|mut i| scan_character(&mut i, '(')))
    } else {
        None
    };
    let has_local_frame = open.is_some();
    if has_local_frame {
        let _ = mod_trivia(cast_base, i);
    }
    let value_start = i.pos();
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .with(StopKind::RightParenthesis);
    i.local.push_stop_set(stops);
    if has_local_frame {
        i.local.push_delimiter(Delimiter::Parenthesis);
    }
    let value = parse_required_cast_pattern_value_isolated(table, i);
    let value_complete = matches!(value, Recovered::Complete(_));
    let close_trivia_checkpoint = i.checkpoint();
    if mod_trivia(cast_base, i).is_none() {
        i.rollback(close_trivia_checkpoint);
    }
    let (close, handoff) = if !value_complete {
        let target =
            cast_prefix_target(CastPrefixPhase::PatternClose, cast_base, has_local_frame, i)
                .unwrap_or(CastPrefixTarget::Boundary);
        if target == CastPrefixTarget::LocalPatternClose {
            let close = i
                .run(from_fn(|mut i| scan_character(&mut i, ')')))
                .expect("the inspected Cast-local close remains available");
            (Recovered::Complete(close), CastPatternHandoff::Target)
        } else {
            (Recovered::Incomplete, cast_pattern_handoff(target))
        }
    } else {
        let recovery = scan_cast_prefix_invalid_run(
            CastPrefixPhase::PatternClose,
            cast_base,
            has_local_frame,
            i,
        );
        if recovery.target == CastPrefixTarget::LocalPatternClose {
            let close = i
                .run(from_fn(|mut i| scan_character(&mut i, ')')))
                .expect("the inspected Cast-local close remains available");
            (Recovered::Complete(close), CastPatternHandoff::Target)
        } else {
            (Recovered::Incomplete, cast_pattern_handoff(recovery.target))
        }
    };
    if has_local_frame {
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    }
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    let start = open.as_ref().map_or(value_start, |range| range.start);
    let end = i.pos().max(start);
    ParsedCastPatternPhase {
        pattern: Recovered::Complete(CastPattern {
            open: open.map_or(Recovered::Incomplete, Recovered::Complete),
            value,
            close,
            range: start..end,
        }),
        handoff,
    }
}

pub(super) fn commit_cast_pattern_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    cast_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CommittedCastPatternPhase
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = committed.probe(|probe| mod_trivia(cast_base, probe.input()));
    let Some(leading) = leading else {
        let at = committed.probe(|probe| probe.input().pos());
        emit_cast_slot_recovery(
            committed,
            CastRole::PatternIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
            at..at,
        );
        return CommittedCastPatternPhase {
            pattern: Recovered::Incomplete,
            handoff: CastPatternHandoff::Boundary,
        };
    };
    committed.emit_trivia(&leading);
    let introducer = committed.probe(|probe| {
        scan_cast_prefix_invalid_run(
            CastPrefixPhase::PatternIntroducer,
            cast_base,
            false,
            probe.input(),
        )
    });
    let has_group_evidence = matches!(
        introducer.target,
        CastPrefixTarget::OpenPattern | CastPrefixTarget::Pattern
    );
    if !has_group_evidence {
        emit_cast_slot_recovery(
            committed,
            CastRole::PatternIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
            introducer.range,
        );
        return CommittedCastPatternPhase {
            pattern: Recovered::Incomplete,
            handoff: cast_pattern_handoff(introducer.target),
        };
    }
    committed.start_node(SyntaxKind::CastPattern);
    if introducer.target == CastPrefixTarget::Pattern || !introducer.range.is_empty() {
        emit_cast_slot_recovery(
            committed,
            CastRole::PatternIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
            introducer.range.clone(),
        );
    }
    let open = if introducer.target == CastPrefixTarget::OpenPattern {
        commit_character(committed, '(')
    } else {
        None
    };
    if let Some(open) = &open {
        committed.token(SyntaxKind::LParen, open.clone());
    }
    let has_local_frame = open.is_some();
    if has_local_frame {
        if let Some(trivia) = committed.probe(|probe| mod_trivia(cast_base, probe.input())) {
            committed.emit_trivia(&trivia);
        }
    }
    let value_start = committed.probe(|probe| probe.input().pos());
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .with(StopKind::RightParenthesis)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(stops);
        if has_local_frame {
            i.local.push_delimiter(Delimiter::Parenthesis);
        }
    });
    let value = commit_required_cast_pattern_value_isolated(table, committed);
    if let Some(trivia) = committed.probe(|probe| mod_trivia(cast_base, probe.input())) {
        committed.emit_trivia(&trivia);
    }
    let (close, handoff) = if !value.complete {
        let target = committed.probe(|probe| {
            cast_prefix_target(
                CastPrefixPhase::PatternClose,
                cast_base,
                has_local_frame,
                probe.input(),
            )
            .unwrap_or(CastPrefixTarget::Boundary)
        });
        if target == CastPrefixTarget::LocalPatternClose {
            let close = commit_character(committed, ')')
                .expect("the inspected Cast-local close remains available");
            committed.token(SyntaxKind::RParen, close.clone());
            (Some(close), CastPatternHandoff::Target)
        } else {
            (None, cast_pattern_handoff(target))
        }
    } else {
        let recovery = committed.probe(|probe| {
            scan_cast_prefix_invalid_run(
                CastPrefixPhase::PatternClose,
                cast_base,
                has_local_frame,
                probe.input(),
            )
        });
        if recovery.range.is_empty() && recovery.target == CastPrefixTarget::LocalPatternClose {
            let close = commit_character(committed, ')')
                .expect("the inspected Cast-local close remains available");
            committed.token(SyntaxKind::RParen, close.clone());
            (Some(close), CastPatternHandoff::Target)
        } else {
            emit_cast_pattern_close_recovery(committed, recovery.range);
            if recovery.target == CastPrefixTarget::LocalPatternClose {
                let close = commit_character(committed, ')')
                    .expect("the inspected Cast-local close remains available");
                committed.token(SyntaxKind::RParen, close.clone());
                (Some(close), CastPatternHandoff::Target)
            } else {
                (None, cast_pattern_handoff(recovery.target))
            }
        }
    };
    committed.probe(|probe| {
        let i = probe.input();
        if has_local_frame {
            assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
        }
        assert_eq!(i.local.pop_stop_set(), Some(stops));
    });
    let start = open.as_ref().map_or(value_start, |range| range.start);
    let end = committed.probe(|probe| probe.input().pos()).max(start);
    committed.finish_node();
    let _ = close;
    CommittedCastPatternPhase {
        pattern: Recovered::Complete(start..end),
        handoff,
    }
}

pub(super) fn parse_cast_target_isolated<'source, E>(
    cast_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedCastTargetPhase<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    if mod_trivia(cast_base, i).is_none() {
        i.rollback(checkpoint);
        return ParsedCastTargetPhase {
            target: Recovered::Incomplete,
            handoff: CastTargetHandoff::Boundary,
        };
    }
    let introducer =
        scan_cast_prefix_invalid_run(CastPrefixPhase::TargetIntroducer, cast_base, false, i);
    let has_target_evidence = matches!(
        introducer.target,
        CastPrefixTarget::TargetColon | CastPrefixTarget::TargetType
    );
    if !has_target_evidence {
        return ParsedCastTargetPhase {
            target: Recovered::Incomplete,
            handoff: if introducer.target == CastPrefixTarget::Form {
                CastTargetHandoff::Form
            } else {
                CastTargetHandoff::Boundary
            },
        };
    }
    let colon = if introducer.target == CastPrefixTarget::TargetColon {
        i.run(from_fn(|mut i| scan_character(&mut i, ':')))
    } else {
        None
    };
    if colon.is_some() {
        let _ = mod_trivia(cast_base, i);
    }
    let value_start = i.pos();
    let value = parse_required_cast_target_type_isolated(i);
    let complete = matches!(value, Recovered::Complete(_));
    let start = colon.as_ref().map_or(value_start, |range| range.start);
    let end = i.pos().max(start);
    ParsedCastTargetPhase {
        target: Recovered::Complete(CastTarget {
            colon: colon.map_or(Recovered::Incomplete, Recovered::Complete),
            value,
            range: start..end,
        }),
        handoff: if complete || i.input.remainder().starts_with([';', '=']) {
            CastTargetHandoff::Form
        } else {
            CastTargetHandoff::Boundary
        },
    }
}

pub(super) fn commit_cast_target_isolated<'parse, 'source, 'local, E, O>(
    cast_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CommittedCastTargetPhase
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = committed.probe(|probe| mod_trivia(cast_base, probe.input()));
    let Some(leading) = leading else {
        let at = committed.probe(|probe| probe.input().pos());
        emit_cast_slot_recovery(
            committed,
            CastRole::TargetIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
            at..at,
        );
        return CommittedCastTargetPhase {
            target: Recovered::Incomplete,
            handoff: CastTargetHandoff::Boundary,
        };
    };
    committed.emit_trivia(&leading);
    let introducer = committed.probe(|probe| {
        scan_cast_prefix_invalid_run(
            CastPrefixPhase::TargetIntroducer,
            cast_base,
            false,
            probe.input(),
        )
    });
    let has_target_evidence = matches!(
        introducer.target,
        CastPrefixTarget::TargetColon | CastPrefixTarget::TargetType
    );
    if !has_target_evidence {
        emit_cast_slot_recovery(
            committed,
            CastRole::TargetIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
            introducer.range,
        );
        return CommittedCastTargetPhase {
            target: Recovered::Incomplete,
            handoff: if introducer.target == CastPrefixTarget::Form {
                CastTargetHandoff::Form
            } else {
                CastTargetHandoff::Boundary
            },
        };
    }
    committed.start_node(SyntaxKind::CastTarget);
    if introducer.target == CastPrefixTarget::TargetType || !introducer.range.is_empty() {
        emit_cast_slot_recovery(
            committed,
            CastRole::TargetIntroducer,
            ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
            introducer.range.clone(),
        );
    }
    let colon = if introducer.target == CastPrefixTarget::TargetColon {
        commit_character(committed, ':')
    } else {
        None
    };
    if let Some(colon) = &colon {
        committed.token(SyntaxKind::Colon, colon.clone());
    }
    if colon.is_some() {
        if let Some(trivia) = committed.probe(|probe| mod_trivia(cast_base, probe.input())) {
            committed.emit_trivia(&trivia);
        }
    }
    let value_start = committed.probe(|probe| probe.input().pos());
    let value = commit_required_cast_target_type_isolated(committed);
    let complete = matches!(value, Recovered::Complete(_));
    let start = colon.as_ref().map_or(value_start, |range| range.start);
    let end = committed.probe(|probe| probe.input().pos()).max(start);
    committed.finish_node();
    CommittedCastTargetPhase {
        target: Recovered::Complete(start..end),
        handoff: if complete
            || committed.probe(|probe| probe.input().input.remainder().starts_with([';', '=']))
        {
            CastTargetHandoff::Form
        } else {
            CastTargetHandoff::Boundary
        },
    }
}

pub(super) fn parse_cast_signature_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<CastDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let intro = i.run(recognize_cast_statement_intro)?;
    let signature = parse_cast_signature_after_intro_isolated(table, &intro, &mut i);
    let declaration = CastDeclaration {
        visibility: signature.visibility,
        pattern: signature.pattern,
        target: signature.target,
        form: Recovered::Incomplete,
        range: intro.start..i.pos(),
    };
    i.errors_rollback(errors_checkpoint);
    Some(declaration)
}

/// Gate 3b's Pattern/Target prefix composition, kept separate from the
/// declaration form so later consumers never duplicate its handoff logic.
pub(super) fn parse_cast_signature_after_intro_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    intro: &CastStatementIntro<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedCastSignature<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let visibility = intro
        .visibility
        .as_ref()
        .map_or(Visibility::Private, |prefix| prefix.visibility);
    let pattern = parse_cast_pattern_isolated(table, intro.cast_base, i);
    let (target, form_handoff) = match pattern.handoff {
        CastPatternHandoff::Target => {
            let target = parse_cast_target_isolated(intro.cast_base, i);
            (target.target, target.handoff == CastTargetHandoff::Form)
        }
        CastPatternHandoff::Form => (Recovered::Incomplete, true),
        CastPatternHandoff::Boundary => (Recovered::Incomplete, false),
    };
    ParsedCastSignature {
        visibility,
        pattern: pattern.pattern,
        target,
        form_handoff,
    }
}

/// Gate 4b's isolated, form-aware Cast AST adapter.  It deliberately builds
/// no CST and remains unreachable from real statement dispatch until Gate 8.
pub(crate) fn parse_cast_declaration_form_aware_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<CastDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let intro = i.run(recognize_cast_statement_intro)?;
    let signature = parse_cast_signature_after_intro_isolated(table, &intro, &mut i);
    let form = signature
        .form_handoff
        .then(|| parse_cast_form_isolated(table, intro.cast_base, &mut i))
        .unwrap_or(Recovered::Incomplete);
    let declaration = CastDeclaration {
        visibility: signature.visibility,
        pattern: signature.pattern,
        target: signature.target,
        form,
        range: intro.start..i.pos(),
    };
    i.errors_rollback(errors_checkpoint);
    Some(declaration)
}

/// Selects the only two standalone Cast forms.  The post-equals body uses the
/// neutral Binding-style layout decision but supplies Cast-owned AST builders.
pub(super) fn parse_cast_form_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    cast_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<CastForm<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(cast_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    };
    if let Some(semicolon) = i.run(scan_punctuation).and_then(|punctuation| {
        (punctuation.kind() == PunctuationKind::Semicolon).then_some(punctuation.range())
    }) {
        return Recovered::Complete(CastForm::Bodyless { semicolon });
    }

    i.rollback(checkpoint.clone());
    let Some(_) = mod_trivia(cast_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    };
    let Some(equals) = i.run(scan_declaration_exact_equals) else {
        i.rollback(checkpoint);
        return cast_body_introducer_error_retry_ast(i)
            .filter(|retry| *retry)
            .map_or(Recovered::Incomplete, |_| {
                parse_cast_form_isolated(table, cast_base, i)
            });
    };
    let body = parse_binding_style_body(
        cast_base,
        |_trivia, i| {
            i.run(from_fn(|i| parse_expression_with_operators(table, i)))
                .or_else(|| {
                    cast_inline_body_error_retry_ast(table, i)
                        .is_some_and(|retry| retry)
                        .then(|| i.run(from_fn(|i| parse_expression_with_operators(table, i))))
                        .flatten()
                })
                .map(|expression| CastBody::Inline { expression })
        },
        |trivia, block_indent, i| CastBody::Indented {
            block: parse_indented_cast_body(table, trivia, cast_base, block_indent, i),
        },
        i,
    )
    .map_or(Recovered::Incomplete, Recovered::Complete);
    let end = match &body {
        Recovered::Complete(CastBody::Inline { expression }) => expression.range().end,
        Recovered::Complete(CastBody::Indented { block }) => block.range().end,
        Recovered::Incomplete => equals.end,
    };
    Recovered::Complete(CastForm::Definition {
        equals: equals.clone(),
        body,
        range: equals.start..end,
    })
}

pub(super) fn commit_cast_signature_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    intro: CastStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::CastDeclaration);
    let _ = commit_cast_signature_after_intro_isolated(table, &intro, committed);
    let end = committed.probe(|probe| probe.input().pos());
    committed.finish_node();
    committed.probe(|probe| {
        probe.input().errors_rollback(errors_checkpoint);
    });
    Recovered::Complete(intro.start..end)
}

/// Emits Gate 3b's already-decided Cast prefix without choosing its form.
/// Both the prefix-only fixture harness and Gate 5's full declaration adapter
/// call this one continuation so their Pattern/Target ownership stays exact.
pub(super) fn commit_cast_signature_after_intro_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    intro: &CastStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CommittedCastSignature
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::CastKw, intro.cast_keyword.range());
    let pattern = commit_cast_pattern_isolated(table, intro.cast_base, committed);
    let form_handoff = match pattern.handoff {
        CastPatternHandoff::Target => {
            commit_cast_target_isolated(intro.cast_base, committed).handoff
                == CastTargetHandoff::Form
        }
        CastPatternHandoff::Form => true,
        CastPatternHandoff::Boundary => false,
    };
    CommittedCastSignature { form_handoff }
}

/// Gate 5's direct-CST form judge.  It shares the Binding-style body layout
/// decision but owns CastBody emission and Cast-specific recovery identity.
pub(super) fn commit_cast_form_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    cast_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        return Recovered::Incomplete;
    }

    let bodyless = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let semicolon = mod_trivia(cast_base, i)
            .and_then(|_| i.run(scan_punctuation))
            .filter(|punctuation| punctuation.kind() == PunctuationKind::Semicolon)
            .map(|punctuation| punctuation.range());
        i.rollback(checkpoint);
        semicolon
    });
    if bodyless.is_some() {
        let trivia = committed
            .probe(|probe| mod_trivia(cast_base, probe.input()))
            .expect("the committed bodyless Cast trivia was already classified");
        committed.emit_trivia(&trivia);
        let semicolon = commit_character(committed, ';')
            .expect("the committed bodyless Cast semicolon was already classified");
        committed.token(SyntaxKind::Semicolon, semicolon.clone());
        return Recovered::Complete(semicolon.clone());
    }

    let equals = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let equals = mod_trivia(cast_base, i).and_then(|_| i.run(scan_declaration_exact_equals));
        i.rollback(checkpoint);
        equals
    });
    if equals.is_none() {
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(cast_base, i);
            i.rollback(checkpoint);
            trivia
        });
        let Some(trivia) = trivia else {
            let at = committed.probe(|probe| probe.input().pos());
            emit_cast_body_introducer_recovery(committed, at..at);
            return Recovered::Incomplete;
        };
        let newline = committed
            .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
        if newline {
            let at = committed.probe(|probe| probe.input().pos());
            emit_cast_body_introducer_recovery(committed, at..at);
            return Recovered::Incomplete;
        }
        let consumed_trivia = committed
            .probe(|probe| mod_trivia(cast_base, probe.input()))
            .expect("the Cast form recovery leaves its trivia at the cursor");
        assert_eq!(consumed_trivia.range(), trivia.range());
        committed.emit_trivia(&consumed_trivia);
        return match cast_body_introducer_error_retry(committed) {
            Some(true) => commit_cast_form_isolated(table, cast_base, committed),
            Some(false) => Recovered::Incomplete,
            None => {
                let at = committed.probe(|probe| probe.input().pos());
                emit_cast_body_introducer_recovery(committed, at..at);
                Recovered::Incomplete
            }
        };
    }
    let trivia = committed
        .probe(|probe| mod_trivia(cast_base, probe.input()))
        .expect("the committed Cast definition trivia was already classified");
    committed.emit_trivia(&trivia);
    let equals = committed
        .probe(|probe| probe.input().run(scan_declaration_exact_equals))
        .expect("the committed Cast definition equals was already classified");
    committed.token(SyntaxKind::Equals, equals.clone());

    let body_start = committed.probe(|probe| probe.input().pos());
    committed.start_node(SyntaxKind::CastBody);
    let body = commit_binding_style_body(
        table,
        cast_base,
        GrammarRole::Declaration(DeclarationRole::Cast(CastRole::Body)),
        |expression| expression.range(),
        |opening_trivia, block_indent, committed| {
            commit_indented_cast_body(table, opening_trivia, cast_base, block_indent, committed);
            body_start..committed.probe(|probe| probe.input().pos())
        },
        |committed| cast_inline_body_error_retry(table, committed),
        committed,
    );
    committed.finish_node();
    let end = match body {
        Recovered::Complete(range) => range.end,
        Recovered::Incomplete => equals.end,
    };
    Recovered::Complete(equals.start..end)
}

pub(super) fn cast_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i
        .run(scan_punctuation)
        .is_some_and(|punctuation| punctuation.kind() == PunctuationKind::Semicolon)
        || i.run(scan_declaration_exact_equals).is_some();
    i.rollback(checkpoint);
    pending
}

/// A Cast form has no authority over a following declaration, caller close,
/// or target colon.  Those are safe points for the one BodyIntroducer error
/// episode and remain unconsumed for their real owner.
pub(super) fn cast_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
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
                | PunctuationKind::Colon
        )
    });
    i.rollback(checkpoint);
    pending
}

/// AST half of the BodyIntroducer recovery lattice.  Direct CST realizes the
/// matching typed Error below; both leave the discovered starter/boundary in
/// place for the same-slot retry or its outer owner.
pub(super) fn cast_body_introducer_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if cast_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if cast_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return (start < i.pos()).then_some(false);
        };
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        let operator_run = declaration_operator_character(character);
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if operator_run {
            while i
                .input
                .remainder()
                .chars()
                .next()
                .is_some_and(declaration_operator_character)
            {
                i.input.next()?;
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            continue;
        }
    }
}

pub(super) fn cast_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
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
            if cast_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if cast_body_boundary_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < i.pos()).then_some((start..i.pos(), false));
            };
            if matches!(character, '\r' | '\n') {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let operator_run = declaration_operator_character(character);
            i.input.next()?;
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            if operator_run {
                while i
                    .input
                    .remainder()
                    .chars()
                    .next()
                    .is_some_and(declaration_operator_character)
                {
                    i.input.next()?;
                    let mut line = i.local.line();
                    line.at_line_start = false;
                    i.local.set_line(line);
                }
                continue;
            }
        }
    })?;
    emit_cast_body_introducer_recovery(committed, recovered.0);
    Some(recovered.1)
}

pub(super) fn cast_inline_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
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

pub(super) fn cast_inline_body_error_retry_ast<'source, E>(
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
        if cast_inline_body_boundary_pending(i) {
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
            .run(from_fn(|i| parse_expression_with_operators(table, i)))
            .is_some();
        i.rollback(checkpoint);
        if candidate {
            return Some(true);
        }
    }
}

pub(super) fn cast_inline_body_error_retry<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> BindingStyleInlineRecovery
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
                if cast_inline_body_boundary_pending(i) {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                let Some(character) = i.input.remainder().chars().next() else {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                };
                if matches!(character, '\r' | '\n') {
                    return (start < i.pos()).then_some((start..i.pos(), false));
                }
                i.input.next()?;
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            if crate::grammar::expression::direct_expression_nud_candidate(
                table,
                LeadingTrivia::None,
                probe,
            ) {
                let end = probe.input().pos();
                return Some((start..end, true));
            }
        }
    });
    let Some((range, retry)) = recovered else {
        return BindingStyleInlineRecovery::None;
    };
    emit_cast_slot_recovery(committed, CastRole::Body, ExpectedSyntax::Expression, range);
    if retry {
        BindingStyleInlineRecovery::Retry
    } else {
        BindingStyleInlineRecovery::TerminalError
    }
}

/// Gate 5's full direct-CST isolated adapter.  It stays deliberately outside
/// real statement dispatch until the Gate 8 atomic promotion.
pub(crate) fn commit_cast_declaration_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    intro: CastStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::CastDeclaration);
    let signature = commit_cast_signature_after_intro_isolated(table, &intro, committed);
    if signature.form_handoff {
        let _ = commit_cast_form_isolated(table, intro.cast_base, committed);
    }
    let end = committed.probe(|probe| probe.input().pos());
    committed.finish_node();
    committed.probe(|probe| {
        probe.input().errors_rollback(errors_checkpoint);
    });
    Recovered::Complete(intro.start..end)
}

/// A standalone Cast declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition and body
/// parsing remain unreachable until their later dedicated gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CastDeclaration<'source> {
    pub(super) visibility: Visibility,
    pub(super) pattern: Recovered<CastPattern<'source>>,
    pub(super) target: Recovered<CastTarget<'source>>,
    pub(super) form: Recovered<CastForm<'source>>,
    pub(super) range: Range<usize>,
}

impl CastDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CastPattern<'source> {
    pub(super) open: Recovered<Range<usize>>,
    pub(super) value: Recovered<Box<Pattern<'source>>>,
    pub(super) close: Recovered<Range<usize>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct CastTarget<'source> {
    pub(super) colon: Recovered<Range<usize>>,
    pub(super) value: Recovered<Box<TypeExpression<'source>>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CastForm<'source> {
    Bodyless {
        semicolon: Range<usize>,
    },
    Definition {
        equals: Range<usize>,
        body: Recovered<CastBody<'source>>,
        range: Range<usize>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum CastBody<'source> {
    Inline {
        expression: OperatorChain<'source>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}
