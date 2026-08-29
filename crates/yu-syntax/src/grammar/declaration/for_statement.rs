use super::*;

/// The sink-free prefix reserved for standalone For statements.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 9 connects it to shared statement dispatch.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ForStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) for_keyword: WordSpan<'source>,
    pub(super) for_base: usize,
}

/// Recognizes the sink-free prefix reserved for a standalone For statement.
///
/// For has no visibility form: only a bare exact maximal `for` establishes
/// its continuation authority.
pub(super) fn recognize_for_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ForStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let Some(for_keyword) = i.run(scan_word) else {
        i.rollback(checkpoint);
        return None;
    };
    if for_keyword.text() != "for" {
        i.rollback(checkpoint);
        return None;
    }
    let for_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    Some(ForStatementIntro {
        start,
        for_keyword,
        for_base,
    })
}

/// Probes For's optional label without claiming a sigil Pattern.
///
/// Unlike case/catch, For leaves the composite available to Pattern when its
/// next significant token is exact `in`, absent, or already caller-owned.
#[allow(dead_code)]
pub(super) fn probe_for_label<'source, E>(
    for_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ForLabel<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let range = probe_apostrophe_sigil_word(i)?;
    let after_composite = i.checkpoint();
    let following = mod_trivia(for_base, i).is_some()
        && !i.input.remainder().is_empty()
        && !any_ambient_owner_claims(i)
        && !for_label_outer_boundary_pending(i);
    let exact_in = i.run(scan_word).is_some_and(|word| word.text() == "in");
    i.rollback(after_composite);
    if !following || exact_in {
        i.rollback(checkpoint);
        return None;
    }
    Some(ForLabel {
        text: &i.input.source()[range.clone()],
        range,
    })
}

/// Tests only punctuation that an active caller has already made a boundary.
/// Other punctuation remains a significant token for For's label lookahead.
pub(super) fn for_label_outer_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        let stop = match punctuation.kind() {
            PunctuationKind::Comma => StopKind::Comma,
            PunctuationKind::Close(Delimiter::Parenthesis) => StopKind::RightParenthesis,
            PunctuationKind::Close(Delimiter::Bracket) => StopKind::RightBracket,
            PunctuationKind::Close(Delimiter::Brace) => StopKind::RightBrace,
            _ => return false,
        };
        i.local.stop_set().is_some_and(|stops| stops.contains(stop))
    });
    i.rollback(checkpoint);
    pending
}

/// The mandatory Pattern slot used by For's isolated header phase.
///
/// The frame carries For's word boundary through canonical Pattern and its
/// annotation TypeExpression.  Punctuation belongs only to fresh-primary
/// recovery policy so a completed Pattern can still own its annotation colon.
pub(super) fn for_pattern_stops<E>(i: &SynIn<E>) -> StopSet
where
    E: ErrorSink<usize>,
{
    i.local.stop_set().unwrap_or_default().with(StopKind::In)
}

pub(super) fn for_pattern_policy() -> PatternMandatorySlotPolicy {
    PatternMandatorySlotPolicy {
        fresh_primary_recovery_stops: StopSet::default()
            .with(StopKind::Colon)
            .with(StopKind::LeftBrace)
            .with(StopKind::In),
        ..PatternMandatorySlotPolicy::default()
    }
}

pub(super) fn parse_required_for_pattern_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<Pattern<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = for_pattern_stops(i);
    i.local.push_stop_set(stops);
    let pattern = i
        .run(from_fn(|i| {
            Some(parse_required_pattern_with_outer_missing_role_and_policy(
                table,
                Some(GrammarRole::ForStatement(ForStatementRole::Pattern)),
                for_pattern_policy(),
                i,
            ))
        }))
        .expect("the mandatory For Pattern entry is total");
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    pattern
}

pub(super) fn commit_required_for_pattern_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParsedPattern<O::Checkpoint>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = committed.probe(|probe| for_pattern_stops(probe.input()));
    committed.probe(|probe| probe.input().local.push_stop_set(stops));
    let pattern = commit_direct_pattern_with_outer_missing_role_and_policy(
        table,
        LeadingTrivia::None,
        Some(GrammarRole::ForStatement(ForStatementRole::Pattern)),
        for_pattern_policy(),
        committed,
    );
    committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops)));
    pattern
}

/// Parses the isolated For header tail after Gate 4's Pattern slot.
///
/// This deliberately does not compose Pattern with the tail yet: the later
/// header adapter owns that assembly.  The tail nevertheless keeps the two
/// slots together because a missing `in` at a header boundary is the single
/// cause that makes the iterable incomplete too.
pub(super) fn parse_for_in_and_iterable_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (Recovered<Range<usize>>, Recovered<OperatorChain<'source>>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let _ = i.run(scan_trivia).expect("trivia scanning is total");
    let in_keyword = for_exact_in(i);
    if in_keyword.is_none() && for_header_truncation_pending(i) {
        return (Recovered::Incomplete, Recovered::Incomplete);
    }
    let iterable = parse_for_iterable_isolated(table, i);
    (
        in_keyword.map_or(Recovered::Incomplete, |word| {
            Recovered::Complete(word.range())
        }),
        iterable,
    )
}

pub(super) fn parse_for_iterable_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<OperatorChain<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .with(StopKind::Colon)
        .with(StopKind::LeftBrace);
    i.local.push_stop_set(stops);
    let _ = i.run(scan_trivia).expect("trivia scanning is total");
    let mut iterable = (!for_iterable_primary_stop_pending(i))
        .then(|| i.run(from_fn(|i| parse_expression_with_operators(table, i))))
        .flatten();
    if iterable.is_none() && for_iterable_error_retry_ast(table, i) {
        iterable = i.run(from_fn(|i| parse_expression_with_operators(table, i)));
    }
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    iterable.map_or(Recovered::Incomplete, Recovered::Complete)
}

pub(super) fn for_iterable_error_retry_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if for_iterable_primary_stop_pending(i) {
            return false;
        }
        let Some(character) = i.input.remainder().chars().next() else {
            return false;
        };
        if matches!(character, '\r' | '\n' | ';') {
            return false;
        }
        i.input.next();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        let checkpoint = i.checkpoint();
        let errors_checkpoint = i.errors_checkpoint();
        let candidate = i
            .run(from_fn(|i| parse_expression_with_operators(table, i)))
            .is_some();
        i.rollback(checkpoint);
        i.errors_rollback(errors_checkpoint);
        if candidate {
            return start < i.pos();
        }
    }
}

pub(super) fn commit_for_in_and_iterable_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> (
    Recovered<Range<usize>>,
    Recovered<ParsedExpression<O::Checkpoint>>,
)
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = committed.probe(|probe| {
        probe
            .input()
            .run(scan_trivia)
            .expect("trivia scanning is total")
    });
    committed.emit_trivia(&trivia);
    let in_keyword = committed.probe(|probe| for_exact_in(probe.input()));
    if let Some(word) = in_keyword {
        committed.token(SyntaxKind::InKw, word.range());
    } else {
        emit_for_missing(
            committed,
            ForStatementRole::InKeyword,
            ExpectedSyntax::Expression,
        );
        if committed.probe(|probe| for_header_truncation_pending(probe.input())) {
            return (Recovered::Incomplete, Recovered::Incomplete);
        }
    }
    let iterable = commit_for_iterable_isolated(table, committed);
    (
        in_keyword.map_or(Recovered::Incomplete, |word| {
            Recovered::Complete(word.range())
        }),
        iterable,
    )
}

pub(super) fn commit_for_iterable_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<ParsedExpression<O::Checkpoint>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .with(StopKind::Colon)
            .with(StopKind::LeftBrace)
    });
    committed.probe(|probe| probe.input().local.push_stop_set(stops));
    committed.start_node(SyntaxKind::ForIterable);
    let trivia = committed.probe(|probe| {
        probe
            .input()
            .run(scan_trivia)
            .expect("trivia scanning is total")
    });
    let leading = (!trivia.is_empty())
        .then_some(LeadingTrivia::Present)
        .unwrap_or(LeadingTrivia::None);
    committed.emit_trivia(&trivia);
    let primary_stop = committed.probe(|probe| for_iterable_primary_stop_pending(probe.input()));
    let mut iterable = (!primary_stop)
        .then(|| parse_direct_expression_with_operators(table, leading, committed))
        .flatten();
    if !primary_stop
        && iterable.is_none()
        && direct_expression_error_retry(
            table,
            GrammarRole::Expression(crate::session::ExpressionRole::Nud),
            committed,
        )
    {
        iterable = parse_direct_expression_with_operators(table, LeadingTrivia::None, committed);
    }
    if iterable.is_none() {
        emit_for_missing(
            committed,
            ForStatementRole::Iterable,
            ExpectedSyntax::Expression,
        );
    }
    committed.finish_node();
    committed.probe(|probe| assert_eq!(probe.input().local.pop_stop_set(), Some(stops)));
    iterable.map_or(Recovered::Incomplete, Recovered::Complete)
}

/// A body starter or caller boundary immediately after Pattern has the one
/// shared absence cause covered by FOR-R's truncation rule.
pub(super) fn for_header_truncation_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() || any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Colon | PunctuationKind::Open(Delimiter::Brace)
        )
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn for_exact_in<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<WordSpan<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let word = i.run(scan_word)?;
    if word.text() == "in" {
        Some(word)
    } else {
        i.rollback(checkpoint);
        None
    }
}

pub(super) fn for_iterable_primary_stop_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Colon | PunctuationKind::Open(Delimiter::Brace)
        )
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn emit_for_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ForStatementRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ForStatement(role);
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

pub(super) fn emit_for_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ForStatementRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::ForStatement(role);
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
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

/// Parses one accepted For continuation. The body adapter owns only For's
/// local punctuation and returns every outer separator and boundary untouched.
pub(crate) fn parse_for_statement_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ForStatement<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let statement = (|| {
        let intro = i.run(recognize_for_statement_intro)?;
        let Some(_) = for_continuation_trivia(intro.for_base, &mut i) else {
            return Some(ForStatement {
                label: None,
                pattern: Recovered::Incomplete,
                in_keyword: Recovered::Incomplete,
                iterable: Recovered::Incomplete,
                body: Recovered::Incomplete,
                range: intro.start..i.pos(),
            });
        };
        let label = probe_for_label(intro.for_base, &mut i);
        if label.is_some() {
            let _ = for_continuation_trivia(intro.for_base, &mut i)
                .expect("an accepted For label has a following continuation gap");
        }
        let pattern = parse_required_for_pattern_isolated(table, &mut i);
        let header_truncated =
            matches!(pattern, Recovered::Incomplete) && for_header_truncation_pending(&mut i);
        let (in_keyword, iterable) = if header_truncated {
            (Recovered::Incomplete, Recovered::Incomplete)
        } else {
            parse_for_in_and_iterable_isolated(table, &mut i)
        };
        let body = if matches!(iterable, Recovered::Complete(_))
            || for_body_starter_after_gap_pending(intro.for_base, &mut i)
        {
            parse_for_body_isolated(table, intro.for_base, &mut i)
        } else {
            Recovered::Incomplete
        };
        let end = i.pos();
        Some(ForStatement {
            label,
            pattern,
            in_keyword,
            iterable,
            body,
            range: intro.start..end,
        })
    })();
    i.errors_rollback(errors_checkpoint);
    statement
}

pub(super) fn parse_for_body_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    for_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<ForBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let checkpoint = i.checkpoint();
    let Some(_) = for_continuation_trivia(for_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    };
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        if for_body_introducer_error_retry_ast(for_base, i).is_some_and(|retry| retry) {
            return parse_for_body_isolated(table, for_base, i);
        }
        return Recovered::Incomplete;
    };
    match punctuation.kind() {
        PunctuationKind::Open(Delimiter::Brace) => Recovered::Complete(ForBody::Braced {
            block: parse_braced_statement_block_expression(table, punctuation.range(), i),
        }),
        PunctuationKind::Colon => {
            let colon = punctuation.range();
            let body = match recognize_introduced_body_layout(for_base, i) {
                IntroducedBodyLayout::Inline { .. } => i
                    .run(from_fn(|i| parse_expression_with_operators(table, i)))
                    .map(|expression| ForColonBody::Inline { expression })
                    .map_or(Recovered::Incomplete, Recovered::Complete),
                IntroducedBodyLayout::Indented {
                    opening_trivia,
                    block_indent,
                } => Recovered::Complete(ForColonBody::Indented {
                    block: parse_indented_for_body(
                        table,
                        opening_trivia,
                        for_base,
                        block_indent,
                        i,
                    ),
                }),
                IntroducedBodyLayout::WrongIndent => Recovered::Incomplete,
            };
            Recovered::Complete(ForBody::Colon { colon, body })
        }
        _ => {
            i.rollback(checkpoint);
            if for_body_introducer_error_retry_ast(for_base, i).is_some_and(|retry| retry) {
                return parse_for_body_isolated(table, for_base, i);
            }
            Recovered::Incomplete
        }
    }
}

/// Direct-CST counterpart of [`parse_for_statement_isolated`].
pub(crate) fn commit_for_statement_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ForStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::ForStatement);
    committed.token(SyntaxKind::ForKw, intro.for_keyword.range());
    let header_gap =
        committed.probe(|probe| for_continuation_trivia(intro.for_base, probe.input()));
    let Some(header_gap) = header_gap else {
        emit_for_missing(
            committed,
            ForStatementRole::Pattern,
            ExpectedSyntax::Expression,
        );
        let end = committed_position(committed);
        committed.finish_node();
        committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
        return Recovered::Complete(intro.start..end);
    };
    committed.emit_trivia(&header_gap);
    let label = committed.probe(|probe| probe_for_label(intro.for_base, probe.input()));
    if let Some(label) = label {
        committed.start_node(SyntaxKind::ForLabel);
        committed.token(SyntaxKind::SigilIdentifier, label.range.clone());
        committed.finish_node();
        let gap = committed
            .probe(|probe| for_continuation_trivia(intro.for_base, probe.input()))
            .expect("an accepted For label has a following continuation gap");
        committed.emit_trivia(&gap);
    }
    let pattern = commit_required_for_pattern_isolated(table, committed);
    let header_truncated = !pattern.is_complete()
        && committed.probe(|probe| for_header_truncation_pending(probe.input()));
    if header_truncated {
        if committed
            .probe(|probe| for_body_starter_after_gap_pending(intro.for_base, probe.input()))
        {
            commit_for_body_isolated(table, intro.for_base, committed);
        }
    } else {
        let (_, iterable) = commit_for_in_and_iterable_isolated(table, committed);
        if matches!(iterable, Recovered::Complete(_))
            || committed
                .probe(|probe| for_body_starter_after_gap_pending(intro.for_base, probe.input()))
        {
            commit_for_body_isolated(table, intro.for_base, committed);
        }
    }
    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    Recovered::Complete(intro.start..end)
}

pub(super) fn commit_for_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    for_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let starter = committed.probe(|probe| {
        let i = probe.input();
        if any_ambient_owner_claims(i) {
            return None;
        }
        let checkpoint = i.checkpoint();
        let starter = for_continuation_trivia(for_base, i).and_then(|trivia| {
            let punctuation = i.run(scan_punctuation)?;
            matches!(
                punctuation.kind(),
                PunctuationKind::Colon | PunctuationKind::Open(Delimiter::Brace)
            )
            .then_some((trivia, punctuation))
        });
        i.rollback(checkpoint);
        starter
    });
    let Some((trivia, starter)) = starter else {
        let recovered = for_body_introducer_error_retry(committed, for_base);
        if matches!(recovered, Some(true)) {
            commit_for_body_isolated(table, for_base, committed);
            return;
        }
        if !committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            emit_for_missing(
                committed,
                ForStatementRole::BodyIntroducer,
                ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
            );
        }
        return;
    };
    let gap = committed
        .probe(|probe| for_continuation_trivia(for_base, probe.input()))
        .expect("the accepted For body starter leaves its leading gap at the cursor");
    assert_eq!(gap.range(), trivia.range());
    committed.emit_trivia(&gap);
    let punctuation = committed
        .probe(|probe| probe.input().run(scan_punctuation))
        .expect("the accepted For body starter remains at the cursor");
    assert_eq!(punctuation.range(), starter.range());
    match punctuation.kind() {
        PunctuationKind::Open(Delimiter::Brace) => {
            commit_braced_statement_block_expression(table, punctuation.range(), committed);
        }
        PunctuationKind::Colon => {
            committed.token(SyntaxKind::Colon, punctuation.range());
            commit_for_colon_body_isolated(table, for_base, committed);
        }
        _ => unreachable!("For body starter was classified from colon or brace only"),
    }
}

/// Skips one malformed For body-introducer run without taking ownership of a
/// later body starter or caller boundary.  The direct path records that run as
/// the sole For-specific error, then retries the body judge at the starter.
pub(super) fn for_body_introducer_error_retry_ast<'source, E>(
    _for_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    loop {
        if for_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if for_body_boundary_pending(i) {
            return (start < i.pos()).then_some(false);
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            i.rollback(checkpoint);
            return None;
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

pub(super) fn for_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Colon | PunctuationKind::Open(Delimiter::Brace)
        )
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn for_body_starter_after_gap_pending<E>(for_base: usize, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = for_continuation_trivia(for_base, i).is_some() && for_body_starter_pending(i);
    i.rollback(checkpoint);
    pending
}

pub(super) fn for_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) || i.input.remainder().is_empty() {
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

pub(super) fn for_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    _for_base: usize,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let start = i.pos();
        loop {
            if for_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if for_body_boundary_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), false));
            }
            let character = i.input.remainder().chars().next()?;
            if matches!(character, '\r' | '\n') {
                i.rollback(checkpoint);
                return None;
            }
            i.input.next()?;
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
        }
    })?;
    emit_for_error(
        committed,
        ForStatementRole::BodyIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        recovered.0,
    );
    Some(recovered.1)
}

pub(super) fn commit_for_colon_body_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    for_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    match committed.probe(|probe| recognize_introduced_body_layout(for_base, probe.input())) {
        IntroducedBodyLayout::Inline { trivia } => {
            committed.emit_trivia(&trivia);
            let leading = (!trivia.is_empty())
                .then_some(LeadingTrivia::Present)
                .unwrap_or(LeadingTrivia::None);
            if parse_direct_expression_with_operators(table, leading, committed).is_none() {
                emit_for_missing(
                    committed,
                    ForStatementRole::Body,
                    ExpectedSyntax::Expression,
                );
            }
        }
        IntroducedBodyLayout::Indented {
            opening_trivia,
            block_indent,
        } => commit_indented_for_body(table, opening_trivia, for_base, block_indent, committed),
        IntroducedBodyLayout::WrongIndent => {
            emit_for_missing(committed, ForStatementRole::Body, ExpectedSyntax::Statement);
        }
    }
}

pub(super) fn for_continuation_trivia<E>(for_base: usize, i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    mod_trivia(for_base, i)
}

/// A standalone For statement shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition and body
/// parsing remain unreachable until their later dedicated gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ForStatement<'source> {
    pub(super) label: Option<ForLabel<'source>>,
    pub(super) pattern: Recovered<Box<Pattern<'source>>>,
    pub(super) in_keyword: Recovered<Range<usize>>,
    pub(super) iterable: Recovered<OperatorChain<'source>>,
    pub(super) body: Recovered<ForBody<'source>>,
    pub(super) range: Range<usize>,
}

impl ForStatement<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ForLabel<'source> {
    pub(super) text: &'source str,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ForBody<'source> {
    Braced {
        block: BracedStatementBlockExpression<'source>,
    },
    Colon {
        colon: Range<usize>,
        body: Recovered<ForColonBody<'source>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ForColonBody<'source> {
    Inline {
        expression: OperatorChain<'source>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}
