use super::*;

/// The sink-free prefix reserved for the shared Type-declaration judge.
///
/// Gate 1 only establishes this carrier; Gate 2 supplies the exact-word
/// recognition that fills it and commits the declaration authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) type_keyword: WordSpan<'source>,
    pub(super) type_base: usize,
}

/// Recognizes the sink-free prefix reserved for a Type declaration.
///
/// This remains deliberately separate from `recognize_statement_intro` until
/// the later dispatch gate.  An exact `type` keyword is enough to establish
/// declaration authority; all mandatory declaration slots belong to the
/// committed continuation introduced later.
pub(super) fn recognize_type_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let type_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(type_base, &mut i) else {
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
    if keyword.text() != "type" {
        i.rollback(checkpoint);
        return None;
    }
    Some(TypeStatementIntro {
        start,
        visibility,
        after_visibility,
        type_keyword: keyword,
        type_base,
    })
}

/// This is intentionally local rather than a global reserved-word state:
/// declaration parameters accept only words that the historical scanner would
/// have classified as ordinary identifiers at this grammar position.
pub(super) fn type_declaration_parameter_raw_word(word: WordSpan<'_>) -> bool {
    !matches!(
        word.text(),
        "use"
            | "mod"
            | "struct"
            | "type"
            | "for"
            | "realm"
            | "band"
            | "as"
            | "without"
            | "with"
            | "infix"
            | "my"
            | "pub"
            | "our"
            | "lazy"
            | "prefix"
            | "suffix"
            | "nullfix"
            | "if"
            | "case"
            | "catch"
            | "where"
            | "elsif"
            | "else"
            | "impl"
            | "derives"
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedTypeDeclarationHeader<'source> {
    pub(super) name: Recovered<WordSpan<'source>>,
    pub(super) parameters: Vec<DeclarationTypeParameter<'source>>,
    pub(super) equals: Recovered<Range<usize>>,
    pub(super) rhs_retry: bool,
}

/// The shared prefix of both nominal and equality Type declarations.  The
/// definition-introducer/RHS phase stays separate so the form judge can see
/// the original post-parameter gap before equality recovery owns it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedTypeDeclarationSharedHeader<'source> {
    pub(super) name: Recovered<WordSpan<'source>>,
    pub(super) parameters: Vec<DeclarationTypeParameter<'source>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum TypeDeclarationHeaderRecovery {
    Missing {
        role: crate::session::TypeDeclarationRole,
        at: usize,
    },
    Error {
        role: crate::session::TypeDeclarationRole,
        range: Range<usize>,
    },
}

/// Parses Type's pre-RHS slots without making the declaration reachable from a
/// real statement consumer.  Gate 5 owns the mandatory RHS itself; this helper
/// reports only whether that later slot may retry at the current cursor.
pub(super) fn parse_type_declaration_header_slots<'source, E>(
    intro: &TypeStatementIntro<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (
    ParsedTypeDeclarationHeader<'source>,
    Vec<TypeDeclarationHeaderRecovery>,
)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut recoveries = Vec::new();
    let shared = parse_type_declaration_shared_header_phase(intro, i, &mut recoveries);
    let (equals, rhs_retry) =
        parse_type_declaration_definition_phase(intro, &shared.name, i, &mut recoveries);

    (
        ParsedTypeDeclarationHeader {
            name: shared.name,
            parameters: shared.parameters,
            equals,
            rhs_retry,
        },
        recoveries,
    )
}

pub(super) fn parse_type_declaration_shared_header_phase<'source, E>(
    intro: &TypeStatementIntro<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
    recoveries: &mut Vec<TypeDeclarationHeaderRecovery>,
) -> ParsedTypeDeclarationSharedHeader<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name_boundary = any_ambient_owner_claims(i);
    if !name_boundary {
        let _ = mod_trivia(intro.type_base, i);
    }
    let name = if name_boundary {
        recoveries.push(TypeDeclarationHeaderRecovery::Missing {
            role: crate::session::TypeDeclarationRole::Name,
            at: i.pos(),
        });
        Recovered::Incomplete
    } else if let Some(name) = i.run(scan_word) {
        Recovered::Complete(name)
    } else {
        match scan_type_declaration_name_invalid_run(i) {
            Some(recovery) => {
                recoveries.push(TypeDeclarationHeaderRecovery::Error {
                    role: crate::session::TypeDeclarationRole::Name,
                    range: recovery.range,
                });
                match recovery.target {
                    TypeDeclarationInvalidTarget::RawName => Recovered::Complete(
                        i.run(scan_word)
                            .expect("a Type name retry must leave its raw word at the cursor"),
                    ),
                    TypeDeclarationInvalidTarget::Equals
                    | TypeDeclarationInvalidTarget::Boundary => Recovered::Incomplete,
                    TypeDeclarationInvalidTarget::Rhs => {
                        unreachable!("name recovery never retries a RHS")
                    }
                }
            }
            None => {
                recoveries.push(TypeDeclarationHeaderRecovery::Missing {
                    role: crate::session::TypeDeclarationRole::Name,
                    at: i.pos(),
                });
                Recovered::Incomplete
            }
        }
    };

    let parameters = if matches!(name, Recovered::Complete(_)) {
        scan_declaration_type_parameter_list(i).unwrap_or_default()
    } else {
        Vec::new()
    };

    ParsedTypeDeclarationSharedHeader { name, parameters }
}

pub(super) fn parse_type_declaration_definition_phase<'source, E>(
    intro: &TypeStatementIntro<'source>,
    name: &Recovered<WordSpan<'source>>,
    i: &mut SynIn<'_, 'source, '_, E>,
    recoveries: &mut Vec<TypeDeclarationHeaderRecovery>,
) -> (Recovered<Range<usize>>, bool)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let definition_boundary = any_ambient_owner_claims(i);
    if !definition_boundary {
        let continuation_checkpoint = i.checkpoint();
        if mod_trivia(intro.type_base, i).is_none() {
            i.rollback(continuation_checkpoint);
        }
    }

    if let Some(equals) = i.run(scan_declaration_exact_equals) {
        (Recovered::Complete(equals), true)
    } else if matches!(name, Recovered::Incomplete) {
        (Recovered::Incomplete, false)
    } else if definition_boundary {
        recoveries.push(TypeDeclarationHeaderRecovery::Missing {
            role: crate::session::TypeDeclarationRole::DefinitionIntroducer,
            at: i.pos(),
        });
        (Recovered::Incomplete, false)
    } else {
        match scan_type_declaration_definition_invalid_run(intro.type_base, i) {
            Some(recovery) => {
                recoveries.push(TypeDeclarationHeaderRecovery::Error {
                    role: crate::session::TypeDeclarationRole::DefinitionIntroducer,
                    range: recovery.range,
                });
                match recovery.target {
                    TypeDeclarationInvalidTarget::Equals => {
                        let equals = i.run(scan_declaration_exact_equals).expect(
                            "definition-introducer retry must leave exact equals at the cursor",
                        );
                        (Recovered::Complete(equals), true)
                    }
                    TypeDeclarationInvalidTarget::Rhs => (Recovered::Incomplete, true),
                    TypeDeclarationInvalidTarget::Boundary => (Recovered::Incomplete, false),
                    TypeDeclarationInvalidTarget::RawName => {
                        unreachable!(
                            "definition-introducer recovery never retries a declaration name"
                        )
                    }
                }
            }
            None if type_declaration_rhs_candidate_pending(i) => {
                recoveries.push(TypeDeclarationHeaderRecovery::Missing {
                    role: crate::session::TypeDeclarationRole::DefinitionIntroducer,
                    at: i.pos(),
                });
                (Recovered::Incomplete, true)
            }
            None => {
                recoveries.push(TypeDeclarationHeaderRecovery::Missing {
                    role: crate::session::TypeDeclarationRole::DefinitionIntroducer,
                    at: i.pos(),
                });
                (Recovered::Incomplete, false)
            }
        }
    }
}

/// Direct-CST's isolated header harness shares the AST scanner and merely
/// realizes its selected recoveries as committed typed records.
pub(super) fn commit_type_declaration_header_slots<'parse, 'source, 'local, E, O>(
    intro: &TypeStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParsedTypeDeclarationHeader<'source>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (header, recoveries) =
        committed.probe(|probe| parse_type_declaration_header_slots(intro, probe.input()));
    for recovery in recoveries {
        emit_type_declaration_header_recovery(committed, recovery);
    }
    header
}

pub(super) fn type_declaration_rhs_role() -> GrammarRole {
    GrammarRole::Declaration(DeclarationRole::Type(
        crate::session::TypeDeclarationRole::Rhs,
    ))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TypeDeclarationEqualityTail {
    DeclarationCompanion,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct TypeDeclarationRhsWithTail<T> {
    pub(super) rhs: Recovered<T>,
    pub(super) tail: Option<TypeDeclarationEqualityTail>,
}

pub(super) fn parse_type_declaration_rhs_with_companion_handoff_isolated<'source, E>(
    header: &ParsedTypeDeclarationHeader<'source>,
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> TypeDeclarationRhsWithTail<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !header.rhs_retry || any_ambient_owner_claims(i) {
        return TypeDeclarationRhsWithTail {
            rhs: Recovered::Incomplete,
            tail: None,
        };
    }
    if recognize_declaration_companion_handoff(type_base, i).is_some() {
        return TypeDeclarationRhsWithTail {
            rhs: Recovered::Incomplete,
            tail: Some(TypeDeclarationEqualityTail::DeclarationCompanion),
        };
    }
    let trivia_checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(type_base, i) else {
        i.rollback(trivia_checkpoint);
        return TypeDeclarationRhsWithTail {
            rhs: Recovered::Incomplete,
            tail: None,
        };
    };
    let baseline = IndentationBaseline {
        column: type_base,
        kind: IndentationBaselineKind::Introducer,
    };
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .with(StopKind::Semicolon)
        .with(StopKind::With)
        .with(StopKind::Derives);
    let scoped_frame = TypeExpressionScopedStopFrame {
        stops: StopSet::default()
            .with(StopKind::With)
            .with(StopKind::Derives),
        visible_episode_depth: i.local.type_expression_episode_depth() + 1,
    };
    let policy = TypeExpressionEpisodePolicy {
        fresh_primary_locally_owned_stops: StopSet::default().with(StopKind::With),
        ..TypeExpressionEpisodePolicy::default()
    };
    i.local.push_indentation_baseline(baseline);
    i.local.push_stop_set(stops);
    i.local.push_type_expression_scoped_stop_frame(scoped_frame);
    let rhs = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_handoff_recovery_isolated(
                    Some(type_declaration_rhs_role()),
                    policy,
                    |i| recognize_declaration_companion_handoff(type_base, i).is_some(),
                    i,
                ),
            )
        }))
        .expect("the isolated companion-aware Type RHS entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(scoped_frame)
    );
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_indentation_baseline(), Some(baseline));
    TypeDeclarationRhsWithTail {
        rhs: match rhs {
            Recovered::Complete(rhs) => Recovered::Complete(Box::new(rhs)),
            Recovered::Incomplete => Recovered::Incomplete,
        },
        tail: recognize_declaration_companion_handoff(type_base, i)
            .is_some()
            .then_some(TypeDeclarationEqualityTail::DeclarationCompanion),
    }
}

pub(super) fn commit_type_declaration_rhs_with_companion_handoff_isolated<
    'parse,
    'source,
    'local,
    E,
    O,
>(
    header: &ParsedTypeDeclarationHeader<'source>,
    type_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> TypeDeclarationRhsWithTail<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !header.rhs_retry {
        return TypeDeclarationRhsWithTail {
            rhs: Recovered::Incomplete,
            tail: None,
        };
    }
    if let Some(with) =
        committed.probe(|probe| recognize_declaration_companion_handoff(type_base, probe.input()))
    {
        emit_type_declaration_header_recovery(
            committed,
            TypeDeclarationHeaderRecovery::Missing {
                role: crate::session::TypeDeclarationRole::Rhs,
                at: with.start,
            },
        );
        return TypeDeclarationRhsWithTail {
            rhs: Recovered::Incomplete,
            tail: Some(TypeDeclarationEqualityTail::DeclarationCompanion),
        };
    }
    let trivia = committed.probe(|probe| {
        let i = probe.input();
        if any_ambient_owner_claims(i) {
            return None;
        }
        let checkpoint = i.checkpoint();
        let trivia = mod_trivia(type_base, i);
        if trivia.is_none() {
            i.rollback(checkpoint);
        }
        trivia
    });
    let Some(trivia) = trivia else {
        let at = committed.probe(|probe| probe.input().pos());
        emit_type_declaration_header_recovery(
            committed,
            TypeDeclarationHeaderRecovery::Missing {
                role: crate::session::TypeDeclarationRole::Rhs,
                at,
            },
        );
        return TypeDeclarationRhsWithTail {
            rhs: Recovered::Incomplete,
            tail: None,
        };
    };
    committed.emit_trivia(&trivia);
    let baseline = IndentationBaseline {
        column: type_base,
        kind: IndentationBaselineKind::Introducer,
    };
    let (stops, scoped_frame) = committed.probe(|probe| {
        let i = probe.input();
        (
            i.local
                .stop_set()
                .unwrap_or_default()
                .with(StopKind::Semicolon)
                .with(StopKind::With)
                .with(StopKind::Derives),
            TypeExpressionScopedStopFrame {
                stops: StopSet::default()
                    .with(StopKind::With)
                    .with(StopKind::Derives),
                visible_episode_depth: i.local.type_expression_episode_depth() + 1,
            },
        )
    });
    let policy = TypeExpressionEpisodePolicy {
        fresh_primary_locally_owned_stops: StopSet::default().with(StopKind::With),
        ..TypeExpressionEpisodePolicy::default()
    };
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_indentation_baseline(baseline);
        i.local.push_stop_set(stops);
        i.local.push_type_expression_scoped_stop_frame(scoped_frame);
    });
    let rhs = commit_direct_type_expression_with_handoff_recovery_isolated(
        Some(type_declaration_rhs_role()),
        policy,
        |i| recognize_declaration_companion_handoff(type_base, i).is_some(),
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(scoped_frame)
        );
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_indentation_baseline(), Some(baseline));
    });
    let range = rhs.range();
    TypeDeclarationRhsWithTail {
        rhs: if range.is_empty() {
            Recovered::Incomplete
        } else {
            Recovered::Complete(range)
        },
        tail: committed
            .probe(|probe| recognize_declaration_companion_handoff(type_base, probe.input()))
            .is_some()
            .then_some(TypeDeclarationEqualityTail::DeclarationCompanion),
    }
}

/// Owns the complete Type-declaration RHS episode. No caller can enter the
/// mandatory TypeExpression without first passing the original-gap ambient
/// check and installing the declaration baseline and stop scope here.
pub(super) fn parse_type_declaration_rhs<'source, E>(
    header: &ParsedTypeDeclarationHeader<'source>,
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !header.rhs_retry || any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let trivia_checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(type_base, i) else {
        i.rollback(trivia_checkpoint);
        return Recovered::Incomplete;
    };

    let baseline = IndentationBaseline {
        column: type_base,
        kind: IndentationBaselineKind::Introducer,
    };
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .with(StopKind::Semicolon)
        .with(StopKind::With);
    i.local.push_indentation_baseline(baseline);
    i.local.push_stop_set(stops);
    let rhs = i
        .run(from_fn(|i| {
            Some(parse_required_type_expression_with_outer_missing_role(
                Some(type_declaration_rhs_role()),
                i,
            ))
        }))
        .expect("the mandatory Type declaration RHS entry is total");
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_indentation_baseline(), Some(baseline));

    match rhs {
        Recovered::Complete(rhs) => Recovered::Complete(Box::new(rhs)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

/// Direct-CST counterpart of [`parse_type_declaration_rhs`]. The same helper
/// owns trivia emission, state setup, mandatory parsing, and exact teardown.
pub(super) fn commit_type_declaration_rhs<'parse, 'source, 'local, E, O>(
    header: &ParsedTypeDeclarationHeader<'source>,
    type_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !header.rhs_retry {
        return Recovered::Incomplete;
    }
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        let at = committed.probe(|probe| probe.input().pos());
        emit_type_declaration_header_recovery(
            committed,
            TypeDeclarationHeaderRecovery::Missing {
                role: crate::session::TypeDeclarationRole::Rhs,
                at,
            },
        );
        return Recovered::Incomplete;
    }
    let trivia = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = mod_trivia(type_base, i);
        if trivia.is_none() {
            i.rollback(checkpoint);
        }
        trivia
    });
    let Some(trivia) = trivia else {
        let at = committed.probe(|probe| probe.input().pos());
        emit_type_declaration_header_recovery(
            committed,
            TypeDeclarationHeaderRecovery::Missing {
                role: crate::session::TypeDeclarationRole::Rhs,
                at,
            },
        );
        return Recovered::Incomplete;
    };
    committed.emit_trivia(&trivia);

    let baseline = IndentationBaseline {
        column: type_base,
        kind: IndentationBaselineKind::Introducer,
    };
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .with(StopKind::Semicolon)
            .with(StopKind::With)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_indentation_baseline(baseline);
        i.local.push_stop_set(stops);
    });
    let rhs = commit_direct_type_expression_with_outer_missing_role(
        Some(type_declaration_rhs_role()),
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_indentation_baseline(), Some(baseline));
    });
    let range = rhs.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

/// Gate-7 isolated Type RHS episode.  It extends the already-atomic TD-T
/// state scope with a depth-fenced Derives stop, without changing the public
/// Type continuation before Gate 8.
pub(super) fn parse_type_declaration_rhs_with_derives_isolated<'source, E>(
    header: &ParsedTypeDeclarationHeader<'source>,
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !header.rhs_retry || any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let trivia_checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(type_base, i) else {
        i.rollback(trivia_checkpoint);
        return Recovered::Incomplete;
    };

    let baseline = IndentationBaseline {
        column: type_base,
        kind: IndentationBaselineKind::Introducer,
    };
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .with(StopKind::Semicolon)
        .with(StopKind::With)
        .with(StopKind::Derives);
    let scoped_frame = TypeExpressionScopedStopFrame {
        stops: StopSet::default().with(StopKind::Derives),
        visible_episode_depth: i.local.type_expression_episode_depth() + 1,
    };
    i.local.push_indentation_baseline(baseline);
    i.local.push_stop_set(stops);
    i.local.push_type_expression_scoped_stop_frame(scoped_frame);
    let rhs = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(type_declaration_rhs_role()),
                    TypeExpressionEpisodePolicy::default(),
                    i,
                ),
            )
        }))
        .expect("the mandatory derives-aware Type declaration RHS entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_indentation_baseline(), Some(baseline));

    match rhs {
        Recovered::Complete(rhs) => Recovered::Complete(Box::new(rhs)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

pub(super) fn commit_type_declaration_rhs_with_derives_isolated<'parse, 'source, 'local, E, O>(
    header: &ParsedTypeDeclarationHeader<'source>,
    type_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if !header.rhs_retry {
        return Recovered::Incomplete;
    }
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        let at = committed.probe(|probe| probe.input().pos());
        emit_type_declaration_header_recovery(
            committed,
            TypeDeclarationHeaderRecovery::Missing {
                role: crate::session::TypeDeclarationRole::Rhs,
                at,
            },
        );
        return Recovered::Incomplete;
    }
    let trivia = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = mod_trivia(type_base, i);
        if trivia.is_none() {
            i.rollback(checkpoint);
        }
        trivia
    });
    let Some(trivia) = trivia else {
        let at = committed.probe(|probe| probe.input().pos());
        emit_type_declaration_header_recovery(
            committed,
            TypeDeclarationHeaderRecovery::Missing {
                role: crate::session::TypeDeclarationRole::Rhs,
                at,
            },
        );
        return Recovered::Incomplete;
    };
    committed.emit_trivia(&trivia);

    let baseline = IndentationBaseline {
        column: type_base,
        kind: IndentationBaselineKind::Introducer,
    };
    let (stops, scoped_frame) = committed.probe(|probe| {
        let i = probe.input();
        (
            i.local
                .stop_set()
                .unwrap_or_default()
                .with(StopKind::Semicolon)
                .with(StopKind::With)
                .with(StopKind::Derives),
            TypeExpressionScopedStopFrame {
                stops: StopSet::default().with(StopKind::Derives),
                visible_episode_depth: i.local.type_expression_episode_depth() + 1,
            },
        )
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_indentation_baseline(baseline);
        i.local.push_stop_set(stops);
        i.local.push_type_expression_scoped_stop_frame(scoped_frame);
    });
    let rhs = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(type_declaration_rhs_role()),
        TypeExpressionEpisodePolicy::default(),
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_indentation_baseline(), Some(baseline));
    });
    let range = rhs.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

/// Parses the shared Type declaration, including header/trailing derives
/// attachments selected by the form-aware promotion core.
pub(crate) fn parse_type_declaration<'source, E>(
    i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_type_declaration_with_derives_isolated(&crate::operator::OperatorTable::empty(), i)
}

/// Operator-aware Type entry used by canonical Statement owners. Attached
/// Impl bodies receive the same table as every other statement-body family.
pub(crate) fn parse_type_declaration_with_operators<'source, E>(
    table: &crate::operator::OperatorTable,
    i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_type_declaration_with_derives_isolated(table, i)
}

/// Direct-CST counterpart of [`parse_type_declaration`], promoted atomically
/// through the same derives-aware core used by the isolated harness.
pub(crate) fn commit_type_declaration<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: TypeStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_type_declaration_with_derives_isolated(
        &crate::operator::OperatorTable::empty(),
        committed,
        intro,
    )
    .0
}

/// Operator-aware direct Type entry used by root and canonical Statement
/// owners. The accepted AttachedImpl tail shares their current table.
pub(crate) fn commit_type_declaration_with_operators<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: TypeStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_type_declaration_with_derives_isolated(table, committed, intro).0
}

fn parse_type_declaration_companion_after_handoff<'source, E>(
    table: &crate::operator::OperatorTable,
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DeclarationCompanion<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    mod_trivia(type_base, i).expect("an accepted Type companion handoff preserves its owner gap");
    parse_declaration_companion_isolated(table, type_base, i)
        .expect("an accepted Type companion handoff preserves exact `with`")
}

fn commit_type_declaration_companion_after_handoff<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    type_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Range<usize>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = committed
        .probe(|probe| mod_trivia(type_base, probe.input()))
        .expect("an accepted Type companion handoff preserves its owner gap");
    committed.emit_trivia(&leading);
    commit_declaration_companion_isolated(table, type_base, committed)
        .expect("an accepted Type companion handoff preserves exact `with`")
}

/// Shared promotion core for Type derives attachments. Header clauses run
/// after the shared name/parameter phase and before TND form selection;
/// trailing clauses run only after a selected Equality RHS episode.
pub(super) fn parse_type_declaration_with_derives_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let intro = i.run(recognize_type_statement_intro)?;
    let mut recoveries = Vec::new();
    let shared = parse_type_declaration_shared_header_phase(&intro, &mut i, &mut recoveries);
    let (mut derives, header_companion_tail) = if matches!(shared.name, Recovered::Complete(_)) {
        recognize_derives_attachment_start(
            DerivesAttachmentOwner::Type,
            DerivesAttachmentPosition::Header,
            intro.type_base,
            &mut i,
        )
        .map(|start| parse_derives_attachments_with_companion_handoff_isolated(start, &mut i))
        .map_or_else(
            || (Vec::new(), None),
            |parsed| (parsed.attachments, parsed.tail),
        )
    } else {
        (Vec::new(), None)
    };

    let decision = classify_type_declaration_post_header(&shared.name, intro.type_base, &mut i);
    let mut companion = None;
    let form = match decision {
        TypeDeclarationPostHeaderDecision::AttachedImpl(start) => {
            Recovered::Complete(TypeDeclarationForm::AttachedImpl(
                parse_type_attached_impl_isolated(table, start, &mut i),
            ))
        }
        TypeDeclarationPostHeaderDecision::Existing(_)
            if header_companion_tail.is_some()
                || recognize_declaration_companion_handoff(intro.type_base, &mut i).is_some() =>
        {
            if let Some(tail) = header_companion_tail {
                debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Type);
                debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
            }
            companion = Some(parse_type_declaration_companion_after_handoff(
                table,
                intro.type_base,
                &mut i,
            ));
            Recovered::Complete(TypeDeclarationForm::Nominal)
        }
        TypeDeclarationPostHeaderDecision::Existing(TypeDeclarationFormDisposition::Nominal {
            owns_trailing_trivia_through,
        }) => {
            consume_type_declaration_nominal_trailing_trivia_until(
                owns_trailing_trivia_through,
                &mut i,
            );
            Recovered::Complete(TypeDeclarationForm::Nominal)
        }
        TypeDeclarationPostHeaderDecision::Existing(
            TypeDeclarationFormDisposition::Equality
            | TypeDeclarationFormDisposition::EqualityRecovery,
        ) => {
            let (equals, rhs_retry) = parse_type_declaration_definition_phase(
                &intro,
                &shared.name,
                &mut i,
                &mut recoveries,
            );
            let header = ParsedTypeDeclarationHeader {
                name: shared.name.clone(),
                parameters: shared.parameters.clone(),
                equals,
                rhs_retry,
            };
            if header.rhs_retry {
                let rhs_with_tail = parse_type_declaration_rhs_with_companion_handoff_isolated(
                    &header,
                    intro.type_base,
                    &mut i,
                );
                let mut equality_companion_tail = rhs_with_tail.tail.is_some();
                if !equality_companion_tail
                    && let Some(start) = recognize_derives_attachment_start(
                        DerivesAttachmentOwner::Type,
                        DerivesAttachmentPosition::Trailing,
                        intro.type_base,
                        &mut i,
                    )
                {
                    let parsed =
                        parse_derives_attachments_with_companion_handoff_isolated(start, &mut i);
                    if let Some(tail) = parsed.tail {
                        debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Type);
                        debug_assert_eq!(tail.position, DerivesAttachmentPosition::Trailing);
                        equality_companion_tail = true;
                    }
                    derives.extend(parsed.attachments);
                }
                if equality_companion_tail {
                    companion = Some(parse_type_declaration_companion_after_handoff(
                        table,
                        intro.type_base,
                        &mut i,
                    ));
                }
                Recovered::Complete(TypeDeclarationForm::Equality {
                    equals: header.equals,
                    rhs: rhs_with_tail.rhs,
                })
            } else {
                Recovered::Incomplete
            }
        }
        TypeDeclarationPostHeaderDecision::Existing(TypeDeclarationFormDisposition::Incomplete) => {
            Recovered::Incomplete
        }
    };
    let range = intro.start..i.pos();
    Some(TypeDeclaration {
        visibility: intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility),
        name: shared.name,
        parameters: shared.parameters,
        derives,
        companion,
        form,
        range,
    })
}

/// Direct-CST counterpart of
/// [`parse_type_declaration_with_derives_isolated`].  It replays each phase
/// only after the shared probes have selected the same AST disposition.
pub(super) fn commit_type_declaration_with_derives_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: TypeStatementIntro<'source>,
) -> (Recovered<Range<usize>>, Vec<DirectDerivesAttachment>)
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::TypeDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::TypeKw, intro.type_keyword.range());

    let (shared, shared_recoveries, shared_end) = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let mut recoveries = Vec::new();
        let shared = parse_type_declaration_shared_header_phase(&intro, i, &mut recoveries);
        let end = i.pos();
        i.rollback(checkpoint);
        (shared, recoveries, end)
    });
    let shared_surface = ParsedTypeDeclarationHeader {
        name: shared.name.clone(),
        parameters: shared.parameters.clone(),
        equals: Recovered::Incomplete,
        rhs_retry: false,
    };
    commit_type_declaration_header_surface(
        intro.type_base,
        &shared_surface,
        shared_recoveries,
        shared_end,
        committed,
    );

    let (mut derives, header_companion_tail) = if matches!(shared.name, Recovered::Complete(_)) {
        committed
            .probe(|probe| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Type,
                    DerivesAttachmentPosition::Header,
                    intro.type_base,
                    probe.input(),
                )
            })
            .map(|start| {
                commit_derives_attachments_with_companion_handoff_isolated(start, committed)
            })
            .map_or_else(
                || (Vec::new(), None),
                |parsed| (parsed.attachments, parsed.tail),
            )
    } else {
        (Vec::new(), None)
    };

    let decision = committed.probe(|probe| {
        classify_type_declaration_post_header(&shared.name, intro.type_base, probe.input())
    });
    match decision {
        TypeDeclarationPostHeaderDecision::AttachedImpl(start) => {
            let _ = commit_type_attached_impl_isolated(table, start, committed);
        }
        TypeDeclarationPostHeaderDecision::Existing(_)
            if header_companion_tail.is_some()
                || committed.probe(|probe| {
                    recognize_declaration_companion_handoff(intro.type_base, probe.input())
                        .is_some()
                }) =>
        {
            if let Some(tail) = header_companion_tail {
                debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Type);
                debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
            }
            let _ =
                commit_type_declaration_companion_after_handoff(table, intro.type_base, committed);
        }
        TypeDeclarationPostHeaderDecision::Existing(TypeDeclarationFormDisposition::Nominal {
            owns_trailing_trivia_through,
        }) => commit_type_declaration_nominal_trailing_trivia_until(
            owns_trailing_trivia_through,
            committed,
        ),
        TypeDeclarationPostHeaderDecision::Existing(TypeDeclarationFormDisposition::Incomplete) => {
        }
        TypeDeclarationPostHeaderDecision::Existing(
            TypeDeclarationFormDisposition::Equality
            | TypeDeclarationFormDisposition::EqualityRecovery,
        ) => {
            let (header, definition_recoveries, definition_end) = committed.probe(|probe| {
                let i = probe.input();
                let checkpoint = i.checkpoint();
                let mut recoveries = Vec::new();
                let (equals, rhs_retry) = parse_type_declaration_definition_phase(
                    &intro,
                    &shared.name,
                    i,
                    &mut recoveries,
                );
                let end = i.pos();
                i.rollback(checkpoint);
                (
                    ParsedTypeDeclarationHeader {
                        name: shared.name.clone(),
                        parameters: shared.parameters.clone(),
                        equals,
                        rhs_retry,
                    },
                    recoveries,
                    end,
                )
            });
            commit_type_declaration_definition_surface_isolated(
                intro.type_base,
                &header,
                definition_recoveries,
                definition_end,
                committed,
            );
            if header.rhs_retry {
                let rhs_with_tail = commit_type_declaration_rhs_with_companion_handoff_isolated(
                    &header,
                    intro.type_base,
                    committed,
                );
                let mut equality_companion_tail = rhs_with_tail.tail.is_some();
                if !equality_companion_tail
                    && let Some(start) = committed.probe(|probe| {
                        recognize_derives_attachment_start(
                            DerivesAttachmentOwner::Type,
                            DerivesAttachmentPosition::Trailing,
                            intro.type_base,
                            probe.input(),
                        )
                    })
                {
                    let parsed = commit_derives_attachments_with_companion_handoff_isolated(
                        start, committed,
                    );
                    if let Some(tail) = parsed.tail {
                        debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Type);
                        debug_assert_eq!(tail.position, DerivesAttachmentPosition::Trailing);
                        equality_companion_tail = true;
                    }
                    derives.extend(parsed.attachments);
                }
                if equality_companion_tail {
                    let _ = commit_type_declaration_companion_after_handoff(
                        table,
                        intro.type_base,
                        committed,
                    );
                }
            }
        }
    }

    let end = committed.probe(|probe| probe.input().pos());
    committed.finish_node();
    (Recovered::Complete(intro.start..end), derives)
}

pub(super) fn commit_type_declaration_definition_surface_isolated<'parse, 'source, 'local, E, O>(
    type_base: usize,
    header: &ParsedTypeDeclarationHeader<'source>,
    recoveries: Vec<TypeDeclarationHeaderRecovery>,
    definition_end: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let definition_recovery = recoveries.iter().find(|recovery| {
        type_declaration_header_recovery_role(recovery)
            == crate::session::TypeDeclarationRole::DefinitionIntroducer
    });
    debug_assert_eq!(recoveries.len(), usize::from(definition_recovery.is_some()));
    let definition_target = definition_recovery
        .map(type_declaration_header_recovery_start)
        .or_else(|| match &header.equals {
            Recovered::Complete(equals) => Some(equals.start),
            Recovered::Incomplete => None,
        })
        .unwrap_or(definition_end);
    commit_type_declaration_continuation_trivia_until(type_base, definition_target, committed);
    if let Some(recovery) = definition_recovery {
        commit_type_declaration_header_recovery(recovery.clone(), committed);
    }
    if let Recovered::Complete(expected) = &header.equals {
        let actual = committed
            .probe(|probe| probe.input().run(scan_declaration_exact_equals))
            .expect("accepted Type definition introducer remains at the cursor");
        debug_assert_eq!(&actual, expected);
        committed.token(SyntaxKind::Equals, actual);
    }
    debug_assert_eq!(committed.probe(|probe| probe.input().pos()), definition_end);
}

pub(super) fn commit_type_declaration_header_surface<'parse, 'source, 'local, E, O>(
    type_base: usize,
    header: &ParsedTypeDeclarationHeader<'source>,
    recoveries: Vec<TypeDeclarationHeaderRecovery>,
    header_end: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name_recovery = recoveries.iter().find(|recovery| {
        type_declaration_header_recovery_role(recovery) == crate::session::TypeDeclarationRole::Name
    });
    let definition_recovery = recoveries.iter().find(|recovery| {
        type_declaration_header_recovery_role(recovery)
            == crate::session::TypeDeclarationRole::DefinitionIntroducer
    });

    let name_target = name_recovery
        .map(type_declaration_header_recovery_start)
        .or_else(|| match &header.name {
            Recovered::Complete(name) => Some(name.range().start),
            Recovered::Incomplete => None,
        })
        .or_else(|| definition_recovery.map(type_declaration_header_recovery_start))
        .or_else(|| match &header.equals {
            Recovered::Complete(equals) => Some(equals.start),
            Recovered::Incomplete => None,
        })
        .unwrap_or(header_end);
    commit_type_declaration_continuation_trivia_until(type_base, name_target, committed);
    if let Some(recovery) = name_recovery {
        commit_type_declaration_header_recovery(recovery.clone(), committed);
    }
    if let Recovered::Complete(expected) = &header.name {
        let actual = commit_word(committed).expect("accepted Type name remains at the cursor");
        debug_assert_eq!(actual.range(), expected.range());
        committed.token(SyntaxKind::Identifier, actual.range());
    }

    if !header.parameters.is_empty() {
        committed.start_node(SyntaxKind::DeclarationTypeParameterList);
        for parameter in &header.parameters {
            let trivia = committed
                .probe(|probe| scan_required_inline_trivia(probe.input()))
                .expect("an accepted Type parameter retains its same-line separator");
            committed.emit_trivia(&trivia);
            let actual = committed
                .probe(|probe| probe.input().run(scan_path_segment))
                .expect("an accepted Type parameter remains at the cursor");
            debug_assert_eq!(actual.range(), declaration_type_parameter_range(parameter));
            committed.token(declaration_type_parameter_kind(parameter), actual.range());
        }
        committed.finish_node();
    }

    let definition_target = definition_recovery
        .map(type_declaration_header_recovery_start)
        .or_else(|| match &header.equals {
            Recovered::Complete(equals) => Some(equals.start),
            Recovered::Incomplete => None,
        })
        .unwrap_or(header_end);
    commit_type_declaration_continuation_trivia_until(type_base, definition_target, committed);
    if let Some(recovery) = definition_recovery {
        commit_type_declaration_header_recovery(recovery.clone(), committed);
    }
    if let Recovered::Complete(expected) = &header.equals {
        let actual = committed
            .probe(|probe| probe.input().run(scan_declaration_exact_equals))
            .expect("accepted Type definition introducer remains at the cursor");
        debug_assert_eq!(&actual, expected);
        committed.token(SyntaxKind::Equals, actual);
    }
    debug_assert_eq!(committed.probe(|probe| probe.input().pos()), header_end);
}

pub(super) fn commit_type_declaration_continuation_trivia_until<'parse, 'source, 'local, E, O>(
    type_base: usize,
    target: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let current = committed.probe(|probe| probe.input().pos());
    if current == target {
        return;
    }
    let trivia = committed
        .probe(|probe| mod_trivia(type_base, probe.input()))
        .expect("accepted Type header trivia remains at the cursor");
    debug_assert_eq!(trivia.range(), current..target);
    committed.emit_trivia(&trivia);
}

/// Replays only the trailing trivia whose ownership the sink-free nominal form
/// judge already established.  This deliberately does not classify the gap a
/// second time: the reported endpoint is the complete ownership decision.
pub(super) fn commit_type_declaration_nominal_trailing_trivia_until<'parse, 'source, 'local, E, O>(
    target: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let current = committed.probe(|probe| probe.input().pos());
    if current == target {
        return;
    }
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("the nominal form judge reported remaining trailing trivia");
    debug_assert_eq!(trivia.range(), current..target);
    committed.emit_trivia(&trivia);
}

/// Consumes only the trailing trivia whose ownership the sink-free nominal
/// form judge already established.  It is replay, not a second form probe.
pub(super) fn consume_type_declaration_nominal_trailing_trivia_until<E>(
    target: usize,
    i: &mut SynIn<E>,
) where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let current = i.pos();
    if current == target {
        return;
    }
    let trivia = i
        .run(scan_trivia)
        .expect("the nominal form judge reported remaining trailing trivia");
    debug_assert_eq!(trivia.range(), current..target);
}

pub(super) fn commit_type_declaration_header_recovery<'parse, 'source, 'local, E, O>(
    recovery: TypeDeclarationHeaderRecovery,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if let TypeDeclarationHeaderRecovery::Error { range, .. } = &recovery {
        committed.probe(|probe| {
            let i = probe.input();
            debug_assert_eq!(i.pos(), range.start);
            while i.pos() < range.end {
                i.input
                    .next()
                    .expect("a selected Type header error range remains available");
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            debug_assert_eq!(i.pos(), range.end);
        });
    }
    emit_type_declaration_header_recovery(committed, recovery);
}

pub(super) fn type_declaration_header_recovery_role(
    recovery: &TypeDeclarationHeaderRecovery,
) -> crate::session::TypeDeclarationRole {
    match recovery {
        TypeDeclarationHeaderRecovery::Missing { role, .. }
        | TypeDeclarationHeaderRecovery::Error { role, .. } => *role,
    }
}

pub(super) fn type_declaration_header_recovery_start(
    recovery: &TypeDeclarationHeaderRecovery,
) -> usize {
    match recovery {
        TypeDeclarationHeaderRecovery::Missing { at, .. } => *at,
        TypeDeclarationHeaderRecovery::Error { range, .. } => range.start,
    }
}

pub(super) fn declaration_type_parameter_range(
    parameter: &DeclarationTypeParameter<'_>,
) -> Range<usize> {
    match parameter {
        DeclarationTypeParameter::Identifier(word)
        | DeclarationTypeParameter::SigilIdentifier(word) => word.range(),
    }
}

pub(super) fn declaration_type_parameter_kind(
    parameter: &DeclarationTypeParameter<'_>,
) -> SyntaxKind {
    match parameter {
        DeclarationTypeParameter::Identifier(_) => SyntaxKind::Identifier,
        DeclarationTypeParameter::SigilIdentifier(_) => SyntaxKind::SigilIdentifier,
    }
}

pub(super) fn emit_type_declaration_header_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    recovery: TypeDeclarationHeaderRecovery,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let (kind, role, range, unexpected) = match recovery {
        TypeDeclarationHeaderRecovery::Missing { role, at } => {
            (RecoveryKind::Missing, role, at..at, Arc::from([]))
        }
        TypeDeclarationHeaderRecovery::Error { role, range } => {
            let unexpected = Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]);
            (RecoveryKind::Error, role, range, unexpected)
        }
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Type(role));
        let expected = match role {
            GrammarRole::Declaration(DeclarationRole::Type(
                crate::session::TypeDeclarationRole::Name,
            )) => ExpectedSyntax::Identifier,
            GrammarRole::Declaration(DeclarationRole::Type(
                crate::session::TypeDeclarationRole::DefinitionIntroducer,
            )) => ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Equals),
            GrammarRole::Declaration(DeclarationRole::Type(
                crate::session::TypeDeclarationRole::Rhs,
            )) => ExpectedSyntax::TypeExpression,
            _ => unreachable!("Type header recovery has only Type declaration roles"),
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TypeDeclarationInvalidTarget {
    RawName,
    Equals,
    Rhs,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct TypeDeclarationInvalidRun {
    pub(super) range: Range<usize>,
    pub(super) target: TypeDeclarationInvalidTarget,
}

pub(super) fn scan_type_declaration_name_invalid_run<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclarationInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_type_declaration_invalid_run(i, |i| {
        type_declaration_raw_name_pending(i).then_some(TypeDeclarationInvalidTarget::RawName)
    })
}

pub(super) fn scan_type_declaration_definition_invalid_run<'source, E>(
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<TypeDeclarationInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_type_declaration_invalid_run(i, |i| {
        if type_declaration_terminal_boundary_pending(type_base, i) {
            Some(TypeDeclarationInvalidTarget::Boundary)
        } else if type_declaration_rhs_candidate_pending(i) {
            Some(TypeDeclarationInvalidTarget::Rhs)
        } else {
            None
        }
    })
}

pub(super) fn scan_type_declaration_invalid_run<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
    retry_candidate: impl Fn(&mut SynIn<'_, 'source, '_, E>) -> Option<TypeDeclarationInvalidTarget>,
) -> Option<TypeDeclarationInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if declaration_exact_equals_pending(i) {
            return (start < i.pos()).then_some(TypeDeclarationInvalidRun {
                range: start..i.pos(),
                target: TypeDeclarationInvalidTarget::Equals,
            });
        }
        if let Some(target) = retry_candidate(i) {
            return (start < i.pos()).then_some(TypeDeclarationInvalidRun {
                range: start..i.pos(),
                target,
            });
        }
        if type_declaration_terminal_boundary_pending(usize::MAX, i) {
            return (start < i.pos()).then_some(TypeDeclarationInvalidRun {
                range: start..i.pos(),
                target: TypeDeclarationInvalidTarget::Boundary,
            });
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(TypeDeclarationInvalidRun {
                range: start..i.pos(),
                target: TypeDeclarationInvalidTarget::Boundary,
            });
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

pub(super) fn type_declaration_raw_name_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_word).is_some();
    i.rollback(checkpoint);
    pending
}

pub(super) fn type_declaration_rhs_candidate_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(parse_type_expression).is_some();
    i.rollback(checkpoint);
    pending
}

pub(super) fn type_declaration_terminal_boundary_pending<E>(
    type_base: usize,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty()
        || matches!(i.input.remainder().chars().next(), Some(';'))
        || any_ambient_owner_claims(i)
    {
        return true;
    }
    if type_base == usize::MAX {
        return false;
    }
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia);
    let pending = trivia.is_some_and(|trivia| {
        i.input.source()[trivia.range()].contains(['\r', '\n'])
            && i.local.line().line_indent <= type_base
    });
    i.rollback(checkpoint);
    pending
}

/// The complete post-header priority decision used by production Type dispatch.
///
/// The `Existing` arm is the explicit insertion seam: a future `with:` form
/// goes before delegation, while a future role-like body belongs inside the
/// existing classifier after Equality and before its terminal dispositions.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum TypeDeclarationPostHeaderDecision<'source> {
    AttachedImpl(TypeAttachedImplStart<'source>),
    Existing(TypeDeclarationFormDisposition),
}

/// Exact attached-Impl evidence captured without consuming the Type gap.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct TypeAttachedImplStart<'source> {
    pub(super) leading: TriviaRun,
    pub(super) keyword: WordSpan<'source>,
    pub(super) type_base: usize,
}

/// Judges Type's post-header form in TAI-J priority order without committing
/// input, line state, diagnostics, or any rollback-owned local state.
pub(super) fn classify_type_declaration_post_header<'source, E>(
    name: &Recovered<WordSpan<'source>>,
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> TypeDeclarationPostHeaderDecision<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let attached_impl = if matches!(name, Recovered::Complete(_)) && !any_ambient_owner_claims(i) {
        let leading = i
            .run(scan_trivia)
            .expect("the maximal Type post-header gap scan is total");
        let has_physical_newline = struct_trivia_has_newline(&leading);
        let accepted_continuation = !has_physical_newline
            || (i.local.line().line_indent > type_base
                && !type_stop_is_active_in_current_episode(i, StopKind::Newline)
                && declaration_braced_newline_owner_from_stack(has_physical_newline, i.local)
                    .is_none());
        if accepted_continuation {
            i.run(scan_word)
                .filter(|word| word.text() == "impl")
                .map(|keyword| TypeAttachedImplStart {
                    leading,
                    keyword,
                    type_base,
                })
        } else {
            None
        }
    } else {
        None
    };
    i.rollback(checkpoint);

    attached_impl.map_or_else(
        || {
            // Future `with:` is inserted immediately before this delegation;
            // future role-like bodies are inserted inside the delegated judge
            // after its exact Equality decision.
            TypeDeclarationPostHeaderDecision::Existing(classify_type_declaration_form(
                name, type_base, i,
            ))
        },
        TypeDeclarationPostHeaderDecision::AttachedImpl,
    )
}

/// The isolated nominal-versus-equality disposition after Type's shared name
/// and parameter header.  This is deliberately sink-free until the later
/// dispatch gate selects a committed declaration continuation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum TypeDeclarationFormDisposition {
    /// The exclusive endpoint of terminal trivia the declaration owns.  A
    /// caller-owned boundary reports the shared-header end instead.
    Nominal {
        owns_trailing_trivia_through: usize,
    },
    Equality,
    EqualityRecovery,
    Incomplete,
}

/// Classifies the Type-declaration form without consuming the post-header
/// gap.  The committed nominal/equality continuations remain a later gate.
pub(super) fn classify_type_declaration_form<'source, E>(
    name: &Recovered<WordSpan<'source>>,
    type_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> TypeDeclarationFormDisposition
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let disposition = if !matches!(name, Recovered::Complete(_)) {
        if type_declaration_exact_equals_after_continuation_pending(type_base, i) {
            TypeDeclarationFormDisposition::EqualityRecovery
        } else {
            TypeDeclarationFormDisposition::Incomplete
        }
    } else {
        let ambient_boundary = any_ambient_owner_claims(i);
        if ambient_boundary {
            TypeDeclarationFormDisposition::Nominal {
                owns_trailing_trivia_through: i.pos(),
            }
        } else {
            let gap_checkpoint = i.checkpoint();
            let shared_end = i.pos();
            let trivia = i
                .run(scan_trivia)
                .expect("the maximal Type form gap trivia scan is total");
            let has_physical_newline = i.input.source()[trivia.range()].contains(['\r', '\n']);
            let accepted_continuation =
                !has_physical_newline || i.local.line().line_indent > type_base;
            let disposition = if accepted_continuation && declaration_exact_equals_pending(i) {
                TypeDeclarationFormDisposition::Equality
            } else {
                let owns_trailing_trivia_through =
                    if declaration_braced_newline_owner_from_stack(has_physical_newline, i.local)
                        .is_some()
                    {
                        Some(shared_end)
                    } else {
                        type_declaration_nominal_terminal_trivia_end_after_trivia(
                            type_base,
                            shared_end,
                            has_physical_newline,
                            i,
                        )
                    };
                match owns_trailing_trivia_through {
                    Some(owns_trailing_trivia_through) => TypeDeclarationFormDisposition::Nominal {
                        owns_trailing_trivia_through,
                    },
                    None => TypeDeclarationFormDisposition::EqualityRecovery,
                }
            };
            i.rollback(gap_checkpoint);
            disposition
        }
    };
    i.rollback(checkpoint);
    disposition
}

/// Probes an exact lone `=` after Type's ordinary continuation trivia.
pub(super) fn type_declaration_exact_equals_after_continuation_pending<E>(
    type_base: usize,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let accepted = mod_trivia(type_base, i).is_some() && declaration_exact_equals_pending(i);
    i.rollback(checkpoint);
    accepted
}

/// The non-ambient terminal alternatives for a complete nominal header.
pub(super) fn type_declaration_nominal_terminal_trivia_end_after_trivia<E>(
    type_base: usize,
    shared_end: usize,
    has_physical_newline: bool,
    i: &mut SynIn<E>,
) -> Option<usize>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if has_physical_newline && i.local.line().line_indent <= type_base {
        // The entire equal-or-shallower physical gap belongs to the caller,
        // even when that newline is immediately followed by EOF.
        Some(shared_end)
    } else if i.input.remainder().is_empty() {
        // Empty/same-line terminal trivia and maximal strictly-deeper
        // trailing trivia both end a nominal declaration at EOF.  In these
        // EOF cases the declaration owns the already-probed gap.
        Some(i.pos())
    } else if matches!(i.input.remainder().chars().next(), Some(';')) {
        (!has_physical_newline).then_some(i.pos())
    } else {
        type_declaration_active_fixed_statement_boundary_pending(i).then_some(shared_end)
    }
}

/// Active caller punctuation has statement-boundary authority only for this
/// fixed subset; semicolon remains its own terminal alternative above.
pub(super) fn type_declaration_active_fixed_statement_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        let stop = match punctuation.kind() {
            PunctuationKind::Comma => StopKind::Comma,
            PunctuationKind::Close(crate::session::Delimiter::Parenthesis) => {
                StopKind::RightParenthesis
            }
            PunctuationKind::Close(crate::session::Delimiter::Bracket) => StopKind::RightBracket,
            PunctuationKind::Close(crate::session::Delimiter::Brace) => StopKind::RightBrace,
            _ => return false,
        };
        i.local.stop_set().is_some_and(|stops| stops.contains(stop))
    });
    i.rollback(checkpoint);
    pending
}

/// A parser-side Type declaration.  Its form remains syntax-only: alias,
/// nominal, and opaque semantics belong to later HIR ownership.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeDeclaration<'source> {
    pub(super) visibility: Visibility,
    pub(super) name: Recovered<WordSpan<'source>>,
    pub(super) parameters: Vec<DeclarationTypeParameter<'source>>,
    pub(super) derives: Vec<DerivesAttachment<'source>>,
    pub(super) companion: Option<DeclarationCompanion<'source>>,
    pub(super) form: Recovered<TypeDeclarationForm<'source>>,
    pub(super) range: Range<usize>,
}

impl TypeDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum TypeDeclarationForm<'source> {
    Nominal,
    Equality {
        equals: Recovered<Range<usize>>,
        rhs: Recovered<Box<TypeExpression<'source>>>,
    },
    AttachedImpl(TypeAttachedImpl<'source>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TypeAttachedImpl<'source> {
    pub(super) impl_keyword: Range<usize>,
    pub(super) head: Recovered<Box<TypeExpression<'source>>>,
    pub(super) description: Option<ImplDescription<'source>>,
    pub(super) body: Recovered<ImplBody<'source>>,
    pub(super) range: Range<usize>,
}
