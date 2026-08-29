use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DerivesAttachmentOwner {
    Struct,
    Enum,
    Error,
    Act,
    Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DerivesAttachmentStart {
    pub(super) owner: DerivesAttachmentOwner,
    pub(super) position: DerivesAttachmentPosition,
    pub(super) keyword: Range<usize>,
    pub(super) owner_base: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DerivesOwnerTailClassifier {
    StructHeader,
    StructTrailing,
    EnumHeader,
    EnumTrailing,
    ErrorHeader,
    ErrorTrailing,
    ActHeader,
    ActTrailing,
    TypeHeader,
    TypeTrailing,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DerivesOwnerTail {
    StructBodyStarter,
    EnumBodyStarter,
    ErrorBodyStarter,
    ActSourceIntroducer,
    ActBodyStarter,
    TypeAttachedImpl,
    TypeDefinitionIntroducer,
    CallerBoundary,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DerivesDriverSpec {
    pub(super) owner: DerivesAttachmentOwner,
    pub(super) position: DerivesAttachmentPosition,
    pub(super) owner_base: usize,
    pub(super) owner_tail_classifier: DerivesOwnerTailClassifier,
    pub(super) outer_role: GrammarRole,
}

impl DerivesDriverSpec {
    pub(super) fn new(
        owner: DerivesAttachmentOwner,
        position: DerivesAttachmentPosition,
        owner_base: usize,
    ) -> Self {
        let owner_tail_classifier = match (owner, position) {
            (DerivesAttachmentOwner::Struct, DerivesAttachmentPosition::Header) => {
                DerivesOwnerTailClassifier::StructHeader
            }
            (DerivesAttachmentOwner::Struct, DerivesAttachmentPosition::Trailing) => {
                DerivesOwnerTailClassifier::StructTrailing
            }
            (DerivesAttachmentOwner::Enum, DerivesAttachmentPosition::Header) => {
                DerivesOwnerTailClassifier::EnumHeader
            }
            (DerivesAttachmentOwner::Enum, DerivesAttachmentPosition::Trailing) => {
                DerivesOwnerTailClassifier::EnumTrailing
            }
            (DerivesAttachmentOwner::Error, DerivesAttachmentPosition::Header) => {
                DerivesOwnerTailClassifier::ErrorHeader
            }
            (DerivesAttachmentOwner::Error, DerivesAttachmentPosition::Trailing) => {
                DerivesOwnerTailClassifier::ErrorTrailing
            }
            (DerivesAttachmentOwner::Act, DerivesAttachmentPosition::Header) => {
                DerivesOwnerTailClassifier::ActHeader
            }
            (DerivesAttachmentOwner::Act, DerivesAttachmentPosition::Trailing) => {
                DerivesOwnerTailClassifier::ActTrailing
            }
            (DerivesAttachmentOwner::Type, DerivesAttachmentPosition::Header) => {
                DerivesOwnerTailClassifier::TypeHeader
            }
            (DerivesAttachmentOwner::Type, DerivesAttachmentPosition::Trailing) => {
                DerivesOwnerTailClassifier::TypeTrailing
            }
        };
        Self {
            owner,
            position,
            owner_base,
            owner_tail_classifier,
            outer_role: GrammarRole::Declaration(DeclarationRole::Derives(
                DerivesRole::RoleReference,
            )),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum DerivesDriverDecision {
    Comma {
        leading: Range<usize>,
        comma: Range<usize>,
    },
    Via {
        leading: Range<usize>,
        keyword: Range<usize>,
    },
    RepeatedClause {
        leading: Range<usize>,
        start: DerivesAttachmentStart,
    },
    OwnerTail(DerivesOwnerTail),
    Boundary,
    NoContinuation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DerivesRoleEpisodeSpec {
    pub(super) stops: StopSet,
    pub(super) scoped_frame: TypeExpressionScopedStopFrame,
    pub(super) policy: TypeExpressionEpisodePolicy,
    pub(super) outer_role: GrammarRole,
}

/// Sink-free attachment authority at an owner-opened Struct/Type attachment
/// point. The original gap and following maximal word are always rolled back.
pub(super) fn recognize_derives_attachment_start<'source, E>(
    owner: DerivesAttachmentOwner,
    position: DerivesAttachmentPosition,
    owner_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<DerivesAttachmentStart>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let result = (|| {
        if any_ambient_owner_claims(i) {
            return None;
        }
        let trivia = i
            .run(scan_trivia)
            .expect("the derives attachment gap trivia scan is total");
        let has_physical_newline = struct_trivia_has_newline(&trivia);
        if derives_gap_is_caller_owned(owner_base, has_physical_newline, i) {
            return None;
        }
        let spec = DerivesDriverSpec::new(owner, position, owner_base);
        if classify_derives_owner_tail(spec.owner_tail_classifier, i).is_some() {
            return None;
        }
        let keyword = i.run(scan_word)?;
        (keyword.text() == "derives").then(|| DerivesAttachmentStart {
            owner,
            position,
            keyword: keyword.range(),
            owner_base,
        })
    })();
    i.rollback(checkpoint);
    result
}

/// One sink-free clause-tail decision shared by the future AST and direct-CST
/// adapters. Local comma/contextual continuations precede owner-tail handoff.
pub(super) fn drive_derives_clauses<E>(
    spec: DerivesDriverSpec,
    i: &mut SynIn<E>,
) -> DerivesDriverDecision
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let decision = if any_ambient_owner_claims(i) {
        DerivesDriverDecision::Boundary
    } else {
        let trivia = i
            .run(scan_trivia)
            .expect("the derives clause gap trivia scan is total");
        let leading = trivia.range();
        let has_physical_newline = struct_trivia_has_newline(&trivia);
        let tail_checkpoint = i.checkpoint();
        if derives_gap_is_caller_owned(spec.owner_base, has_physical_newline, i) {
            DerivesDriverDecision::Boundary
        } else if i.input.remainder().is_empty() {
            DerivesDriverDecision::Boundary
        } else if let Some(comma) = scan_derives_comma(i) {
            DerivesDriverDecision::Comma { leading, comma }
        } else if let Some(word) = i.run(scan_word) {
            match word.text() {
                "via" => DerivesDriverDecision::Via {
                    leading,
                    keyword: word.range(),
                },
                "derives" => DerivesDriverDecision::RepeatedClause {
                    leading,
                    start: DerivesAttachmentStart {
                        owner: spec.owner,
                        position: spec.position,
                        keyword: word.range(),
                        owner_base: spec.owner_base,
                    },
                },
                _ => {
                    i.rollback(tail_checkpoint);
                    classify_derives_owner_tail(spec.owner_tail_classifier, i).map_or(
                        DerivesDriverDecision::NoContinuation,
                        DerivesDriverDecision::OwnerTail,
                    )
                }
            }
        } else if let Some(tail) = classify_derives_owner_tail(spec.owner_tail_classifier, i) {
            DerivesDriverDecision::OwnerTail(tail)
        } else {
            DerivesDriverDecision::NoContinuation
        }
    };
    i.rollback(checkpoint);
    decision
}

pub(super) fn derives_role_episode_spec(
    spec: DerivesDriverSpec,
    incoming: StopSet,
    current_episode_depth: usize,
    ambient_newline_owner: Option<DeclarationBracedNewlineOwner>,
) -> DerivesRoleEpisodeSpec {
    let mut stops = incoming
        .with(StopKind::Comma)
        .with(StopKind::Derives)
        .with(StopKind::Via);
    let mut scoped_stops = StopSet::default()
        .with(StopKind::Derives)
        .with(StopKind::Via);
    if ambient_newline_owner.is_some() {
        // A RoleRef discovers this boundary only after parsing its first
        // primary. Keep it visible to that outer episode, while the scoped
        // frame suspends it inside parentheses, arrows, forall bodies, and
        // every other recursively-owned TypeExpression episode.
        stops = stops.with(StopKind::Newline);
        scoped_stops = scoped_stops.with(StopKind::Newline);
    }
    let mut policy = TypeExpressionEpisodePolicy::default();
    if spec.owner_tail_classifier == DerivesOwnerTailClassifier::StructHeader {
        for stop in [
            StopKind::LeftBrace,
            StopKind::LeftParenthesis,
            StopKind::Colon,
            StopKind::Semicolon,
        ] {
            stops = stops.with(stop);
            scoped_stops = scoped_stops.with(stop);
        }
        policy.fresh_primary_locally_owned_stops =
            StopSet::default().with(StopKind::LeftParenthesis);
    } else if matches!(
        spec.owner_tail_classifier,
        DerivesOwnerTailClassifier::EnumHeader
            | DerivesOwnerTailClassifier::ErrorHeader
            | DerivesOwnerTailClassifier::ActHeader
    ) {
        // Enum, Error, and Act raw headers leave every actual body introducer to the later
        // form judge. The scoped frame makes the four stops visible only to
        // this outer RoleRef episode; recursive TypeExpression episodes own
        // their nested punctuation as usual.
        for stop in [
            StopKind::LeftBrace,
            StopKind::Colon,
            StopKind::Equal,
            StopKind::Semicolon,
        ] {
            stops = stops.with(stop);
            scoped_stops = scoped_stops.with(stop);
        }
    } else if spec.owner_tail_classifier == DerivesOwnerTailClassifier::TypeHeader {
        // Equality and attached Impl belong only to the outer Header RoleRef
        // episode. Nested TypeExpression episodes retain both words as local
        // syntax, and fresh-primary `impl` hands back a Missing RoleRef.
        for stop in [StopKind::Equal, StopKind::Impl] {
            stops = stops.with(stop);
            scoped_stops = scoped_stops.with(stop);
        }
    }
    DerivesRoleEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy,
        outer_role: spec.outer_role,
    }
}

pub(super) fn derives_gap_is_caller_owned<E>(
    owner_base: usize,
    has_physical_newline: bool,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    has_physical_newline
        && (i.local.line().line_indent <= owner_base
            || type_stop_is_active_in_current_episode(i, StopKind::Newline)
            || declaration_braced_newline_owner_from_stack(true, i.local).is_some())
}

pub(super) fn derives_active_fixed_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        let stop = match punctuation.kind() {
            PunctuationKind::Comma => StopKind::Comma,
            PunctuationKind::Semicolon => StopKind::Semicolon,
            PunctuationKind::Close(Delimiter::Parenthesis) => StopKind::RightParenthesis,
            PunctuationKind::Close(Delimiter::Bracket) => StopKind::RightBracket,
            PunctuationKind::Close(Delimiter::Brace) => StopKind::RightBrace,
            _ => return false,
        };
        type_stop_is_active_in_current_episode(i, stop)
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn classify_derives_owner_tail<E>(
    classifier: DerivesOwnerTailClassifier,
    i: &mut SynIn<E>,
) -> Option<DerivesOwnerTail>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let owner_tail = match classifier {
        DerivesOwnerTailClassifier::TypeHeader if declaration_exact_impl_pending(i) => {
            Some(DerivesOwnerTail::TypeAttachedImpl)
        }
        DerivesOwnerTailClassifier::TypeHeader if declaration_exact_equals_pending(i) => {
            Some(DerivesOwnerTail::TypeDefinitionIntroducer)
        }
        DerivesOwnerTailClassifier::StructHeader => {
            i.run(scan_punctuation).and_then(|punctuation| {
                matches!(
                    punctuation.kind(),
                    PunctuationKind::Open(Delimiter::Brace)
                        | PunctuationKind::Open(Delimiter::Parenthesis)
                        | PunctuationKind::Colon
                        | PunctuationKind::Semicolon
                )
                .then_some(DerivesOwnerTail::StructBodyStarter)
            })
        }
        DerivesOwnerTailClassifier::EnumHeader if declaration_exact_equals_pending(i) => {
            Some(DerivesOwnerTail::EnumBodyStarter)
        }
        DerivesOwnerTailClassifier::EnumHeader => i.run(scan_punctuation).and_then(|punctuation| {
            matches!(
                punctuation.kind(),
                PunctuationKind::Open(Delimiter::Brace)
                    | PunctuationKind::Colon
                    | PunctuationKind::Semicolon
            )
            .then_some(DerivesOwnerTail::EnumBodyStarter)
        }),
        DerivesOwnerTailClassifier::ErrorHeader if declaration_exact_equals_pending(i) => {
            Some(DerivesOwnerTail::ErrorBodyStarter)
        }
        DerivesOwnerTailClassifier::ErrorHeader => {
            i.run(scan_punctuation).and_then(|punctuation| {
                matches!(
                    punctuation.kind(),
                    PunctuationKind::Open(Delimiter::Brace)
                        | PunctuationKind::Colon
                        | PunctuationKind::Semicolon
                )
                .then_some(DerivesOwnerTail::ErrorBodyStarter)
            })
        }
        DerivesOwnerTailClassifier::ActHeader if declaration_exact_equals_pending(i) => {
            Some(DerivesOwnerTail::ActSourceIntroducer)
        }
        DerivesOwnerTailClassifier::ActHeader => i.run(scan_punctuation).and_then(|punctuation| {
            matches!(
                punctuation.kind(),
                PunctuationKind::Open(Delimiter::Brace)
                    | PunctuationKind::Colon
                    | PunctuationKind::Semicolon
            )
            .then_some(DerivesOwnerTail::ActBodyStarter)
        }),
        _ => None,
    };
    i.rollback(checkpoint);
    owner_tail.or_else(|| {
        derives_active_fixed_boundary_pending(i).then_some(DerivesOwnerTail::CallerBoundary)
    })
}

/// Enum opens a trailing derives attachment point only after its own braced
/// variant body has consumed a real matching close. Colon/equals dedents and
/// every bodyless or recovered form intentionally leave `derives` to their
/// outer Statement owner instead.
pub(super) fn enum_body_has_actual_trailing_close(body: &Recovered<EnumBody<'_>>) -> bool {
    matches!(
        body,
        Recovered::Complete(EnumBody::Braced(EnumBracedBody {
            close: Recovered::Complete(_),
            ..
        }))
    )
}

/// Act opens a trailing derives attachment point only after its own braced
/// statement block has consumed a real matching close. Every bodyless, colon,
/// and recovered braced form leaves `derives` to the surrounding statement.
pub(super) fn act_body_has_actual_trailing_close(body: &Recovered<ActBody<'_>>) -> bool {
    matches!(
        body,
        Recovered::Complete(ActBody::Braced { block }) if block.has_complete_close()
    )
}

pub(super) fn scan_derives_comma<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let comma = i.run(scan_punctuation).and_then(|punctuation| {
        (punctuation.kind() == PunctuationKind::Comma).then(|| punctuation.range())
    });
    if comma.is_none() {
        i.rollback(checkpoint);
    }
    comma
}

/// Isolated AST construction for one owner-opened derives attachment point.
/// The caller supplies the sole accepted start; later clauses come only from
/// the shared driver so AST and direct-CST adapters cannot diverge on clause
/// continuation ownership.
pub(super) fn parse_derives_attachments_isolated<'source, E>(
    start: DerivesAttachmentStart,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Vec<DerivesAttachment<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut attachments = Vec::new();
    let mut next_start = Some(start);
    while let Some(start) = next_start.take() {
        let spec = DerivesDriverSpec::new(start.owner, start.position, start.owner_base);
        let (attachment, repeated_start) = parse_derives_clause_isolated(start, spec, i);
        attachments.push(attachment);
        next_start = repeated_start;
    }
    attachments
}

pub(super) fn parse_derives_clause_isolated<'source, E>(
    start: DerivesAttachmentStart,
    spec: DerivesDriverSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (DerivesAttachment<'source>, Option<DerivesAttachmentStart>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = i
        .run(scan_trivia)
        .expect("the derives attachment gap is total");
    debug_assert_eq!(leading.range().end, start.keyword.start);
    let keyword = i
        .run(scan_word)
        .expect("an accepted derives attachment start leaves its keyword at the cursor");
    assert_eq!(keyword.range(), start.keyword);
    debug_assert_eq!(keyword.text(), "derives");

    let mut roles = Vec::new();
    let (via, repeated_start) = loop {
        consume_derives_role_trivia(start.owner_base, i);
        roles.push(parse_required_derives_role(spec, i));
        match drive_derives_clauses(spec, i) {
            DerivesDriverDecision::Comma { leading, comma } => {
                consume_derives_trivia(leading, i);
                let consumed = scan_derives_comma(i)
                    .expect("the shared derives driver leaves its comma at the cursor");
                assert_eq!(consumed, comma);
            }
            DerivesDriverDecision::Via { leading, keyword } => {
                consume_derives_trivia(leading, i);
                let consumed = i
                    .run(scan_word)
                    .expect("the shared derives driver leaves its via word at the cursor");
                assert_eq!(consumed.range(), keyword);
                debug_assert_eq!(consumed.text(), "via");
                let via = parse_derives_via_isolated(keyword, spec, i);
                let repeated_start = match drive_derives_clauses(spec, i) {
                    DerivesDriverDecision::RepeatedClause { leading, start } => {
                        consume_derives_trivia(leading, i);
                        Some(start)
                    }
                    DerivesDriverDecision::Comma { .. }
                    | DerivesDriverDecision::Via { .. }
                    | DerivesDriverDecision::OwnerTail(_)
                    | DerivesDriverDecision::Boundary
                    | DerivesDriverDecision::NoContinuation => None,
                };
                break (Some(via), repeated_start);
            }
            DerivesDriverDecision::RepeatedClause { leading, start } => {
                consume_derives_trivia(leading, i);
                break (None, Some(start));
            }
            DerivesDriverDecision::OwnerTail(_)
            | DerivesDriverDecision::Boundary
            | DerivesDriverDecision::NoContinuation => break (None, None),
        }
    };
    let end = i.pos();
    let clause_start = start.keyword.start;
    (
        DerivesAttachment {
            position: start.position,
            clause: DerivesClause {
                keyword: start.keyword,
                roles,
                via,
                range: clause_start..end,
            },
        },
        repeated_start,
    )
}

pub(super) fn consume_derives_trivia<E>(expected: Range<usize>, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = i.run(scan_trivia).expect("trivia is total");
    assert_eq!(trivia.range(), expected);
}

pub(super) fn consume_derives_role_trivia<E>(owner_base: usize, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    if derives_gap_is_caller_owned(owner_base, struct_trivia_has_newline(&trivia), i) {
        i.rollback(checkpoint);
    }
}

pub(super) fn parse_required_derives_role<'source, E>(
    spec: DerivesDriverSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = i.local.stop_set().unwrap_or_default();
    let ambient_newline_owner = declaration_braced_newline_owner_for_physical_newline(i.local);
    let episode = derives_role_episode_spec(
        spec,
        incoming,
        i.local.type_expression_episode_depth(),
        ambient_newline_owner,
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let role = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("the mandatory derives RoleReference entry is total");
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    match role {
        Recovered::Complete(role) => Recovered::Complete(Box::new(role)),
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DerivesViaInvalidTarget {
    RawIdentifier,
    Boundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DerivesViaInvalidRun {
    pub(super) range: Range<usize>,
    pub(super) target: DerivesViaInvalidTarget,
}

/// `scan_word` is the existing declaration-name convention for a mandatory
/// raw lexical identifier: it intentionally performs no contextual keyword
/// reclassification.  Its malformed-run recovery stops at the same clause
/// driver boundaries as the role list, then retries one raw word in place.
pub(super) fn parse_derives_via_isolated<'source, E>(
    keyword: Range<usize>,
    spec: DerivesDriverSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DerivesVia<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    consume_derives_role_trivia(spec.owner_base, i);
    let target = if let Some(target) = i.run(scan_word) {
        Recovered::Complete(target)
    } else if let Some(recovery) = scan_derives_via_invalid_run(spec, i) {
        match recovery.target {
            DerivesViaInvalidTarget::RawIdentifier => Recovered::Complete(
                i.run(scan_word)
                    .expect("ViaTarget retry leaves its raw word at the cursor"),
            ),
            DerivesViaInvalidTarget::Boundary => Recovered::Incomplete,
        }
    } else {
        Recovered::Incomplete
    };
    let end = match &target {
        Recovered::Complete(target) => target.range().end,
        Recovered::Incomplete => keyword.end,
    };
    let range_start = keyword.start;
    DerivesVia {
        keyword,
        target,
        range: range_start..end,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectDerivesAttachment {
    pub(super) position: DerivesAttachmentPosition,
    pub(super) clause: DirectDerivesClause,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectDerivesClause {
    pub(super) keyword: Range<usize>,
    pub(super) roles: Vec<Recovered<Range<usize>>>,
    pub(super) via: Option<DirectDerivesVia>,
    pub(super) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectDerivesVia {
    pub(super) keyword: Range<usize>,
    pub(super) target: Recovered<Range<usize>>,
    pub(super) range: Range<usize>,
}

/// Isolated direct-CST counterpart of [`parse_derives_attachments_isolated`].
/// The owner adapter supplies the one accepted start; this function owns only
/// DerivesClause nodes and their source children, not declaration dispatch.
pub(super) fn commit_derives_attachments_isolated<'parse, 'source, 'local, E, O>(
    start: DerivesAttachmentStart,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Vec<DirectDerivesAttachment>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut attachments = Vec::new();
    let mut next_start = Some(start);
    while let Some(start) = next_start.take() {
        let spec = DerivesDriverSpec::new(start.owner, start.position, start.owner_base);
        let (attachment, repeated_start) = commit_derives_clause_isolated(start, spec, committed);
        attachments.push(attachment);
        next_start = repeated_start;
    }
    attachments
}

pub(super) fn commit_derives_clause_isolated<'parse, 'source, 'local, E, O>(
    start: DerivesAttachmentStart,
    spec: DerivesDriverSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> (DirectDerivesAttachment, Option<DerivesAttachmentStart>)
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::DerivesClause);
    let leading = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("the derives attachment gap is total");
    debug_assert_eq!(leading.range().end, start.keyword.start);
    committed.emit_trivia(&leading);
    let keyword = commit_word(committed)
        .expect("an accepted derives attachment start leaves its keyword at the cursor");
    assert_eq!(keyword.range(), start.keyword);
    debug_assert_eq!(keyword.text(), "derives");
    committed.token(SyntaxKind::DerivesKw, keyword.range());

    let mut roles = Vec::new();
    let (via, repeated_start) = loop {
        commit_derives_role_trivia(start.owner_base, committed);
        roles.push(commit_required_derives_role(spec, committed));
        match committed.probe(|probe| drive_derives_clauses(spec, probe.input())) {
            DerivesDriverDecision::Comma { leading, comma } => {
                commit_derives_trivia(leading, committed);
                let consumed = committed
                    .probe(|probe| scan_derives_comma(probe.input()))
                    .expect("the shared derives driver leaves its comma at the cursor");
                assert_eq!(consumed, comma);
                committed.token(SyntaxKind::Comma, consumed);
            }
            DerivesDriverDecision::Via { leading, keyword } => {
                commit_derives_trivia(leading, committed);
                let consumed = commit_word(committed)
                    .expect("the shared derives driver leaves its via word at the cursor");
                assert_eq!(consumed.range(), keyword);
                debug_assert_eq!(consumed.text(), "via");
                committed.token(SyntaxKind::ViaKw, consumed.range());
                let via = commit_derives_via_isolated(keyword, spec, committed);
                let repeated_start =
                    match committed.probe(|probe| drive_derives_clauses(spec, probe.input())) {
                        DerivesDriverDecision::RepeatedClause { leading, start } => {
                            commit_derives_trivia(leading, committed);
                            Some(start)
                        }
                        DerivesDriverDecision::Comma { .. }
                        | DerivesDriverDecision::Via { .. }
                        | DerivesDriverDecision::OwnerTail(_)
                        | DerivesDriverDecision::Boundary
                        | DerivesDriverDecision::NoContinuation => None,
                    };
                break (Some(via), repeated_start);
            }
            DerivesDriverDecision::RepeatedClause { leading, start } => {
                commit_derives_trivia(leading, committed);
                break (None, Some(start));
            }
            DerivesDriverDecision::OwnerTail(_)
            | DerivesDriverDecision::Boundary
            | DerivesDriverDecision::NoContinuation => break (None, None),
        }
    };
    let end = committed_position(committed);
    let clause_start = start.keyword.start;
    committed.finish_node();
    (
        DirectDerivesAttachment {
            position: start.position,
            clause: DirectDerivesClause {
                keyword: start.keyword,
                roles,
                via,
                range: clause_start..end,
            },
        },
        repeated_start,
    )
}

pub(super) fn commit_derives_trivia<'parse, 'source, 'local, E, O>(
    expected: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia is total");
    assert_eq!(trivia.range(), expected);
    committed.emit_trivia(&trivia);
}

pub(super) fn commit_derives_role_trivia<'parse, 'source, 'local, E, O>(
    owner_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let trivia = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let trivia = i.run(scan_trivia).expect("trivia is total");
        if derives_gap_is_caller_owned(owner_base, struct_trivia_has_newline(&trivia), i) {
            i.rollback(checkpoint);
            None
        } else {
            Some(trivia)
        }
    });
    if let Some(trivia) = trivia.as_ref() {
        committed.emit_trivia(trivia);
    }
}

pub(super) fn commit_required_derives_role<'parse, 'source, 'local, E, O>(
    spec: DerivesDriverSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = committed.probe(|probe| probe.input().local.stop_set().unwrap_or_default());
    let episode = committed.probe(|probe| {
        let i = probe.input();
        derives_role_episode_spec(
            spec,
            incoming,
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
    let role = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame)
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = role.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

pub(super) fn commit_derives_via_isolated<'parse, 'source, 'local, E, O>(
    keyword: Range<usize>,
    spec: DerivesDriverSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> DirectDerivesVia
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_derives_role_trivia(spec.owner_base, committed);
    let target = if let Some(target) = commit_word(committed) {
        let range = target.range();
        committed.token(SyntaxKind::Identifier, range.clone());
        Recovered::Complete(range)
    } else if let Some(recovery) =
        committed.probe(|probe| scan_derives_via_invalid_run(spec, probe.input()))
    {
        emit_derives_via_recovery(committed, RecoveryKind::Error, recovery.range.clone());
        match recovery.target {
            DerivesViaInvalidTarget::RawIdentifier => {
                let target = commit_word(committed)
                    .expect("ViaTarget retry leaves its raw word at the cursor");
                let range = target.range();
                committed.token(SyntaxKind::Identifier, range.clone());
                Recovered::Complete(range)
            }
            DerivesViaInvalidTarget::Boundary => Recovered::Incomplete,
        }
    } else {
        let at = committed_position(committed);
        emit_derives_via_recovery(committed, RecoveryKind::Missing, at..at);
        Recovered::Incomplete
    };
    let end = match &target {
        Recovered::Complete(target) => target.end,
        Recovered::Incomplete => keyword.end,
    };
    let range_start = keyword.start;
    DirectDerivesVia {
        keyword,
        target,
        range: range_start..end,
    }
}

pub(super) fn scan_derives_via_invalid_run<E>(
    spec: DerivesDriverSpec,
    i: &mut SynIn<E>,
) -> Option<DerivesViaInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if derives_via_boundary_pending(spec, i) {
            return (start < i.pos()).then_some(DerivesViaInvalidRun {
                range: start..i.pos(),
                target: DerivesViaInvalidTarget::Boundary,
            });
        }
        if start < i.pos() && derives_via_raw_identifier_pending(i) {
            return Some(DerivesViaInvalidRun {
                range: start..i.pos(),
                target: DerivesViaInvalidTarget::RawIdentifier,
            });
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(DerivesViaInvalidRun {
                range: start..i.pos(),
                target: DerivesViaInvalidTarget::Boundary,
            });
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

pub(super) fn derives_via_boundary_pending<E>(spec: DerivesDriverSpec, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    !matches!(
        drive_derives_clauses(spec, i),
        DerivesDriverDecision::NoContinuation
    )
}

pub(super) fn derives_via_raw_identifier_pending<E>(i: &mut SynIn<E>) -> bool
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

pub(super) fn emit_derives_via_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    kind: RecoveryKind,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Derives(DerivesRole::ViaTarget));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            kind,
            match kind {
                RecoveryKind::Missing => Arc::from([]),
                RecoveryKind::Error => Arc::from([crate::session::UnexpectedSyntax::Token {
                    range: range.clone(),
                    category: crate::session::UnexpectedCategory::OtherCharacter,
                }]),
            },
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Identifier,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DerivesAttachment<'source> {
    pub(super) position: DerivesAttachmentPosition,
    pub(super) clause: DerivesClause<'source>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DerivesClause<'source> {
    pub(super) keyword: Range<usize>,
    pub(super) roles: Vec<Recovered<Box<TypeExpression<'source>>>>,
    pub(super) via: Option<DerivesVia<'source>>,
    pub(super) range: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct DerivesVia<'source> {
    pub(super) keyword: Range<usize>,
    pub(super) target: Recovered<WordSpan<'source>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum DerivesAttachmentPosition {
    Header,
    Trailing,
}
