use super::*;
use crate::session::{
    CanonicalRecoveryContinuation, CanonicalRecoveryEpisode, RecoverySiteSpec, UnexpectedCategory,
    YumarkEmbeddedRecoveryFact,
};

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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DerivesClauseStart {
    pub(super) keyword: Range<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum DeclarationCompanionDerivesLayout {
    Inline,
    Indented { block_indent: usize },
    Braced,
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
pub(super) enum DerivesDriverContext {
    Attachment {
        owner: DerivesAttachmentOwner,
        position: DerivesAttachmentPosition,
        owner_base: usize,
        owner_tail_classifier: DerivesOwnerTailClassifier,
    },
    DeclarationCompanion {
        layout: DeclarationCompanionDerivesLayout,
    },
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
    pub(super) context: DerivesDriverContext,
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
            context: DerivesDriverContext::Attachment {
                owner,
                position,
                owner_base,
                owner_tail_classifier,
            },
            outer_role: GrammarRole::Declaration(DeclarationRole::Derives(
                DerivesRole::RoleReference,
            )),
        }
    }

    pub(super) fn declaration_companion(layout: DeclarationCompanionDerivesLayout) -> Self {
        Self {
            context: DerivesDriverContext::DeclarationCompanion { layout },
            outer_role: GrammarRole::Declaration(DeclarationRole::Derives(
                DerivesRole::RoleReference,
            )),
        }
    }

    fn attachment_metadata(
        self,
    ) -> Option<(
        DerivesAttachmentOwner,
        DerivesAttachmentPosition,
        usize,
        DerivesOwnerTailClassifier,
    )> {
        match self.context {
            DerivesDriverContext::Attachment {
                owner,
                position,
                owner_base,
                owner_tail_classifier,
            } => Some((owner, position, owner_base, owner_tail_classifier)),
            DerivesDriverContext::DeclarationCompanion { .. } => None,
        }
    }

    pub(super) fn attachment_owner_tail_classifier(self) -> DerivesOwnerTailClassifier {
        self.attachment_metadata()
            .map(|(_, _, _, classifier)| classifier)
            .expect("an attachment classifier is unavailable in declaration-companion context")
    }

    pub(super) fn attachment_owner_base(self) -> usize {
        self.attachment_metadata()
            .map(|(_, _, owner_base, _)| owner_base)
            .expect("an attachment base is unavailable in declaration-companion context")
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
    DeclarationCompanionRepeatedClause {
        leading: Range<usize>,
        start: DerivesClauseStart,
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
        let (_, _, _, owner_tail_classifier) = spec
            .attachment_metadata()
            .expect("an attachment spec preserves its owner metadata");
        if classify_derives_owner_tail(owner_tail_classifier, i).is_some() {
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
    } else if let DerivesDriverContext::DeclarationCompanion { layout } = spec.context
        && super::companion::declaration_companion_derives_sequence_boundary_pending(layout, i)
    {
        DerivesDriverDecision::Boundary
    } else {
        let trivia = i
            .run(scan_trivia)
            .expect("the derives clause gap trivia scan is total");
        let leading = trivia.range();
        let has_physical_newline = struct_trivia_has_newline(&trivia);
        let tail_checkpoint = i.checkpoint();
        if let DerivesDriverContext::Attachment { owner_base, .. } = spec.context
            && derives_gap_is_caller_owned(owner_base, has_physical_newline, i)
        {
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
                "derives" => match spec.context {
                    DerivesDriverContext::Attachment {
                        owner,
                        position,
                        owner_base,
                        ..
                    } => DerivesDriverDecision::RepeatedClause {
                        leading,
                        start: DerivesAttachmentStart {
                            owner,
                            position,
                            keyword: word.range(),
                            owner_base,
                        },
                    },
                    DerivesDriverContext::DeclarationCompanion { .. } => {
                        DerivesDriverDecision::DeclarationCompanionRepeatedClause {
                            leading,
                            start: DerivesClauseStart {
                                keyword: word.range(),
                            },
                        }
                    }
                },
                _ => {
                    i.rollback(tail_checkpoint);
                    spec.attachment_metadata()
                        .and_then(|(_, _, _, classifier)| {
                            classify_derives_owner_tail(classifier, i)
                        })
                        .map_or(
                            DerivesDriverDecision::NoContinuation,
                            DerivesDriverDecision::OwnerTail,
                        )
                }
            }
        } else if let Some(tail) = spec
            .attachment_metadata()
            .and_then(|(_, _, _, classifier)| classify_derives_owner_tail(classifier, i))
        {
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
    let attachment_classifier = spec
        .attachment_metadata()
        .map(|(_, _, _, classifier)| classifier);
    if attachment_classifier == Some(DerivesOwnerTailClassifier::StructHeader) {
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
        attachment_classifier,
        Some(
            DerivesOwnerTailClassifier::EnumHeader
                | DerivesOwnerTailClassifier::ErrorHeader
                | DerivesOwnerTailClassifier::ActHeader
        )
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
    } else if attachment_classifier == Some(DerivesOwnerTailClassifier::TypeHeader) {
        // Equality and attached Impl belong only to the outer Header RoleRef
        // episode. Nested TypeExpression episodes retain both words as local
        // syntax, and fresh-primary `impl` hands back a Missing RoleRef.
        for stop in [StopKind::Equal, StopKind::Impl] {
            stops = stops.with(stop);
            scoped_stops = scoped_stops.with(stop);
        }
    } else if let DerivesDriverContext::DeclarationCompanion { layout } = spec.context {
        let layout_stops: &[StopKind] = match layout {
            DeclarationCompanionDerivesLayout::Inline => &[
                StopKind::Newline,
                StopKind::Semicolon,
                StopKind::Comma,
                StopKind::RightParenthesis,
                StopKind::RightBracket,
                StopKind::RightBrace,
            ],
            DeclarationCompanionDerivesLayout::Indented { .. } => &[
                StopKind::Semicolon,
                StopKind::RightParenthesis,
                StopKind::RightBracket,
                StopKind::RightBrace,
            ],
            DeclarationCompanionDerivesLayout::Braced => &[
                StopKind::Newline,
                StopKind::Semicolon,
                StopKind::Comma,
                StopKind::RightParenthesis,
                StopKind::RightBracket,
                StopKind::RightBrace,
            ],
        };
        for &stop in layout_stops {
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct DerivesDeclarationCompanionTail {
    pub(super) owner: DerivesAttachmentOwner,
    pub(super) position: DerivesAttachmentPosition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DerivesAttachmentsWithTail<'source> {
    pub(super) attachments: Vec<DerivesAttachment<'source>>,
    pub(super) tail: Option<DerivesDeclarationCompanionTail>,
}

enum CompanionDerivesDecision {
    Comma {
        leading: Range<usize>,
        comma: Range<usize>,
    },
    Via {
        leading: Range<usize>,
        keyword: Range<usize>,
    },
    Repeated {
        leading: Range<usize>,
        start: DerivesAttachmentStart,
    },
    Companion(DerivesDeclarationCompanionTail),
    Boundary,
    NoContinuation,
}

fn companion_derives_tail(start: &DerivesAttachmentStart) -> DerivesDeclarationCompanionTail {
    DerivesDeclarationCompanionTail {
        owner: start.owner,
        position: start.position,
    }
}

fn drive_companion_handoff_derives<E>(
    start: &DerivesAttachmentStart,
    i: &mut SynIn<E>,
) -> CompanionDerivesDecision
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let decision = if any_ambient_owner_claims(i) {
        CompanionDerivesDecision::Boundary
    } else if recognize_declaration_companion_handoff(start.owner_base, i).is_some() {
        CompanionDerivesDecision::Companion(companion_derives_tail(start))
    } else {
        let trivia = i
            .run(scan_trivia)
            .expect("the isolated derives clause gap scan is total");
        let leading = trivia.range();
        let has_physical_newline = struct_trivia_has_newline(&trivia);
        let tail_checkpoint = i.checkpoint();
        let ordinary_spec = DerivesDriverSpec::new(start.owner, start.position, start.owner_base);
        if derives_gap_is_caller_owned(start.owner_base, has_physical_newline, i)
            || i.input.remainder().is_empty()
        {
            CompanionDerivesDecision::Boundary
        } else if let Some(comma) = scan_derives_comma(i) {
            CompanionDerivesDecision::Comma { leading, comma }
        } else if let Some(word) = i.run(scan_word) {
            match word.text() {
                "via" => CompanionDerivesDecision::Via {
                    leading,
                    keyword: word.range(),
                },
                "derives" => CompanionDerivesDecision::Repeated {
                    leading,
                    start: DerivesAttachmentStart {
                        owner: start.owner,
                        position: start.position,
                        keyword: word.range(),
                        owner_base: start.owner_base,
                    },
                },
                _ => {
                    i.rollback(tail_checkpoint);
                    classify_derives_owner_tail(ordinary_spec.attachment_owner_tail_classifier(), i)
                        .map_or(CompanionDerivesDecision::NoContinuation, |_| {
                            CompanionDerivesDecision::Boundary
                        })
                }
            }
        } else if classify_derives_owner_tail(ordinary_spec.attachment_owner_tail_classifier(), i)
            .is_some()
        {
            CompanionDerivesDecision::Boundary
        } else {
            CompanionDerivesDecision::NoContinuation
        }
    };
    i.rollback(checkpoint);
    decision
}

fn companion_derives_role_episode_spec<E>(
    start: &DerivesAttachmentStart,
    i: &SynIn<E>,
) -> DerivesRoleEpisodeSpec
where
    E: ErrorSink<usize>,
{
    let ordinary = derives_role_episode_spec(
        DerivesDriverSpec::new(start.owner, start.position, start.owner_base),
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
        declaration_braced_newline_owner_for_physical_newline(i.local),
    );
    DerivesRoleEpisodeSpec {
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

fn consume_companion_derives_role_trivia<E>(
    start: &DerivesAttachmentStart,
    allow_companion_handoff: bool,
    i: &mut SynIn<E>,
) where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    if any_ambient_owner_claims(i)
        || (allow_companion_handoff
            && recognize_declaration_companion_handoff(start.owner_base, i).is_some())
    {
        return;
    }
    let trivia = i.run(scan_trivia).expect("trivia is total");
    if derives_gap_is_caller_owned(start.owner_base, struct_trivia_has_newline(&trivia), i) {
        i.rollback(checkpoint);
    }
}

fn parse_companion_handoff_derives_role<'source, E>(
    start: &DerivesAttachmentStart,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if recognize_declaration_companion_handoff(start.owner_base, i).is_some() {
        return Recovered::Incomplete;
    }
    let episode = companion_derives_role_episode_spec(start, i);
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let role = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_handoff_recovery_isolated(
                    Some(episode.outer_role),
                    episode.policy,
                    |i| recognize_declaration_companion_handoff(start.owner_base, i).is_some(),
                    i,
                ),
            )
        }))
        .expect("the isolated companion-aware Derives RoleReference entry is total");
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

fn parse_companion_handoff_derives_via<'source, E>(
    start: &DerivesAttachmentStart,
    keyword: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DerivesVia<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    consume_companion_derives_role_trivia(start, true, i);
    let target = if let Some(target) = i.run(scan_word) {
        Recovered::Complete(target)
    } else {
        let episode = derives_via_target_episode(DerivesViaBoundary::companion(start), i);
        i.local.record_yumark_embedded_recovery(episode.fact);
        match episode.continuation {
            CanonicalRecoveryContinuation::RetrySameSlot => Recovered::Complete(
                i.run(scan_word)
                    .expect("the isolated ViaTarget retry leaves a raw word"),
            ),
            CanonicalRecoveryContinuation::StopAtBoundary => Recovered::Incomplete,
        }
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

pub(super) fn parse_derives_attachments_with_companion_handoff_isolated<'source, E>(
    first: DerivesAttachmentStart,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DerivesAttachmentsWithTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut attachments = Vec::new();
    let mut next_start = Some(first);
    let mut tail = None;
    while let Some(start) = next_start.take() {
        let leading = i
            .run(scan_trivia)
            .expect("the derives attachment gap is total");
        debug_assert_eq!(leading.range().end, start.keyword.start);
        let keyword = i
            .run(scan_word)
            .expect("an accepted derives attachment leaves its keyword");
        assert_eq!(keyword.range(), start.keyword);
        let mut roles = Vec::new();
        let (via, repeated) = loop {
            consume_companion_derives_role_trivia(&start, true, i);
            roles.push(parse_companion_handoff_derives_role(&start, i));
            match drive_companion_handoff_derives(&start, i) {
                CompanionDerivesDecision::Comma { leading, comma } => {
                    consume_derives_trivia(leading, i);
                    assert_eq!(scan_derives_comma(i), Some(comma));
                }
                CompanionDerivesDecision::Via { leading, keyword } => {
                    consume_derives_trivia(leading, i);
                    let consumed = i
                        .run(scan_word)
                        .expect("the isolated derives driver leaves via at the cursor");
                    assert_eq!(consumed.range(), keyword);
                    let via = parse_companion_handoff_derives_via(&start, keyword, i);
                    let repeated = match drive_companion_handoff_derives(&start, i) {
                        CompanionDerivesDecision::Repeated { leading, start } => {
                            consume_derives_trivia(leading, i);
                            Some(start)
                        }
                        CompanionDerivesDecision::Companion(found) => {
                            tail = Some(found);
                            None
                        }
                        _ => None,
                    };
                    break (Some(via), repeated);
                }
                CompanionDerivesDecision::Repeated { leading, start } => {
                    consume_derives_trivia(leading, i);
                    break (None, Some(start));
                }
                CompanionDerivesDecision::Companion(found) => {
                    tail = Some(found);
                    break (None, None);
                }
                CompanionDerivesDecision::Boundary | CompanionDerivesDecision::NoContinuation => {
                    break (None, None);
                }
            }
        };
        let end = i.pos();
        let clause_start = start.keyword.start;
        attachments.push(DerivesAttachment {
            position: start.position,
            clause: DerivesClause {
                keyword: start.keyword,
                roles,
                via,
                range: clause_start..end,
            },
        });
        next_start = repeated;
        if tail.is_some() {
            break;
        }
    }
    DerivesAttachmentsWithTail { attachments, tail }
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
    let (owner, position, owner_base, _) = spec
        .attachment_metadata()
        .expect("an attachment clause uses attachment driver metadata");
    assert_eq!(owner, start.owner);
    assert_eq!(position, start.position);
    assert_eq!(owner_base, start.owner_base);
    let (clause, repeated_start) = parse_derives_clause_core(
        DerivesClauseStart {
            keyword: start.keyword,
        },
        spec,
        i,
    );
    (
        DerivesAttachment { position, clause },
        repeated_start.map(|start| DerivesAttachmentStart {
            owner,
            position,
            keyword: start.keyword,
            owner_base,
        }),
    )
}

pub(super) fn recognize_declaration_companion_derives_start<E>(
    i: &mut SynIn<E>,
) -> Option<DerivesClauseStart>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.run(scan_word).and_then(|word| {
        (word.text() == "derives").then(|| DerivesClauseStart {
            keyword: word.range(),
        })
    });
    i.rollback(checkpoint);
    start
}

pub(super) fn parse_declaration_companion_derives_clause<'source, E>(
    start: DerivesClauseStart,
    spec: DerivesDriverSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (DerivesClause<'source>, Option<DerivesClauseStart>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    assert!(matches!(
        spec.context,
        DerivesDriverContext::DeclarationCompanion { .. }
    ));
    parse_derives_clause_core(start, spec, i)
}

fn parse_derives_clause_core<'source, E>(
    start: DerivesClauseStart,
    spec: DerivesDriverSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (DerivesClause<'source>, Option<DerivesClauseStart>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = i.run(scan_trivia).expect("the derives clause gap is total");
    debug_assert_eq!(leading.range().end, start.keyword.start);
    let keyword = i
        .run(scan_word)
        .expect("an accepted derives attachment start leaves its keyword at the cursor");
    assert_eq!(keyword.range(), start.keyword);
    debug_assert_eq!(keyword.text(), "derives");

    let mut roles = Vec::new();
    let (via, repeated_start) = loop {
        consume_derives_role_trivia(spec, i);
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
                        Some(DerivesClauseStart {
                            keyword: start.keyword,
                        })
                    }
                    DerivesDriverDecision::DeclarationCompanionRepeatedClause {
                        leading,
                        start,
                    } => {
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
                break (
                    None,
                    Some(DerivesClauseStart {
                        keyword: start.keyword,
                    }),
                );
            }
            DerivesDriverDecision::DeclarationCompanionRepeatedClause { leading, start } => {
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
        DerivesClause {
            keyword: start.keyword,
            roles,
            via,
            range: clause_start..end,
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

pub(super) fn consume_derives_role_trivia<E>(spec: DerivesDriverSpec, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    if matches!(
        spec.context,
        DerivesDriverContext::DeclarationCompanion { .. }
    ) && any_ambient_owner_claims(i)
    {
        return;
    }
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let caller_owned = match spec.context {
        DerivesDriverContext::Attachment { owner_base, .. } => {
            derives_gap_is_caller_owned(owner_base, struct_trivia_has_newline(&trivia), i)
        }
        DerivesDriverContext::DeclarationCompanion { layout } => {
            super::companion::declaration_companion_derives_mandatory_trivia_is_sequence_gap(
                layout, &trivia, i,
            )
        }
    };
    if caller_owned {
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
    consume_derives_role_trivia(spec, i);
    let target = if let Some(target) = i.run(scan_word) {
        Recovered::Complete(target)
    } else {
        let episode = derives_via_target_episode(DerivesViaBoundary::ordinary(spec), i);
        i.local.record_yumark_embedded_recovery(episode.fact);
        match episode.continuation {
            CanonicalRecoveryContinuation::RetrySameSlot => Recovered::Complete(
                i.run(scan_word)
                    .expect("ViaTarget retry leaves its raw word at the cursor"),
            ),
            CanonicalRecoveryContinuation::StopAtBoundary => Recovered::Incomplete,
        }
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct DirectDerivesAttachmentsWithTail {
    pub(super) attachments: Vec<DirectDerivesAttachment>,
    pub(super) tail: Option<DerivesDeclarationCompanionTail>,
}

fn commit_companion_derives_role_trivia<'parse, 'source, 'local, E, O>(
    start: &DerivesAttachmentStart,
    allow_companion_handoff: bool,
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
        if any_ambient_owner_claims(i)
            || (allow_companion_handoff
                && recognize_declaration_companion_handoff(start.owner_base, i).is_some())
        {
            return None;
        }
        let trivia = i.run(scan_trivia).expect("trivia is total");
        if derives_gap_is_caller_owned(start.owner_base, struct_trivia_has_newline(&trivia), i) {
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

fn emit_companion_derives_role_missing_at<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    at: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
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

fn commit_companion_handoff_derives_role<'parse, 'source, 'local, E, O>(
    start: &DerivesAttachmentStart,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode =
        committed.probe(|probe| companion_derives_role_episode_spec(start, probe.input()));
    if let Some(with) = committed
        .probe(|probe| recognize_declaration_companion_handoff(start.owner_base, probe.input()))
    {
        emit_companion_derives_role_missing_at(episode.outer_role, with.start, committed);
        return Recovered::Incomplete;
    }
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    });
    let role = commit_direct_type_expression_with_handoff_recovery_isolated(
        Some(episode.outer_role),
        episode.policy,
        |i| recognize_declaration_companion_handoff(start.owner_base, i).is_some(),
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
    let range = role.range();
    if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    }
}

fn commit_companion_handoff_derives_via<'parse, 'source, 'local, E, O>(
    start: &DerivesAttachmentStart,
    keyword: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> DirectDerivesVia
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_companion_derives_role_trivia(start, true, committed);
    let target = if let Some(target) = commit_word(committed) {
        let range = target.range();
        committed.token(SyntaxKind::Identifier, range.clone());
        Recovered::Complete(range)
    } else {
        let episode = committed.probe(|probe| {
            derives_via_target_episode(DerivesViaBoundary::companion(start), probe.input())
        });
        let continuation = episode.continuation;
        committed.emit_canonical_recovery_fact(episode.fact);
        match continuation {
            CanonicalRecoveryContinuation::RetrySameSlot => {
                let target =
                    commit_word(committed).expect("the isolated ViaTarget retry leaves a raw word");
                let range = target.range();
                committed.token(SyntaxKind::Identifier, range.clone());
                Recovered::Complete(range)
            }
            CanonicalRecoveryContinuation::StopAtBoundary => Recovered::Incomplete,
        }
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

pub(super) fn commit_derives_attachments_with_companion_handoff_isolated<
    'parse,
    'source,
    'local,
    E,
    O,
>(
    first: DerivesAttachmentStart,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> DirectDerivesAttachmentsWithTail
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut attachments = Vec::new();
    let mut next_start = Some(first);
    let mut tail = None;
    while let Some(start) = next_start.take() {
        committed.start_node(SyntaxKind::DerivesClause);
        let leading = committed
            .probe(|probe| probe.input().run(scan_trivia))
            .expect("the derives attachment gap is total");
        debug_assert_eq!(leading.range().end, start.keyword.start);
        committed.emit_trivia(&leading);
        let keyword =
            commit_word(committed).expect("an accepted derives attachment leaves its keyword");
        assert_eq!(keyword.range(), start.keyword);
        committed.token(SyntaxKind::DerivesKw, keyword.range());
        let mut roles = Vec::new();
        let (via, repeated) = loop {
            commit_companion_derives_role_trivia(&start, true, committed);
            roles.push(commit_companion_handoff_derives_role(&start, committed));
            match committed.probe(|probe| drive_companion_handoff_derives(&start, probe.input())) {
                CompanionDerivesDecision::Comma { leading, comma } => {
                    commit_derives_trivia(leading, committed);
                    let consumed = committed
                        .probe(|probe| scan_derives_comma(probe.input()))
                        .expect("the isolated derives driver leaves its comma");
                    assert_eq!(consumed, comma);
                    committed.token(SyntaxKind::Comma, consumed);
                }
                CompanionDerivesDecision::Via { leading, keyword } => {
                    commit_derives_trivia(leading, committed);
                    let consumed = commit_word(committed)
                        .expect("the isolated derives driver leaves via at the cursor");
                    assert_eq!(consumed.range(), keyword);
                    committed.token(SyntaxKind::ViaKw, consumed.range());
                    let via = commit_companion_handoff_derives_via(&start, keyword, committed);
                    let repeated = match committed
                        .probe(|probe| drive_companion_handoff_derives(&start, probe.input()))
                    {
                        CompanionDerivesDecision::Repeated { leading, start } => {
                            commit_derives_trivia(leading, committed);
                            Some(start)
                        }
                        CompanionDerivesDecision::Companion(found) => {
                            tail = Some(found);
                            None
                        }
                        _ => None,
                    };
                    break (Some(via), repeated);
                }
                CompanionDerivesDecision::Repeated { leading, start } => {
                    commit_derives_trivia(leading, committed);
                    break (None, Some(start));
                }
                CompanionDerivesDecision::Companion(found) => {
                    tail = Some(found);
                    break (None, None);
                }
                CompanionDerivesDecision::Boundary | CompanionDerivesDecision::NoContinuation => {
                    break (None, None);
                }
            }
        };
        let end = committed_position(committed);
        committed.finish_node();
        attachments.push(DirectDerivesAttachment {
            position: start.position,
            clause: DirectDerivesClause {
                keyword: start.keyword.clone(),
                roles,
                via,
                range: start.keyword.start..end,
            },
        });
        next_start = repeated;
        if tail.is_some() {
            break;
        }
    }
    DirectDerivesAttachmentsWithTail { attachments, tail }
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
    let (owner, position, owner_base, _) = spec
        .attachment_metadata()
        .expect("an attachment clause uses attachment driver metadata");
    assert_eq!(owner, start.owner);
    assert_eq!(position, start.position);
    assert_eq!(owner_base, start.owner_base);
    let (clause, repeated_start) = commit_derives_clause_core::<true, _, _>(
        DerivesClauseStart {
            keyword: start.keyword,
        },
        spec,
        committed,
    );
    (
        DirectDerivesAttachment {
            position,
            clause: clause.expect("the attachment direct clause retains its summary"),
        },
        repeated_start.map(|start| DerivesAttachmentStart {
            owner,
            position,
            keyword: start.keyword,
            owner_base,
        }),
    )
}

pub(super) fn commit_declaration_companion_derives_clause<'parse, 'source, 'local, E, O>(
    start: DerivesClauseStart,
    spec: DerivesDriverSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<DerivesClauseStart>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    assert!(matches!(
        spec.context,
        DerivesDriverContext::DeclarationCompanion { .. }
    ));
    commit_derives_clause_core::<false, _, _>(start, spec, committed).1
}

fn commit_derives_clause_core<'parse, 'source, 'local, const RETAIN: bool, E, O>(
    start: DerivesClauseStart,
    spec: DerivesDriverSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> (Option<DirectDerivesClause>, Option<DerivesClauseStart>)
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
        commit_derives_role_trivia(spec, committed);
        let role = commit_required_derives_role(spec, committed);
        if RETAIN {
            roles.push(role);
        }
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
                            Some(DerivesClauseStart {
                                keyword: start.keyword,
                            })
                        }
                        DerivesDriverDecision::DeclarationCompanionRepeatedClause {
                            leading,
                            start,
                        } => {
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
                break (
                    None,
                    Some(DerivesClauseStart {
                        keyword: start.keyword,
                    }),
                );
            }
            DerivesDriverDecision::DeclarationCompanionRepeatedClause { leading, start } => {
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
        RETAIN.then(|| DirectDerivesClause {
            keyword: start.keyword,
            roles,
            via,
            range: clause_start..end,
        }),
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
    spec: DerivesDriverSpec,
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
        if matches!(
            spec.context,
            DerivesDriverContext::DeclarationCompanion { .. }
        ) && any_ambient_owner_claims(i)
        {
            return None;
        }
        let trivia = i.run(scan_trivia).expect("trivia is total");
        let caller_owned = match spec.context {
            DerivesDriverContext::Attachment { owner_base, .. } => {
                derives_gap_is_caller_owned(owner_base, struct_trivia_has_newline(&trivia), i)
            }
            DerivesDriverContext::DeclarationCompanion { layout } => {
                super::companion::declaration_companion_derives_mandatory_trivia_is_sequence_gap(
                    layout, &trivia, i,
                )
            }
        };
        if caller_owned {
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
    commit_derives_role_trivia(spec, committed);
    let target = if let Some(target) = commit_word(committed) {
        let range = target.range();
        committed.token(SyntaxKind::Identifier, range.clone());
        Recovered::Complete(range)
    } else {
        let episode = committed.probe(|probe| {
            derives_via_target_episode(DerivesViaBoundary::ordinary(spec), probe.input())
        });
        let continuation = episode.continuation;
        committed.emit_canonical_recovery_fact(episode.fact);
        match continuation {
            CanonicalRecoveryContinuation::RetrySameSlot => {
                let target = commit_word(committed)
                    .expect("ViaTarget retry leaves its raw word at the cursor");
                let range = target.range();
                committed.token(SyntaxKind::Identifier, range.clone());
                Recovered::Complete(range)
            }
            CanonicalRecoveryContinuation::StopAtBoundary => Recovered::Incomplete,
        }
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum DerivesViaBoundary {
    Ordinary {
        spec: DerivesDriverSpec,
    },
    Companion {
        spec: DerivesDriverSpec,
        owner_base: usize,
    },
}

impl DerivesViaBoundary {
    fn ordinary(spec: DerivesDriverSpec) -> Self {
        Self::Ordinary { spec }
    }

    fn companion(start: &DerivesAttachmentStart) -> Self {
        Self::Companion {
            spec: DerivesDriverSpec::new(start.owner, start.position, start.owner_base),
            owner_base: start.owner_base,
        }
    }

    fn pending<E>(self, i: &mut SynIn<E>) -> bool
    where
        E: ErrorSink<usize>,
        Unexpected<char>: Into<E::Error>,
        UnexpectedEndOfInput: Into<E::Error>,
    {
        match self {
            Self::Ordinary { spec } => derives_via_boundary_pending(spec, i),
            Self::Companion { spec, owner_base } => {
                recognize_declaration_companion_handoff(owner_base, i).is_some()
                    || derives_via_boundary_pending(spec, i)
            }
        }
    }
}

fn derives_via_target_recovery_fact(
    range: Range<usize>,
    kind: RecoveryKind,
) -> YumarkEmbeddedRecoveryFact {
    YumarkEmbeddedRecoveryFact {
        spec: RecoverySiteSpec {
            role: GrammarRole::Declaration(DeclarationRole::Derives(DerivesRole::ViaTarget)),
            expected: ExpectedSyntax::Identifier,
        },
        range,
        kind,
        unexpected: (kind == RecoveryKind::Error).then_some(UnexpectedCategory::OtherCharacter),
    }
}

fn derives_via_target_episode<E>(
    boundary: DerivesViaBoundary,
    i: &mut SynIn<E>,
) -> CanonicalRecoveryEpisode
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if boundary.pending(i) {
            let kind = if start < i.pos() {
                RecoveryKind::Error
            } else {
                RecoveryKind::Missing
            };
            return CanonicalRecoveryEpisode {
                fact: derives_via_target_recovery_fact(start..i.pos(), kind),
                continuation: CanonicalRecoveryContinuation::StopAtBoundary,
            };
        }
        if start < i.pos() && derives_via_raw_identifier_pending(i) {
            return CanonicalRecoveryEpisode {
                fact: derives_via_target_recovery_fact(start..i.pos(), RecoveryKind::Error),
                continuation: CanonicalRecoveryContinuation::RetrySameSlot,
            };
        }
        let Some(character) = i.input.remainder().chars().next() else {
            let kind = if start < i.pos() {
                RecoveryKind::Error
            } else {
                RecoveryKind::Missing
            };
            return CanonicalRecoveryEpisode {
                fact: derives_via_target_recovery_fact(start..i.pos(), kind),
                continuation: CanonicalRecoveryContinuation::StopAtBoundary,
            };
        };
        if matches!(character, '\r' | '\n') {
            let kind = if start < i.pos() {
                RecoveryKind::Error
            } else {
                RecoveryKind::Missing
            };
            return CanonicalRecoveryEpisode {
                fact: derives_via_target_recovery_fact(start..i.pos(), kind),
                continuation: CanonicalRecoveryContinuation::StopAtBoundary,
            };
        }
        i.input
            .next()
            .expect("the ViaTarget recovery unit remains available");
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
