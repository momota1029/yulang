//! One streaming judge for both polymorphic-variant output paths.
//!
//! The driver owns the NT/IT ordering and required-slot state.  Contexts only
//! realize accepted events as AST values or direct CST output.

use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum TagPosition {
    Optional,
    AfterTag,
    Required {
        filled: bool,
        last_comma: Option<Range<usize>>,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TagJudgeOrigin {
    /// The opener, an explicit comma, or an already-authorized local layout
    /// boundary has opened exactly one tag head.  ASOB must not re-judge it.
    FreshLocalHead {
        /// Opener/comma authority also keeps a live companion spelling local.
        /// A locally committed implicit boundary has already queried ASOB and
        /// must not query it again from the post-newline position.
        companion_spelling_is_local: bool,
    },
    /// A completed/recovered tag or a local recovery episode is handing the
    /// still-unconsumed gap back to NT.
    ContinuationOrRecovery,
}

enum GapBoundary {
    None,
    SameLine(TriviaRun),
    QualifyingNewline(TriviaRun),
    Owner,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum TagBoundary {
    Close,
    Comma(Range<usize>),
    QualifyingNewline,
    Owner,
}

struct TagTransition {
    next: TagPosition,
    emit_missing: bool,
    trailing_comma: Option<Range<usize>>,
}

fn transition(position: &TagPosition, boundary: TagBoundary) -> TagTransition {
    match boundary {
        TagBoundary::Close => TagTransition {
            next: position.clone(),
            emit_missing: false,
            trailing_comma: match position {
                TagPosition::Required {
                    filled: false,
                    last_comma,
                } => last_comma.clone(),
                _ => None,
            },
        },
        TagBoundary::Comma(comma) => {
            let emit_missing = !matches!(position, TagPosition::AfterTag);
            TagTransition {
                next: TagPosition::Required {
                    filled: emit_missing,
                    last_comma: Some(comma),
                },
                emit_missing,
                trailing_comma: None,
            }
        }
        TagBoundary::QualifyingNewline => TagTransition {
            next: if matches!(position, TagPosition::AfterTag) {
                TagPosition::Required {
                    filled: false,
                    last_comma: None,
                }
            } else {
                position.clone()
            },
            emit_missing: false,
            trailing_comma: None,
        },
        TagBoundary::Owner => TagTransition {
            next: position.clone(),
            emit_missing: matches!(position, TagPosition::Required { filled: false, .. }),
            trailing_comma: None,
        },
    }
}

enum PayloadJudge {
    Outer,
    Candidate {
        boundary_start: usize,
        trivia: TriviaRun,
    },
    Malformed {
        boundary_start: usize,
        trivia: TriviaRun,
        range: Range<usize>,
        retry: bool,
    },
    None,
}

#[derive(Clone)]
enum PayloadIssue {
    Boundary(Range<usize>),
    Type(Range<usize>),
}

trait VariantContext<'source> {
    type Error: ErrorSink<usize>;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, Self::Error>) -> R)
    -> R;
    fn begin_type_expression_episode(&mut self) -> usize;
    fn end_type_expression_episode(&mut self, episode_depth: usize);
    fn emit_trivia(&mut self, trivia: &TriviaRun);
    fn emit_missing_tag(&mut self);
    fn emit_comma(&mut self, comma: Range<usize>);
    fn emit_separator_error(&mut self, semicolon: Range<usize>);
    fn emit_close_error(&mut self, range: Range<usize>);
    fn emit_close(&mut self, close: Range<usize>);
    fn emit_missing_close(&mut self);
    fn set_trailing_comma(&mut self, comma: Range<usize>);
    fn begin_tag(&mut self, malformed: Option<Range<usize>>);
    fn accept_tag_head(&mut self, primary: TypePrimary<'source>);
    fn finish_tag(&mut self, complete: bool);
    fn begin_payload(
        &mut self,
        boundary: Recovered<Range<usize>>,
        trivia: &TriviaRun,
        issue: Option<PayloadIssue>,
    );
    fn consume_payload_type(&mut self) -> bool;
    fn finish_payload(&mut self);
}

/// The variant judge retains ownership of tag-position transitions.  Once it
/// yields its close slot, this adapter delegates only close retry/termination
/// to the common delimited-close driver.
struct VariantCloseSlotContext<'context, C> {
    context: &'context mut C,
}

impl<'source, C> TypeCloseSlotContext<'source> for VariantCloseSlotContext<'_, C>
where
    C: VariantContext<'source>,
{
    type Error = C::Error;

    fn with_input<R>(
        &mut self,
        f: impl FnOnce(&mut SynIn<'_, 'source, '_, Self::Error>) -> R,
    ) -> R {
        self.context.with_input(f)
    }

    fn emit_close_trivia(&mut self, trivia: &TriviaRun) {
        self.context.emit_trivia(trivia);
    }

    fn emit_matching_close(&mut self, _kind: SyntaxKind, range: Range<usize>) {
        self.context.emit_close(range);
    }

    fn emit_mismatched_close(
        &mut self,
        _role: GrammarRole,
        range: Range<usize>,
        _expected: ExpectedSyntax,
    ) {
        self.context.emit_close_error(range);
    }

    fn emit_missing_close(&mut self, _role: GrammarRole, _expected: ExpectedSyntax) {
        self.context.emit_missing_close();
    }
}

pub(super) fn parse<'source, E>(
    colon: Range<usize>,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> PolymorphicVariantType<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = colon.start;
    let mut context = AstContext::new(i);
    let (layout, stops) = enter_variant(&mut context);
    drive(&mut context, layout);
    leave_variant(&mut context, layout, stops);
    let end = if let Some(close) = &context.close {
        close.end
    } else {
        context.with_input(|i| i.pos())
    };
    PolymorphicVariantType {
        colon,
        open,
        tags: context.tags,
        trailing_comma: context.trailing_comma,
        close: context
            .close
            .map_or(Recovered::Incomplete, Recovered::Complete),
        range: start..end,
    }
}

pub(super) fn commit_direct<'parse, 'source, 'local, E, O>(
    colon: Range<usize>,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::PolymorphicVariantType);
    committed.token(SyntaxKind::Colon, colon);
    committed.token(SyntaxKind::LBrace, open);
    let mut context = DirectContext { committed };
    let (layout, stops) = enter_variant(&mut context);
    let closed = drive(&mut context, layout);
    leave_variant(&mut context, layout, stops);
    context.committed.finish_node();
    closed
}

fn enter_variant<'source, C>(context: &mut C) -> (LayoutDelimitedFrame, StopSet)
where
    C: VariantContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    let incoming = context.with_input(|i| {
        i.local
            .indentation_baseline()
            .map_or(0, |baseline| baseline.column)
    });
    let stops = context.with_input(|i| {
        let stops = active_stop_set(i)
            .with(StopKind::Comma)
            .with(StopKind::RightBrace);
        i.local.push_delimiter(Delimiter::Brace);
        i.local.push_stop_set(stops);
        i.local
            .push_type_delimited_owner(TypeDelimitedOwner::PolymorphicVariant);
        stops
    });
    let opening = context.with_input(consume_trivia);
    context.emit_trivia(&opening);
    let layout = context.with_input(|i| {
        LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, i.local.line().line_indent)
    });
    context.with_input(|i| push_layout(layout, i));
    (layout, stops)
}

fn leave_variant<'source, C>(context: &mut C, layout: LayoutDelimitedFrame, stops: StopSet)
where
    C: VariantContext<'source>,
{
    context.with_input(|i| {
        pop_layout(layout, i);
        assert_eq!(
            i.local.pop_type_delimited_owner(),
            Some(TypeDelimitedOwner::PolymorphicVariant),
        );
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    });
}

fn drive<'source, C>(context: &mut C, layout: LayoutDelimitedFrame) -> bool
where
    C: VariantContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    let mut position = TagPosition::Optional;
    let mut origin = TagJudgeOrigin::FreshLocalHead {
        companion_spelling_is_local: true,
    };
    let mut closed = false;
    loop {
        if let Some(close) = context.with_input(scan_close_brace) {
            let outcome = transition(&position, TagBoundary::Close);
            if let Some(comma) = outcome.trailing_comma {
                context.set_trailing_comma(comma);
            }
            context.emit_close(close);
            closed = true;
            break;
        }
        if let Some(mismatched) =
            context.with_input(|i| scan_mismatched_close_for(Delimiter::Brace, i))
        {
            context.emit_close_error(mismatched);
            origin = TagJudgeOrigin::ContinuationOrRecovery;
            continue;
        }
        if let Some(comma) = context.with_input(scan_record_comma) {
            let outcome = transition(&position, TagBoundary::Comma(comma.clone()));
            if outcome.emit_missing {
                context.emit_missing_tag();
            }
            context.emit_comma(comma);
            position = outcome.next;
            origin = TagJudgeOrigin::FreshLocalHead {
                companion_spelling_is_local: true,
            };
            continue;
        }
        if context.with_input(exact_semicolon_pending) {
            let caller_owns = context
                .with_input(|i| type_stop_is_active_in_current_episode(i, StopKind::Semicolon));
            if caller_owns {
                apply_owner_transition(&position, context);
                break;
            }
            let semicolon = context
                .with_input(scan_record_semicolon)
                .expect("the exact semicolon probe accepted a semicolon");
            context.emit_separator_error(semicolon);
            origin = TagJudgeOrigin::ContinuationOrRecovery;
            continue;
        }

        if matches!(origin, TagJudgeOrigin::ContinuationOrRecovery)
            && context.with_input(any_ambient_owner_claims)
        {
            apply_owner_transition(&position, context);
            break;
        }

        match context.with_input(|i| classify_tag_boundary(layout, origin, i)) {
            GapBoundary::SameLine(trivia) => {
                let consumed = context.with_input(consume_trivia);
                debug_assert_eq!(consumed.range(), trivia.range());
                context.emit_trivia(&consumed);
                if matches!(origin, TagJudgeOrigin::ContinuationOrRecovery) {
                    origin = TagJudgeOrigin::FreshLocalHead {
                        companion_spelling_is_local: false,
                    };
                }
                continue;
            }
            GapBoundary::QualifyingNewline(trivia) => {
                let consumed = context.with_input(consume_trivia);
                debug_assert_eq!(consumed.range(), trivia.range());
                context.emit_trivia(&consumed);
                position = transition(&position, TagBoundary::QualifyingNewline).next;
                if matches!(origin, TagJudgeOrigin::ContinuationOrRecovery) {
                    origin = TagJudgeOrigin::FreshLocalHead {
                        companion_spelling_is_local: false,
                    };
                }
                continue;
            }
            GapBoundary::Owner => {
                apply_owner_transition(&position, context);
                break;
            }
            GapBoundary::None => {}
        }

        if let Some(primary) = context.with_input(|i| parse_tag_primary(origin, i)) {
            context.begin_tag(None);
            context.accept_tag_head(primary);
            drive_payloads(context);
            context.finish_tag(true);
            position = TagPosition::AfterTag;
            origin = TagJudgeOrigin::ContinuationOrRecovery;
            continue;
        }
        if context.with_input(type_recovery_boundary_pending) {
            apply_owner_transition(&position, context);
            break;
        }
        if let Some(range) = context.with_input(consume_invalid_run) {
            context.begin_tag(Some(range));
            let ambient_retry = context.with_input(any_ambient_owner_claims);
            if !ambient_retry
                && let Some(primary) =
                    context.with_input(|i| parse_type_primary_in_context(true, i))
            {
                context.accept_tag_head(primary);
                drive_payloads(context);
                context.finish_tag(true);
            } else {
                context.finish_tag(false);
            }
            position = TagPosition::AfterTag;
            origin = TagJudgeOrigin::ContinuationOrRecovery;
            continue;
        }
        apply_owner_transition(&position, context);
        break;
    }

    if !closed {
        let close = drive_type_close_slot(
            &mut VariantCloseSlotContext { context },
            CloseRecoverySpec {
                delimiter: Delimiter::Brace,
                owner: ConstructRole::PolymorphicVariantType,
                matching_kind: SyntaxKind::RBrace,
                missing_after_mismatch: MissingAfterMismatch::Emit,
            },
        );
        closed = matches!(close, Recovered::Complete(_));
    }
    closed
}

fn drive_payloads<'source, C>(context: &mut C)
where
    C: VariantContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    loop {
        let episode_depth = context.begin_type_expression_episode();
        match context.with_input(inspect_payload) {
            PayloadJudge::Outer | PayloadJudge::None => {
                context.end_type_expression_episode(episode_depth);
                break;
            }
            PayloadJudge::Candidate {
                boundary_start,
                trivia,
            } => {
                let consumed = context.with_input(consume_trivia);
                debug_assert_eq!(consumed.range(), trivia.range());
                let boundary = if trivia.is_empty() {
                    Recovered::Incomplete
                } else {
                    Recovered::Complete(boundary_start..context.with_input(|i| i.pos()))
                };
                context.begin_payload(boundary, &consumed, None);
                assert!(context.consume_payload_type());
                context.finish_payload();
                context.end_type_expression_episode(episode_depth);
            }
            PayloadJudge::Malformed {
                boundary_start,
                trivia,
                range,
                retry,
            } => {
                let consumed_trivia = context.with_input(consume_trivia);
                debug_assert_eq!(consumed_trivia.range(), trivia.range());
                let consumed_range = context.with_input(consume_invalid_run);
                debug_assert_eq!(consumed_range, Some(range.clone()));
                let boundary = if trivia.is_empty() {
                    Recovered::Incomplete
                } else {
                    Recovered::Complete(boundary_start..range.start)
                };
                let issue = if trivia.is_empty() {
                    PayloadIssue::Boundary(range)
                } else {
                    PayloadIssue::Type(range)
                };
                context.begin_payload(boundary, &consumed_trivia, Some(issue));
                if retry {
                    assert!(context.consume_payload_type());
                }
                context.finish_payload();
                context.end_type_expression_episode(episode_depth);
                if !retry {
                    break;
                }
            }
        }
    }
}

fn inspect_payload<E>(i: &mut SynIn<E>) -> PayloadJudge
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return PayloadJudge::Outer;
    }
    let checkpoint = i.checkpoint();
    let boundary_start = i.pos();
    let trivia = consume_trivia(i);
    let judge = if trivia_has_newline(&trivia) || payload_outer_boundary(i) {
        PayloadJudge::Outer
    } else if type_primary_candidate(i) {
        PayloadJudge::Candidate {
            boundary_start,
            trivia,
        }
    } else if let Some(range) = consume_invalid_run(i) {
        let retry = type_primary_candidate(i);
        let ambient_retry = retry && any_ambient_owner_claims(i);
        if trivia.is_empty() && (!retry || ambient_retry) {
            PayloadJudge::None
        } else {
            PayloadJudge::Malformed {
                boundary_start,
                trivia,
                range,
                retry: retry && !ambient_retry,
            }
        }
    } else {
        PayloadJudge::None
    };
    i.rollback(checkpoint);
    judge
}

fn apply_owner_transition<'source, C>(position: &TagPosition, context: &mut C)
where
    C: VariantContext<'source>,
{
    if transition(position, TagBoundary::Owner).emit_missing {
        context.emit_missing_tag();
    }
}

fn classify_tag_boundary<E>(
    layout: LayoutDelimitedFrame,
    origin: TagJudgeOrigin,
    i: &mut SynIn<E>,
) -> GapBoundary
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = consume_trivia(i);
    let boundary = if trivia.is_empty() {
        owner_boundary_pending(origin, i).then_some(GapBoundary::Owner)
    } else if trivia_has_newline(&trivia) {
        // A local tag head owns a qualifying newline even if an enclosing
        // type slot happens to carry `StopKind::Newline`.  A matching local
        // close remains different: that whole newline gap belongs to the
        // caller's close recovery and must stay intact.
        let caller_owns_local_close = type_stop_is_active_in_current_episode(i, StopKind::Newline)
            && scan_close_brace(i).is_some();
        if !caller_owns_local_close
            && layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
                == LayoutDelimitedBoundary::ImplicitNewline
        {
            Some(GapBoundary::QualifyingNewline(trivia))
        } else {
            Some(GapBoundary::Owner)
        }
    } else if owner_boundary_pending(origin, i) {
        Some(GapBoundary::Owner)
    } else {
        Some(GapBoundary::SameLine(trivia))
    };
    i.rollback(checkpoint);
    boundary.unwrap_or(GapBoundary::None)
}

fn owner_boundary_pending<E>(origin: TagJudgeOrigin, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let local_stops = StopSet::default()
        .with(StopKind::Comma)
        .with(StopKind::RightBrace);
    let boundary = classify_type_boundary(
        TypeBoundaryPolicy {
            matching_close: Some(Delimiter::Brace),
            local_separators: StopSet::default().with(StopKind::Comma),
            locally_owned_stops: local_stops,
        },
        i,
    );
    if matches!(
        origin,
        TagJudgeOrigin::FreshLocalHead {
            companion_spelling_is_local: true,
        }
    ) && matches!(
            boundary,
            Some(TypeBoundary::ActiveStop(StopKind::Elsif | StopKind::Else))
    ) && any_ambient_owner_claims(i)
    {
        return false;
    }
    matches!(
        boundary,
        Some(TypeBoundary::Eof | TypeBoundary::ActiveStop(_) | TypeBoundary::OuterOwnedClose)
    )
}

fn parse_tag_primary<'source, E>(
    origin: TagJudgeOrigin,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<TypePrimary<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let opener_or_comma_owns_companion = matches!(
        origin,
        TagJudgeOrigin::FreshLocalHead {
            companion_spelling_is_local: true,
        }
    ) && any_ambient_owner_claims(i);
    if !opener_or_comma_owns_companion {
        return parse_type_primary_in_context(true, i);
    }

    let stops = active_stop_set(i)
        .without(StopKind::Elsif)
        .without(StopKind::Else);
    i.local.push_stop_set(stops);
    let primary = parse_type_primary_in_context(true, i);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    primary
}

fn exact_semicolon_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_record_semicolon(i).is_some();
    i.rollback(checkpoint);
    pending
}

fn payload_outer_boundary<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    type_recovery_boundary_pending(i)
}

fn consume_invalid_run<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_type_item_invalid_run_with(
        i,
        type_primary_candidate,
        |_| false,
        payload_outer_boundary,
        |i| type_item_boundary_after_trivia(i, payload_outer_boundary),
    )
    .map(|(range, _)| range)
}

struct AstTag<'source> {
    name: Recovered<WordSpan<'source>>,
    payloads: Vec<Recovered<PolymorphicVariantPayload<'source>>>,
    start: usize,
    head_end: usize,
}

struct AstPayload<'source> {
    boundary: Recovered<Range<usize>>,
    type_expr: Recovered<Box<TypeExpression<'source>>>,
    start: usize,
    fallback_end: usize,
}

struct AstContext<'context, 'parse, 'source, 'local, E: ErrorSink<usize>> {
    i: &'context mut SynIn<'parse, 'source, 'local, E>,
    tags: Vec<Recovered<PolymorphicVariantTag<'source>>>,
    trailing_comma: Option<Range<usize>>,
    close: Option<Range<usize>>,
    current_tag: Option<AstTag<'source>>,
    current_payload: Option<AstPayload<'source>>,
}

impl<'context, 'parse, 'source, 'local, E: ErrorSink<usize>>
    AstContext<'context, 'parse, 'source, 'local, E>
{
    fn new(i: &'context mut SynIn<'parse, 'source, 'local, E>) -> Self {
        Self {
            i,
            tags: Vec::new(),
            trailing_comma: None,
            close: None,
            current_tag: None,
            current_payload: None,
        }
    }
}

impl<'source, E> VariantContext<'source> for AstContext<'_, '_, 'source, '_, E>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    fn begin_type_expression_episode(&mut self) -> usize {
        self.i
            .local
            .push_type_expression_episode(TypeExpressionEpisodePolicy::default())
    }

    fn end_type_expression_episode(&mut self, episode_depth: usize) {
        assert_eq!(
            self.i.local.pop_type_expression_episode(),
            Some(TypeExpressionEpisodePolicy::default()),
        );
        debug_assert_eq!(
            self.i.local.type_expression_episode_depth() + 1,
            episode_depth
        );
    }

    type Error = E;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, E>) -> R) -> R {
        f(self.i)
    }

    fn emit_trivia(&mut self, _trivia: &TriviaRun) {}

    fn emit_missing_tag(&mut self) {
        self.tags.push(Recovered::Incomplete);
    }

    fn emit_comma(&mut self, _comma: Range<usize>) {}
    fn emit_separator_error(&mut self, _semicolon: Range<usize>) {}
    fn emit_close_error(&mut self, _range: Range<usize>) {}

    fn emit_close(&mut self, close: Range<usize>) {
        self.close = Some(close);
    }

    fn emit_missing_close(&mut self) {}

    fn set_trailing_comma(&mut self, comma: Range<usize>) {
        self.trailing_comma = Some(comma);
    }

    fn begin_tag(&mut self, malformed: Option<Range<usize>>) {
        let (start, head_end) = malformed.map_or((self.i.pos(), self.i.pos()), |range| {
            (range.start, range.end)
        });
        self.current_tag = Some(AstTag {
            name: Recovered::Incomplete,
            payloads: Vec::new(),
            start,
            head_end,
        });
    }

    fn accept_tag_head(&mut self, primary: TypePrimary<'source>) {
        let range = primary_range(&primary);
        let tag = self
            .current_tag
            .as_mut()
            .expect("tag head requires an open tag");
        if tag.start == tag.head_end {
            tag.start = range.start;
        }
        tag.head_end = range.end;
        if let TypePrimary::Atom(TypeAtom::Identifier(name)) = primary {
            tag.name = Recovered::Complete(name);
        }
    }

    fn finish_tag(&mut self, complete: bool) {
        let tag = self.current_tag.take().expect("finishing an unopened tag");
        if !complete {
            self.tags.push(Recovered::Incomplete);
            return;
        }
        let end = tag
            .payloads
            .last()
            .and_then(|payload| match payload {
            Recovered::Complete(payload) => Some(payload.range.end),
            Recovered::Incomplete => None,
            })
            .unwrap_or(tag.head_end);
        self.tags.push(Recovered::Complete(PolymorphicVariantTag {
            name: tag.name,
            payloads: tag.payloads,
            range: tag.start..end,
        }));
    }

    fn begin_payload(
        &mut self,
        boundary: Recovered<Range<usize>>,
        _trivia: &TriviaRun,
        issue: Option<PayloadIssue>,
    ) {
        let current = self.i.pos();
        let start = match &boundary {
            Recovered::Complete(range) => range.start,
            Recovered::Incomplete => match &issue {
                Some(PayloadIssue::Boundary(range)) => range.start,
                _ => current,
            },
        };
        let fallback_end = issue.as_ref().map_or(current, |issue| match issue {
            PayloadIssue::Boundary(range) | PayloadIssue::Type(range) => range.end,
        });
        self.current_payload = Some(AstPayload {
            boundary,
            type_expr: Recovered::Incomplete,
            start,
            fallback_end,
        });
    }

    fn consume_payload_type(&mut self) -> bool {
        let saved = self.i.local.type_ml_arg();
        self.i.local.set_type_ml_arg(true);
        let value = parse_type_expression_in_current_episode(false, self.i);
        self.i.local.set_type_ml_arg(saved);
        if let Some(value) = value {
            self.current_payload
                .as_mut()
                .expect("payload type requires an open payload")
                .type_expr = Recovered::Complete(Box::new(value));
            true
        } else {
            false
        }
    }

    fn finish_payload(&mut self) {
        let payload = self
            .current_payload
            .take()
            .expect("finishing an unopened payload");
        let end = match &payload.type_expr {
            Recovered::Complete(type_expr) => type_expr.range.end,
            Recovered::Incomplete => payload.fallback_end,
        };
        self.current_tag
            .as_mut()
            .expect("payload requires an open tag")
            .payloads
            .push(Recovered::Complete(PolymorphicVariantPayload {
                boundary: payload.boundary,
                type_expr: payload.type_expr,
                range: payload.start..end,
            }));
    }
}

struct DirectContext<
    'context,
    'parse,
    'source,
    'local,
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
> {
    committed: &'context mut Committed<'parse, 'source, 'local, E, O>,
}

impl<'source, E, O> VariantContext<'source> for DirectContext<'_, '_, 'source, '_, E, O>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    fn begin_type_expression_episode(&mut self) -> usize {
        self.with_input(|i| {
            i.local
                .push_type_expression_episode(TypeExpressionEpisodePolicy::default())
        })
    }

    fn end_type_expression_episode(&mut self, episode_depth: usize) {
        assert_eq!(
            self.with_input(|i| i.local.pop_type_expression_episode()),
            Some(TypeExpressionEpisodePolicy::default()),
        );
        debug_assert_eq!(
            self.with_input(|i| i.local.type_expression_episode_depth()) + 1,
            episode_depth,
        );
    }

    type Error = E;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, E>) -> R) -> R {
        self.committed.probe(|probe| f(probe.input()))
    }

    fn emit_trivia(&mut self, trivia: &TriviaRun) {
        self.committed.emit_trivia(trivia);
    }

    fn emit_missing_tag(&mut self) {
        self.committed.start_node(SyntaxKind::PolymorphicVariantTag);
        emit_type_missing(
            self.committed,
            GrammarRole::Type(TypeRole::PolymorphicVariantTag),
            ExpectedSyntax::Identifier,
        );
        self.committed.finish_node();
    }

    fn emit_comma(&mut self, comma: Range<usize>) {
        self.committed.token(SyntaxKind::Comma, comma);
    }

    fn emit_separator_error(&mut self, semicolon: Range<usize>) {
        emit_type_error(
            self.committed,
            TypeRole::PolymorphicVariantTagSeparator,
            semicolon,
            ExpectedSyntax::DelimitedSequenceSeparator,
        );
    }

    fn emit_close_error(&mut self, range: Range<usize>) {
        emit_error_with_role(
            self.committed,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::PolymorphicVariantType,
                delimiter: Delimiter::Brace,
            },
            range,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
        );
    }

    fn emit_close(&mut self, close: Range<usize>) {
        self.committed.token(SyntaxKind::RBrace, close);
    }

    fn emit_missing_close(&mut self) {
        emit_type_missing(
            self.committed,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::PolymorphicVariantType,
                delimiter: Delimiter::Brace,
            },
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
        );
    }

    fn set_trailing_comma(&mut self, _comma: Range<usize>) {}

    fn begin_tag(&mut self, malformed: Option<Range<usize>>) {
        self.committed.start_node(SyntaxKind::PolymorphicVariantTag);
        if let Some(range) = malformed {
            emit_type_error(
                self.committed,
                TypeRole::PolymorphicVariantTag,
                range,
                ExpectedSyntax::Identifier,
            );
        }
    }

    fn accept_tag_head(&mut self, primary: TypePrimary<'source>) {
        match primary {
            TypePrimary::Atom(TypeAtom::Identifier(name)) => {
                self.committed.token(SyntaxKind::Identifier, name.range());
            }
            primary => emit_type_error(
                self.committed,
                TypeRole::PolymorphicVariantTagName,
                primary_range(&primary),
                ExpectedSyntax::Identifier,
            ),
        }
    }

    fn finish_tag(&mut self, _complete: bool) {
        self.committed.finish_node();
    }

    fn begin_payload(
        &mut self,
        boundary: Recovered<Range<usize>>,
        trivia: &TriviaRun,
        issue: Option<PayloadIssue>,
    ) {
        self.committed
            .start_node(SyntaxKind::PolymorphicVariantPayload);
        match issue {
            Some(PayloadIssue::Boundary(range)) => emit_type_error(
                self.committed,
                TypeRole::PolymorphicVariantPayloadBoundary,
                range,
                ExpectedSyntax::TypePayloadBoundary,
            ),
            Some(PayloadIssue::Type(range)) => {
                self.committed.emit_trivia(trivia);
                emit_type_error(
                    self.committed,
                    TypeRole::PolymorphicVariantPayload,
                    range,
                    ExpectedSyntax::TypeExpression,
                );
            }
            None => match boundary {
                Recovered::Complete(_) => self.committed.emit_trivia(trivia),
                Recovered::Incomplete => emit_type_missing(
                    self.committed,
                    GrammarRole::Type(TypeRole::PolymorphicVariantPayloadBoundary),
                    ExpectedSyntax::TypePayloadBoundary,
                ),
            },
        }
    }

    fn consume_payload_type(&mut self) -> bool {
        let saved = self.with_input(|i| i.local.type_ml_arg());
        self.with_input(|i| i.local.set_type_ml_arg(true));
        let parsed =
            commit_direct_type_expression_in_current_episode(false, self.committed).is_some();
        self.with_input(|i| i.local.set_type_ml_arg(saved));
        parsed
    }

    fn finish_payload(&mut self) {
        self.committed.finish_node();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use chasa::{input::IsCut, prelude::In};

    use crate::{
        SyntaxNode,
        input::SourceInput,
        session::{FullCstOutput, ParseLocal},
    };

    fn assert_variant_defers_live_companion(source: &str, remainder: &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let root_scope = local.push_root_statement_ambient_scope();
        let companion = local.push_if_expression_companion(0, &["elsif", "else"]);
        let stops = StopSet::default()
            .with(StopKind::Elsif)
            .with(StopKind::Else);
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let expression = i
            .run(from_fn(parse_type_expression))
            .expect("polymorphic variant prefix");
        assert_eq!(i.input.remainder(), remainder, "AST {source:?}");
        assert!(matches!(
            expression.complete_primary(),
            TypePrimary::PolymorphicVariant(PolymorphicVariantType {
                tags,
                close: Recovered::Incomplete,
                ..
            }) if matches!(tags.as_slice(), [Recovered::Complete(PolymorphicVariantTag {
                payloads,
                ..
            })] if payloads.is_empty())
        ));
        drop(i);
        assert_eq!(local.pop_stop_set(), Some(stops));
        assert_eq!(
            local.pop_if_expression_companion().map(|frame| frame.id()),
            Some(companion),
        );
        assert_eq!(local.pop_ambient_owner_scope(), Some(root_scope));

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let root_scope = local.push_root_statement_ambient_scope();
        let companion = local.push_if_expression_companion(0, &["elsif", "else"]);
        let stops = StopSet::default()
            .with(StopKind::Elsif)
            .with(StopKind::Else);
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = crate::session::Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_direct_type_expression(&mut committed).expect("direct polymorphic variant prefix");
        assert_eq!(
            committed.probe(|probe| probe.input().input.remainder()),
            remainder,
            "direct {source:?}",
        );
        committed.finish_node();
        let output = committed.into_output();
        let recoveries = output.committed_recoveries();
        assert_eq!(
            recoveries
                .iter()
                .filter(|record| record.kind == RecoveryKind::Missing
                    && record.site.role
                        == GrammarRole::ClosingDelimiter {
                            owner: ConstructRole::PolymorphicVariantType,
                            delimiter: Delimiter::Brace,
                        })
                .count(),
            1,
            "direct {source:?}: {recoveries:#?}",
        );
        assert!(
            !recoveries
                .iter()
                .any(|record| record.kind == RecoveryKind::Missing
                && matches!(
                    record.site.role,
                    GrammarRole::Type(
                        TypeRole::PolymorphicVariantTag
                            | TypeRole::PolymorphicVariantPayload
                            | TypeRole::PolymorphicVariantPayloadBoundary
                    )
                )),
            "direct {source:?}: {recoveries:#?}",
        );
        drop(output);
        assert_eq!(local.pop_stop_set(), Some(stops));
        assert_eq!(
            local.pop_if_expression_companion().map(|frame| frame.id()),
            Some(companion),
        );
        assert_eq!(local.pop_ambient_owner_scope(), Some(root_scope));
    }

    fn assert_nested_variant_preserves_else_arm(source: &str) {
        let table = crate::operator::OperatorTable::empty();

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        i.run(from_fn(|i| {
            crate::grammar::expression::parse_expression_with_operators(&table, i)
        }))
        .expect("AST nested polymorphic variant expression");
        assert_eq!(i.input.remainder(), "", "AST {source:?}");

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = crate::session::Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        crate::grammar::expression::parse_direct_expression_with_operators(
            &table,
            crate::scan::operator::LeadingTrivia::None,
            &mut committed,
        )
        .expect("direct nested polymorphic variant expression");
        assert_eq!(
            committed.probe(|probe| probe.input().input.remainder()),
            "",
            "direct {source:?}",
        );
        committed.finish_node();
        let output = committed.into_output();
        let recoveries = output.committed_recoveries().to_vec();
        let root = SyntaxNode::new_root(output.finish_complete());
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::ElseKw)
                .count(),
            1,
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
                .count(),
            0,
        );
        for owner in [
            ConstructRole::PolymorphicVariantType,
            ConstructRole::StructNamedFields,
        ] {
            assert_eq!(
                recoveries
                    .iter()
                    .filter(|record| record.kind == RecoveryKind::Missing
                        && record.site.role
                            == GrammarRole::ClosingDelimiter {
                                owner,
                                delimiter: Delimiter::Brace,
                            })
                    .count(),
                1,
                "{owner:?}: {recoveries:#?}",
            );
        }
    }

    fn boundary(source: &str, stops: StopSet) -> Option<TypeBoundary> {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        classify_type_boundary(
            TypeBoundaryPolicy {
                matching_close: None,
                local_separators: StopSet::default(),
                locally_owned_stops: StopSet::default(),
            },
            &mut i,
        )
    }

    fn stop_source(stop: StopKind) -> &'static str {
        match stop {
            StopKind::Newline => "\n",
            StopKind::Comma => ",",
            StopKind::Semicolon => ";",
            StopKind::Colon => ":",
            StopKind::LeftBrace => "{",
            StopKind::Elsif => "elsif",
            StopKind::Else => "else",
            StopKind::RightParenthesis => ")",
            StopKind::RightBracket => "]",
            StopKind::RightBrace => "}",
            StopKind::Equal => "=",
            StopKind::Arrow => "->",
            StopKind::ArmGuardIf => "if",
            StopKind::ArmGuardWhere => "where",
            StopKind::With => "with",
            StopKind::Derives => "derives",
            StopKind::Via => "via",
            StopKind::LeftParenthesis => "(",
        }
    }

    #[test]
    fn boundary_classifier_covers_every_stop_in_active_and_inactive_states() {
        for stop in StopKind::ALL.iter().copied() {
            let source = stop_source(stop);
            let inactive = boundary(source, StopSet::default());
            assert!(
                !matches!(inactive, Some(TypeBoundary::ActiveStop(found)) if found == stop)
                    && !matches!(inactive, Some(TypeBoundary::OuterOwnedClose)),
                "inactive {stop:?} at {source:?}: {inactive:?}",
            );

            let active = boundary(source, StopSet::default().with(stop));
            if matches!(
                stop,
                StopKind::RightParenthesis | StopKind::RightBracket | StopKind::RightBrace
            ) {
                assert_eq!(active, Some(TypeBoundary::OuterOwnedClose), "{stop:?}");
            } else {
                assert_eq!(active, Some(TypeBoundary::ActiveStop(stop)), "{stop:?}");
            }
        }
    }

    #[test]
    fn boundary_classifier_uses_exact_tokens_and_always_reports_eof() {
        for (stop, exact, longer_spellings) in [
            (StopKind::Colon, ":", &["::"][..]),
            (StopKind::Equal, "=", &["==", "=>", "=+"][..]),
            (StopKind::Arrow, "->", &["->>", "->="][..]),
        ] {
            let active = StopSet::default().with(stop);
            assert_eq!(
                boundary(exact, active),
                Some(TypeBoundary::ActiveStop(stop))
            );
            for longer in longer_spellings {
                assert_ne!(
                    boundary(longer, active),
                    Some(TypeBoundary::ActiveStop(stop)),
                    "{stop:?} must not split {longer:?}",
                );
            }
        }
        assert_eq!(boundary("", StopSet::default()), Some(TypeBoundary::Eof));
        assert_eq!(
            boundary("", StopSet::default().with(StopKind::With)),
            Some(TypeBoundary::Eof),
        );
    }

    #[test]
    fn qualifying_tag_newline_remains_local_under_an_active_newline_stop() {
        let source = ":{\n  A Pair(Int)\n  B\n}";
        let stops = StopSet::default().with(StopKind::Newline);

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let expression = i
            .run(from_fn(parse_type_expression))
            .expect("polymorphic variant AST prefix");
        assert_eq!(i.input.remainder(), "\n}");
        assert!(matches!(
            expression.complete_primary(),
            TypePrimary::PolymorphicVariant(PolymorphicVariantType {
                tags,
                close: Recovered::Incomplete,
                ..
            }) if tags.len() == 2
        ));
        drop(i);
        assert_eq!(local.pop_stop_set(), Some(stops));

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = crate::session::Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_direct_type_expression(&mut committed).expect("polymorphic variant direct prefix");
        assert_eq!(
            committed.probe(|probe| probe.input().input.remainder()),
            "\n}",
        );
        committed.finish_node();
        let output = committed.into_output();
        assert_eq!(
            output
                .committed_recoveries()
                .iter()
                .filter(|record| {
                    record.kind == RecoveryKind::Missing
                        && record.site.role
                            == GrammarRole::ClosingDelimiter {
                                owner: ConstructRole::PolymorphicVariantType,
                                delimiter: Delimiter::Brace,
                            }
                })
                .count(),
            1,
        );
        drop(output);
        assert_eq!(local.pop_stop_set(), Some(stops));
    }

    #[test]
    fn it3_same_line_payload_candidate_defers_to_the_live_if_companion() {
        assert_variant_defers_live_companion(":{A else: 0", " else: 0");
        assert_nested_variant_preserves_else_arm("if condition:\n  struct S { field: :{A else: 0");
    }

    #[test]
    fn nt5_newline_tag_candidate_defers_to_the_live_if_companion() {
        assert_variant_defers_live_companion(":{A\nelse: 0", "\nelse: 0");
        assert_nested_variant_preserves_else_arm("if condition:\n  struct S { field: :{A\nelse: 0");
    }

    #[test]
    fn opener_and_comma_fresh_heads_keep_companion_spelling_local() {
        let source = ":{else,A,else}";
        let stops = StopSet::default()
            .with(StopKind::Elsif)
            .with(StopKind::Else);

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let root_scope = local.push_root_statement_ambient_scope();
        let companion = local.push_if_expression_companion(0, &["elsif", "else"]);
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let mut i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let expression = i
            .run(from_fn(parse_type_expression))
            .expect("complete polymorphic variant");
        assert_eq!(i.input.remainder(), "");
        assert!(matches!(
            expression.complete_primary(),
            TypePrimary::PolymorphicVariant(PolymorphicVariantType {
                tags,
                close: Recovered::Complete(_),
                ..
            }) if tags.len() == 3
        ));
        drop(i);
        assert_eq!(local.pop_stop_set(), Some(stops));
        assert_eq!(
            local.pop_if_expression_companion().map(|frame| frame.id()),
            Some(companion),
        );
        assert_eq!(local.pop_ambient_owner_scope(), Some(root_scope));

        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let root_scope = local.push_root_statement_ambient_scope();
        let companion = local.push_if_expression_companion(0, &["elsif", "else"]);
        local.push_stop_set(stops);
        let mut expectations = chasa::LatestSink::new();
        let mut is_cut = false;
        let i = In::new(
            &mut source_input,
            &mut expectations,
            IsCut::new(&mut is_cut),
        )
        .set_local(&mut local);
        let mut committed = crate::session::Probe::new(i).commit(FullCstOutput::new(source));
        committed.start_node(SyntaxKind::Root);
        commit_direct_type_expression(&mut committed).expect("direct complete polymorphic variant");
        assert_eq!(committed.probe(|probe| probe.input().input.remainder()), "",);
        committed.finish_node();
        let output = committed.into_output();
        assert!(output.committed_recoveries().is_empty());
        assert_eq!(
            SyntaxNode::new_root(output.finish_complete()).to_string(),
            source
        );
        assert_eq!(local.pop_stop_set(), Some(stops));
        assert_eq!(
            local.pop_if_expression_companion().map(|frame| frame.id()),
            Some(companion),
        );
        assert_eq!(local.pop_ambient_owner_scope(), Some(root_scope));
    }

    #[test]
    fn every_tag_position_has_a_defined_transition_for_every_boundary_kind() {
        let comma = 7..8;
        let positions = [
            TagPosition::Optional,
            TagPosition::AfterTag,
            TagPosition::Required {
                filled: false,
                last_comma: Some(comma.clone()),
            },
            TagPosition::Required {
                filled: true,
                last_comma: Some(comma.clone()),
            },
        ];

        for position in positions {
            let close = transition(&position, TagBoundary::Close);
            assert!(!close.emit_missing);
            assert_eq!(
                close.trailing_comma,
                if matches!(position, TagPosition::Required { filled: false, .. }) {
                    Some(comma.clone())
                } else {
                    None
                },
            );

            let separator = transition(&position, TagBoundary::Comma(comma.clone()));
            let separator_missing = !matches!(position, TagPosition::AfterTag);
            assert_eq!(separator.emit_missing, separator_missing);
            assert_eq!(
                separator.next,
                TagPosition::Required {
                    filled: separator_missing,
                    last_comma: Some(comma.clone()),
                },
            );

            let newline = transition(&position, TagBoundary::QualifyingNewline);
            assert_eq!(
                newline.next,
                if matches!(position, TagPosition::AfterTag) {
                    TagPosition::Required {
                        filled: false,
                        last_comma: None,
                    }
                } else {
                    position.clone()
                },
            );

            let owner = transition(&position, TagBoundary::Owner);
            assert_eq!(
                owner.emit_missing,
                matches!(position, TagPosition::Required { filled: false, .. }),
            );
            assert_eq!(owner.next, position);
        }
    }
}
