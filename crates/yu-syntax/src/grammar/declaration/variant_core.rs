use super::*;

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum EnumBody<'source> {
    Bodyless {
        semicolon: Option<Range<usize>>,
    },
    Braced(EnumBracedBody<'source>),
    Colon {
        colon: Range<usize>,
        body: Recovered<EnumIndentedVariantBody<'source>>,
    },
    Equals {
        equals: Range<usize>,
        body: Recovered<EnumEqualsVariantBody<'source>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EnumBracedBody<'source> {
    pub(super) open: Range<usize>,
    pub(super) variants: Vec<Recovered<EnumVariant<'source>>>,
    pub(super) trailing_comma: Option<Range<usize>>,
    pub(super) close: Recovered<Range<usize>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum EnumEqualsVariantBody<'source> {
    Inline {
        variants: Vec<Recovered<EnumVariant<'source>>>,
        trailing_pipe: Option<Range<usize>>,
        range: Range<usize>,
    },
    Indented(EnumIndentedVariantBody<'source>),
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EnumIndentedVariantBody<'source> {
    pub(super) base_indent: usize,
    pub(super) block_indent: usize,
    pub(super) variants: Vec<Recovered<EnumVariant<'source>>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct EnumVariant<'source> {
    pub(super) name: Recovered<WordSpan<'source>>,
    pub(super) payload: EnumVariantPayload<'source>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum EnumVariantPayload<'source> {
    Unit,
    From {
        keyword: Range<usize>,
        type_expr: Recovered<Box<TypeExpression<'source>>>,
        range: Range<usize>,
    },
    Named {
        open: Range<usize>,
        fields: Vec<Recovered<StructNamedField<'source>>>,
        trailing_comma: Option<Range<usize>>,
        close: Recovered<Range<usize>>,
        range: Range<usize>,
    },
    Tuple {
        open: Range<usize>,
        fields: Vec<Recovered<StructTupleField<'source>>>,
        trailing_comma: Option<Range<usize>>,
        close: Recovered<Range<usize>>,
        range: Range<usize>,
    },
    Positional {
        types: Vec<Recovered<Box<TypeExpression<'source>>>>,
        range: Range<usize>,
    },
}

pub(super) fn enum_body_range_end(body: &Recovered<EnumBody<'_>>) -> Option<usize> {
    match body {
        Recovered::Incomplete => None,
        Recovered::Complete(EnumBody::Bodyless {
            semicolon: Some(semicolon),
        }) => Some(semicolon.end),
        Recovered::Complete(EnumBody::Bodyless { semicolon: None }) => None,
        Recovered::Complete(EnumBody::Braced(body)) => Some(body.range.end),
        Recovered::Complete(EnumBody::Colon { colon, body }) => match body {
            Recovered::Complete(body) => Some(body.range.end),
            Recovered::Incomplete => Some(colon.end),
        },
        Recovered::Complete(EnumBody::Equals { equals, body }) => match body {
            Recovered::Complete(EnumEqualsVariantBody::Inline { range, .. }) => Some(range.end),
            Recovered::Complete(EnumEqualsVariantBody::Indented(body)) => Some(body.range.end),
            Recovered::Incomplete => Some(equals.end),
        },
    }
}

pub(super) fn enum_body_implicit_boundary_pending<E>(enum_base: usize, i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) || i.input.remainder().is_empty() {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = match mod_trivia(enum_base, i) {
        None => i
            .run(scan_trivia)
            .is_some_and(|trivia| enum_variant_trivia_has_newline(&trivia)),
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

pub(super) fn enum_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_declaration_exact_equals).is_some()
        || i.run(scan_punctuation).is_some_and(|punctuation| {
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

/// Consumes one maximal malformed Enum body-introducer run. The AST path has
/// no recovery nodes yet, but it must reach the same starter or caller-owned
/// boundary that Gate 8's direct-CST adapter will record.
pub(super) fn enum_body_introducer_error_retry_ast<'source, E>(
    enum_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if enum_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if enum_body_implicit_boundary_pending(enum_base, i) {
            return (start < i.pos()).then_some(false);
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

#[derive(Clone)]
pub(super) enum DirectEnumBodyStarter {
    Bodyless(Range<usize>),
    Braced(Range<usize>),
    Colon(Range<usize>),
    Equals(Range<usize>),
}

pub(super) fn enum_direct_body_starter<E>(
    enum_base: usize,
    i: &mut SynIn<E>,
) -> Option<(TriviaRun, DirectEnumBodyStarter)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let result = (|| {
        let trivia = mod_trivia(enum_base, i)?;
        if let Some(equals) = i.run(scan_declaration_exact_equals) {
            return Some((trivia, DirectEnumBodyStarter::Equals(equals)));
        }
        let punctuation = i.run(scan_punctuation)?;
        let starter = match punctuation.kind() {
            PunctuationKind::Semicolon => DirectEnumBodyStarter::Bodyless(punctuation.range()),
            PunctuationKind::Open(Delimiter::Brace) => {
                DirectEnumBodyStarter::Braced(punctuation.range())
            }
            PunctuationKind::Colon => DirectEnumBodyStarter::Colon(punctuation.range()),
            _ => return None,
        };
        Some((trivia, starter))
    })();
    i.rollback(checkpoint);
    result
}

/// The four body-local separator regimes share one stream judge.  The form
/// controls only separator and terminal authority; variant head and payload
/// parsing deliberately stay behind [`VariantDeclarationSequenceContext`] until Gate
/// 6 supplies their real AST/direct-CST adapters.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum VariantDeclarationSequenceForm {
    Braced,
    ColonIndented,
    EqualsInline,
    EqualsIndented,
}

/// Backward-compatible fixture spelling for the neutral sequence-form type.
/// Production adapters use `VariantDeclarationSequenceForm` directly.
pub(super) type EnumVariantSequenceForm = VariantDeclarationSequenceForm;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct EnumVariantSeparatorSet {
    pub(super) comma: bool,
    pub(super) pipe: bool,
}

impl EnumVariantSeparatorSet {
    #[allow(dead_code)]
    pub(super) const fn new(comma: bool, pipe: bool) -> Self {
        Self { comma, pipe }
    }
}

/// The invariant sequence inputs selected by the body-form judge.  In
/// particular, the layout frame is captured by that owner once; a later
/// variant or recovery path must never reconstruct it from an item.
#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct VariantDeclarationSequenceSpec {
    pub(super) form: VariantDeclarationSequenceForm,
    pub(super) layout: LayoutDelimitedFrame,
    pub(super) declaration_base: usize,
    pub(super) explicit_separators: EnumVariantSeparatorSet,
    pub(super) matching_close: Option<Delimiter>,
    pub(super) allow_leading_pipe: bool,
    pub(super) allow_trailing_pipe: bool,
}

/// Backward-compatible fixture spelling for the neutral sequence spec.
/// Production adapters use `VariantDeclarationSequenceSpec` directly.
pub(super) type EnumVariantSequenceSpec = VariantDeclarationSequenceSpec;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum EnumVariantSeparator {
    Comma(Range<usize>),
    Pipe(Range<usize>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum EnumVariantSequenceTermination {
    MatchingClose(Range<usize>),
    MismatchedClose,
    Dedent,
    OwnerBoundary,
    EndOfInput,
    ItemContinuation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct VariantDeclarationCompanionOwnerTail {
    pub(super) owner: VariantDeclarationOwner,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CompanionVariantTypeExit {
    Normal,
    ItemContinuation,
}

struct CompanionVariantTypeResult<T> {
    value: Recovered<T>,
    exit: CompanionVariantTypeExit,
}

trait CompanionVariantSequenceContext<'source>: VariantDeclarationSequenceContext<'source> {
    fn take_item_continuation(&mut self) -> bool;
}

/// Item realization is intentionally the only pluggable part of the neutral
/// stream.  Gate 5's fixture context consumes one raw word; Gate 6 will make
/// the same callback own `from`, named, tuple, and positional payloads.
pub(super) trait VariantDeclarationSequenceContext<'source> {
    type Error: ErrorSink<usize>;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, Self::Error>) -> R)
    -> R;
    fn emit_trivia(&mut self, trivia: &TriviaRun);
    fn emit_missing_variant(&mut self);
    fn emit_separator(&mut self, separator: EnumVariantSeparator);
    fn set_trailing_separator(&mut self, separator: EnumVariantSeparator);
    fn emit_matching_close(&mut self, close: Range<usize>);

    /// Receives an already-selected malformed prefix, if any, with the cursor
    /// at its raw-name retry candidate or at a terminal safe point.  Returning
    /// false closes one incomplete item without making the stream invent a
    /// second recovery record.
    fn parse_variant_item(&mut self, malformed: Option<Range<usize>>) -> bool;
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum EnumVariantSequencePosition {
    Optional,
    Required {
        pending_boundary: Option<EnumVariantBoundary>,
    },
    AfterVariant,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum EnumVariantBoundary {
    Explicit(EnumVariantSeparator),
    LayoutNewline,
}

#[derive(Clone, Debug)]
pub(super) struct EnumVariantSequenceState {
    pub(super) position: EnumVariantSequencePosition,
    pub(super) accepted_variant: bool,
    pub(super) accepted_leading_pipe: bool,
}

impl EnumVariantSequenceState {
    pub(super) fn new(spec: EnumVariantSequenceSpec) -> Self {
        let position = if matches!(spec.form, EnumVariantSequenceForm::Braced) {
            EnumVariantSequencePosition::Optional
        } else {
            EnumVariantSequencePosition::Required {
                pending_boundary: None,
            }
        };
        Self {
            position,
            accepted_variant: false,
            accepted_leading_pipe: false,
        }
    }

    pub(super) fn accepted_variant(&mut self) {
        self.position = EnumVariantSequencePosition::AfterVariant;
        self.accepted_variant = true;
    }

    pub(super) fn qualifying_newline(&mut self) {
        if matches!(self.position, EnumVariantSequencePosition::AfterVariant) {
            self.position = EnumVariantSequencePosition::Required {
                pending_boundary: Some(EnumVariantBoundary::LayoutNewline),
            };
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum EnumVariantJudgeOrigin {
    FreshSlot,
    Continuation,
}

pub(super) enum EnumVariantGap {
    SameLine(TriviaRun),
    QualifyingNewline(TriviaRun),
    Dedent,
    Owner,
    ItemContinuation,
    None,
}

pub(super) struct EnumVariantSeparatorCluster {
    pub(super) trivia: TriviaRun,
    pub(super) separator: EnumVariantSeparator,
}

/// Drives only sequence evidence.  A raw word following a completed stub item
/// on the same line is deliberately returned as [`ItemContinuation`] rather
/// than guessed to be a second variant: Gate 6 owns its positional payload.
#[allow(dead_code)]
pub(super) fn drive_variant_declaration_sequence<'source, C>(
    context: &mut C,
    spec: VariantDeclarationSequenceSpec,
) -> EnumVariantSequenceTermination
where
    C: VariantDeclarationSequenceContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    let mut state = EnumVariantSequenceState::new(spec);
    let mut origin = EnumVariantJudgeOrigin::FreshSlot;

    loop {
        if context.with_input(|i| i.input.remainder().is_empty()) {
            finish_enum_variant_sequence(&mut state, spec, context);
            return EnumVariantSequenceTermination::EndOfInput;
        }
        if let Some(close) = context.with_input(|i| scan_enum_variant_matching_close(spec, i)) {
            finish_enum_variant_sequence(&mut state, spec, context);
            context.emit_matching_close(close.clone());
            return EnumVariantSequenceTermination::MatchingClose(close);
        }
        if context.with_input(|i| enum_variant_mismatched_close_pending(spec, i)) {
            finish_enum_variant_sequence(&mut state, spec, context);
            return EnumVariantSequenceTermination::MismatchedClose;
        }
        if let Some(cluster) = context.with_input(|i| scan_enum_variant_separator_cluster(spec, i))
        {
            apply_enum_variant_separator(&mut state, spec, &cluster.separator, context);
            if !cluster.trivia.is_empty() {
                context.emit_trivia(&cluster.trivia);
            }
            context.emit_separator(cluster.separator);
            origin = EnumVariantJudgeOrigin::FreshSlot;
            continue;
        }
        if matches!(origin, EnumVariantJudgeOrigin::Continuation)
            && context.with_input(any_ambient_owner_claims)
        {
            finish_enum_variant_sequence(&mut state, spec, context);
            return EnumVariantSequenceTermination::OwnerBoundary;
        }

        match context.with_input(|i| classify_enum_variant_gap(spec, i)) {
            EnumVariantGap::SameLine(trivia) => {
                let terminal_follows = context
                    .with_input(|i| enum_variant_same_line_trivia_precedes_terminal(spec, i));
                if matches!(origin, EnumVariantJudgeOrigin::FreshSlot) || terminal_follows {
                    let consumed = context.with_input(consume_enum_variant_trivia);
                    debug_assert_eq!(consumed.range(), trivia.range());
                    context.emit_trivia(&consumed);
                    continue;
                }
                return EnumVariantSequenceTermination::ItemContinuation;
            }
            EnumVariantGap::QualifyingNewline(trivia) => {
                let consumed = context.with_input(consume_enum_variant_trivia);
                debug_assert_eq!(consumed.range(), trivia.range());
                context.emit_trivia(&consumed);
                state.qualifying_newline();
                origin = EnumVariantJudgeOrigin::FreshSlot;
                continue;
            }
            EnumVariantGap::Dedent => {
                finish_enum_variant_sequence(&mut state, spec, context);
                return EnumVariantSequenceTermination::Dedent;
            }
            EnumVariantGap::Owner => {
                finish_enum_variant_sequence(&mut state, spec, context);
                return EnumVariantSequenceTermination::OwnerBoundary;
            }
            EnumVariantGap::ItemContinuation => {
                return EnumVariantSequenceTermination::ItemContinuation;
            }
            EnumVariantGap::None => {}
        }

        if context.with_input(|i| enum_variant_terminal_boundary_pending(spec, i)) {
            finish_enum_variant_sequence(&mut state, spec, context);
            return if context.with_input(|i| i.input.remainder().is_empty()) {
                EnumVariantSequenceTermination::EndOfInput
            } else {
                EnumVariantSequenceTermination::OwnerBoundary
            };
        }
        if context.with_input(enum_variant_raw_name_pending) {
            if !context.parse_variant_item(None) {
                return EnumVariantSequenceTermination::ItemContinuation;
            }
            state.accepted_variant();
            origin = EnumVariantJudgeOrigin::Continuation;
            continue;
        }
        if let Some(range) = context.with_input(|i| scan_enum_variant_invalid_run(spec, i)) {
            let _retried = context.parse_variant_item(Some(range));
            state.accepted_variant();
            origin = EnumVariantJudgeOrigin::Continuation;
            continue;
        }

        finish_enum_variant_sequence(&mut state, spec, context);
        return EnumVariantSequenceTermination::ItemContinuation;
    }
}

fn finish_variant_sequence_before_companion<'source, C>(
    state: &mut EnumVariantSequenceState,
    spec: VariantDeclarationSequenceSpec,
    context: &mut C,
) where
    C: VariantDeclarationSequenceContext<'source>,
{
    if matches!(
        state.position,
        EnumVariantSequencePosition::Required {
            pending_boundary: Some(EnumVariantBoundary::Explicit(EnumVariantSeparator::Pipe(_))),
        }
    ) {
        context.emit_missing_variant();
    } else {
        finish_enum_variant_sequence(state, spec, context);
    }
}

fn drive_equals_inline_variant_sequence_with_companion_handoff<'source, C>(
    context: &mut C,
    spec: VariantDeclarationSequenceSpec,
) -> (EnumVariantSequenceTermination, bool)
where
    C: CompanionVariantSequenceContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    assert!(matches!(
        spec.form,
        VariantDeclarationSequenceForm::EqualsInline
    ));
    let mut state = EnumVariantSequenceState::new(spec);
    let mut origin = EnumVariantJudgeOrigin::FreshSlot;
    loop {
        if context.with_input(|i| i.input.remainder().is_empty()) {
            finish_enum_variant_sequence(&mut state, spec, context);
            return (EnumVariantSequenceTermination::EndOfInput, false);
        }
        if let Some(close) = context.with_input(|i| scan_enum_variant_matching_close(spec, i)) {
            finish_enum_variant_sequence(&mut state, spec, context);
            context.emit_matching_close(close.clone());
            return (EnumVariantSequenceTermination::MatchingClose(close), false);
        }
        if context.with_input(|i| enum_variant_mismatched_close_pending(spec, i)) {
            finish_enum_variant_sequence(&mut state, spec, context);
            return (EnumVariantSequenceTermination::MismatchedClose, false);
        }
        if let Some(cluster) = context.with_input(|i| scan_enum_variant_separator_cluster(spec, i))
        {
            apply_enum_variant_separator(&mut state, spec, &cluster.separator, context);
            if !cluster.trivia.is_empty() {
                context.emit_trivia(&cluster.trivia);
            }
            context.emit_separator(cluster.separator);
            origin = EnumVariantJudgeOrigin::FreshSlot;
            continue;
        }
        if matches!(origin, EnumVariantJudgeOrigin::Continuation)
            && context.with_input(any_ambient_owner_claims)
        {
            finish_enum_variant_sequence(&mut state, spec, context);
            return (EnumVariantSequenceTermination::OwnerBoundary, false);
        }
        if context.with_input(|i| {
            recognize_declaration_companion_handoff(spec.declaration_base, i).is_some()
        }) {
            finish_variant_sequence_before_companion(&mut state, spec, context);
            return (EnumVariantSequenceTermination::OwnerBoundary, true);
        }
        match context.with_input(|i| classify_enum_variant_gap(spec, i)) {
            EnumVariantGap::SameLine(trivia) => {
                let terminal_follows = context
                    .with_input(|i| enum_variant_same_line_trivia_precedes_terminal(spec, i));
                if matches!(origin, EnumVariantJudgeOrigin::FreshSlot) || terminal_follows {
                    let consumed = context.with_input(consume_enum_variant_trivia);
                    debug_assert_eq!(consumed.range(), trivia.range());
                    context.emit_trivia(&consumed);
                    continue;
                }
                return (EnumVariantSequenceTermination::ItemContinuation, false);
            }
            EnumVariantGap::QualifyingNewline(trivia) => {
                let consumed = context.with_input(consume_enum_variant_trivia);
                debug_assert_eq!(consumed.range(), trivia.range());
                context.emit_trivia(&consumed);
                state.qualifying_newline();
                origin = EnumVariantJudgeOrigin::FreshSlot;
                continue;
            }
            EnumVariantGap::Dedent => {
                finish_enum_variant_sequence(&mut state, spec, context);
                return (EnumVariantSequenceTermination::Dedent, false);
            }
            EnumVariantGap::Owner => {
                finish_enum_variant_sequence(&mut state, spec, context);
                return (EnumVariantSequenceTermination::OwnerBoundary, false);
            }
            EnumVariantGap::ItemContinuation => {
                return (EnumVariantSequenceTermination::ItemContinuation, false);
            }
            EnumVariantGap::None => {}
        }
        if context.with_input(|i| enum_variant_terminal_boundary_pending(spec, i)) {
            finish_enum_variant_sequence(&mut state, spec, context);
            let termination = if context.with_input(|i| i.input.remainder().is_empty()) {
                EnumVariantSequenceTermination::EndOfInput
            } else {
                EnumVariantSequenceTermination::OwnerBoundary
            };
            return (termination, false);
        }
        if context.with_input(enum_variant_raw_name_pending) {
            if !context.parse_variant_item(None) {
                return (EnumVariantSequenceTermination::ItemContinuation, false);
            }
            state.accepted_variant();
            if context.take_item_continuation() {
                return (EnumVariantSequenceTermination::ItemContinuation, false);
            }
            origin = EnumVariantJudgeOrigin::Continuation;
            continue;
        }
        if let Some(range) = context.with_input(|i| scan_enum_variant_invalid_run(spec, i)) {
            let _retried = context.parse_variant_item(Some(range));
            state.accepted_variant();
            if context.take_item_continuation() {
                return (EnumVariantSequenceTermination::ItemContinuation, false);
            }
            origin = EnumVariantJudgeOrigin::Continuation;
            continue;
        }
        finish_enum_variant_sequence(&mut state, spec, context);
        return (EnumVariantSequenceTermination::ItemContinuation, false);
    }
}

/// The former Enum-named entry point remains only for Gate 5's existing
/// neutral sequence fixture; declaration adapters call the renamed core.
#[allow(dead_code)]
pub(super) fn drive_enum_variant_sequence<'source, C>(
    context: &mut C,
    spec: VariantDeclarationSequenceSpec,
) -> EnumVariantSequenceTermination
where
    C: VariantDeclarationSequenceContext<'source>,
    Unexpected<char>: Into<<C::Error as ErrorSink<usize>>::Error>,
    UnexpectedEndOfInput: Into<<C::Error as ErrorSink<usize>>::Error>,
{
    drive_variant_declaration_sequence(context, spec)
}

pub(super) fn apply_enum_variant_separator<'source, C>(
    state: &mut EnumVariantSequenceState,
    spec: EnumVariantSequenceSpec,
    separator: &EnumVariantSeparator,
    context: &mut C,
) where
    C: VariantDeclarationSequenceContext<'source>,
{
    let pending_layout_pipe = matches!(
        (&state.position, separator),
        (
            EnumVariantSequencePosition::Required {
                pending_boundary: Some(EnumVariantBoundary::LayoutNewline),
            },
            EnumVariantSeparator::Pipe(_),
        )
    );
    let leading_pipe = matches!(separator, EnumVariantSeparator::Pipe(_))
        && spec.allow_leading_pipe
        && !state.accepted_variant
        && !state.accepted_leading_pipe
        && matches!(
            state.position,
            EnumVariantSequencePosition::Optional
                | EnumVariantSequencePosition::Required {
                    pending_boundary: None | Some(EnumVariantBoundary::LayoutNewline),
                }
        );
    if leading_pipe {
        state.accepted_leading_pipe = true;
    } else if !pending_layout_pipe
        && !matches!(state.position, EnumVariantSequencePosition::AfterVariant)
    {
        context.emit_missing_variant();
    }
    state.position = EnumVariantSequencePosition::Required {
        pending_boundary: Some(EnumVariantBoundary::Explicit(separator.clone())),
    };
}

pub(super) fn finish_enum_variant_sequence<'source, C>(
    state: &mut EnumVariantSequenceState,
    spec: EnumVariantSequenceSpec,
    context: &mut C,
) where
    C: VariantDeclarationSequenceContext<'source>,
{
    let EnumVariantSequencePosition::Required { pending_boundary } = &state.position else {
        return;
    };
    match pending_boundary {
        Some(EnumVariantBoundary::Explicit(EnumVariantSeparator::Comma(_)))
        | Some(EnumVariantBoundary::LayoutNewline) => {
            if let Some(EnumVariantBoundary::Explicit(separator)) = pending_boundary {
                context.set_trailing_separator(separator.clone());
            }
        }
        Some(EnumVariantBoundary::Explicit(separator @ EnumVariantSeparator::Pipe(_)))
            if state.accepted_variant && spec.allow_trailing_pipe =>
        {
            context.set_trailing_separator(separator.clone());
        }
        _ => context.emit_missing_variant(),
    }
}

pub(super) fn classify_enum_variant_gap<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> EnumVariantGap
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return EnumVariantGap::Owner;
    }
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if trivia.is_empty() {
        i.rollback(checkpoint);
        return EnumVariantGap::None;
    }
    if !enum_variant_trivia_has_newline(&trivia) {
        i.rollback(checkpoint);
        return EnumVariantGap::SameLine(trivia);
    }
    if matches!(spec.form, EnumVariantSequenceForm::EqualsInline) {
        i.rollback(checkpoint);
        return EnumVariantGap::ItemContinuation;
    }
    let following_indent = i.local.line().line_indent;
    if matches!(
        spec.form,
        EnumVariantSequenceForm::ColonIndented | EnumVariantSequenceForm::EqualsIndented
    ) && following_indent < spec.layout.base_indent()
    {
        i.rollback(checkpoint);
        return EnumVariantGap::Dedent;
    }
    let boundary = spec.layout.boundary_after_trivia(&trivia, following_indent);
    i.rollback(checkpoint);
    match boundary {
        LayoutDelimitedBoundary::ImplicitNewline => EnumVariantGap::QualifyingNewline(trivia),
        LayoutDelimitedBoundary::DeeperNewline => EnumVariantGap::ItemContinuation,
        LayoutDelimitedBoundary::None => EnumVariantGap::SameLine(trivia),
    }
}

pub(super) fn scan_enum_variant_separator_cluster<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> Option<EnumVariantSeparatorCluster>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if matches!(spec.form, EnumVariantSequenceForm::EqualsInline)
        && enum_variant_trivia_has_newline(&trivia)
    {
        i.rollback(checkpoint);
        return None;
    }
    let Some(separator) = scan_enum_variant_separator_at_cursor(spec, i) else {
        i.rollback(checkpoint);
        return None;
    };
    Some(EnumVariantSeparatorCluster { trivia, separator })
}

pub(super) fn scan_enum_variant_separator_at_cursor<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> Option<EnumVariantSeparator>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if spec.explicit_separators.comma {
        let checkpoint = i.checkpoint();
        if let Some(punctuation) = i.run(scan_punctuation)
            && punctuation.kind() == PunctuationKind::Comma
        {
            return Some(EnumVariantSeparator::Comma(punctuation.range()));
        }
        i.rollback(checkpoint);
    }
    if spec.explicit_separators.pipe {
        let checkpoint = i.checkpoint();
        let start = i.pos();
        if i.skip(item('|')).is_some() {
            return Some(EnumVariantSeparator::Pipe(start..i.pos()));
        }
        i.rollback(checkpoint);
    }
    None
}

pub(super) fn enum_variant_separator_pending<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_enum_variant_separator_at_cursor(spec, i).is_some();
    i.rollback(checkpoint);
    pending
}

pub(super) fn scan_enum_variant_matching_close<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let delimiter = spec.matching_close?;
    let checkpoint = i.checkpoint();
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        return None;
    };
    if punctuation.kind() == PunctuationKind::Close(delimiter) {
        Some(punctuation.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}

pub(super) fn enum_variant_matching_close_pending<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_enum_variant_matching_close(spec, i).is_some();
    i.rollback(checkpoint);
    pending
}

pub(super) fn enum_variant_mismatched_close_pending<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let Some(expected) = spec.matching_close else {
        return false;
    };
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(punctuation.kind(), PunctuationKind::Close(found) if found != expected)
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn enum_variant_terminal_boundary_pending<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() || any_ambient_owner_claims(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i
        .run(scan_punctuation)
        .is_some_and(|punctuation| match punctuation.kind() {
            PunctuationKind::Semicolon | PunctuationKind::Close(_) => true,
            PunctuationKind::Comma => !spec.explicit_separators.comma,
            _ => false,
        });
    i.rollback(checkpoint);
    pending
}

pub(super) fn enum_variant_same_line_trivia_precedes_terminal<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    let terminal = !trivia.is_empty()
        && !enum_variant_trivia_has_newline(&trivia)
        && (scan_enum_variant_matching_close(spec, i).is_some()
            || enum_variant_mismatched_close_pending(spec, i)
            || enum_variant_terminal_boundary_pending(spec, i));
    i.rollback(checkpoint);
    terminal
}

pub(super) fn scan_enum_variant_invalid_run<E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if enum_variant_raw_name_pending(i)
            || enum_variant_matching_close_pending(spec, i)
            || enum_variant_mismatched_close_pending(spec, i)
            || enum_variant_terminal_boundary_pending(spec, i)
            || enum_variant_separator_pending(spec, i)
        {
            return (start < i.pos()).then_some(start..i.pos());
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(start..i.pos());
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

pub(super) fn consume_enum_variant_trivia<E>(i: &mut SynIn<E>) -> TriviaRun
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.run(scan_trivia).expect("trivia scanning is total")
}

pub(super) fn enum_variant_trivia_has_newline(trivia: &TriviaRun) -> bool {
    trivia
        .parts()
        .iter()
        .any(|part| matches!(part.kind(), TriviaPartKind::Newline))
}

/// The field grammar is structurally shared by Struct and Enum payloads, but
/// its recovery identity is owned by the surrounding declaration.  Keeping
/// that mapping explicit prevents an Enum payload from fabricating a Struct
/// recovery record while preserving Struct's existing public surface.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum VariantFieldDriverSpec {
    Struct,
    EnumNamed,
    EnumTuple,
    ErrorNamed,
    ErrorTuple,
}

impl VariantFieldDriverSpec {
    pub(super) fn named_type_owner(self) -> TypeDelimitedOwner {
        match self {
            Self::Struct => TypeDelimitedOwner::StructNamedFields,
            Self::EnumNamed => TypeDelimitedOwner::VariantNamedPayload,
            Self::EnumTuple => TypeDelimitedOwner::VariantTuplePayload,
            Self::ErrorNamed => TypeDelimitedOwner::VariantNamedPayload,
            Self::ErrorTuple => TypeDelimitedOwner::VariantTuplePayload,
        }
    }

    pub(super) fn type_role(self) -> GrammarRole {
        match self {
            Self::Struct => GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldType,
            )),
            Self::EnumNamed => GrammarRole::Declaration(DeclarationRole::Enum(
                EnumDeclarationRole::Variant(VariantDeclarationRole::NamedFieldType),
            )),
            Self::EnumTuple => GrammarRole::Declaration(DeclarationRole::Enum(
                EnumDeclarationRole::Variant(VariantDeclarationRole::TupleFieldType),
            )),
            Self::ErrorNamed => GrammarRole::Declaration(DeclarationRole::Error(
                ErrorDeclarationRole::Variant(VariantDeclarationRole::NamedFieldType),
            )),
            Self::ErrorTuple => GrammarRole::Declaration(DeclarationRole::Error(
                ErrorDeclarationRole::Variant(VariantDeclarationRole::TupleFieldType),
            )),
        }
    }

    pub(super) fn tuple_payload(self) -> Self {
        match self {
            Self::EnumNamed | Self::EnumTuple => Self::EnumTuple,
            Self::ErrorNamed | Self::ErrorTuple => Self::ErrorTuple,
            Self::Struct => Self::Struct,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum VariantDeclarationOwner {
    Enum,
    Error,
}

/// The sole owner-specific input to the otherwise neutral variant sequence
/// and payload core. Form, layout, separators, and close authority remain in
/// `VariantDeclarationSequenceSpec`; this spec changes only recovery owners.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct VariantDeclarationOwnerSpec {
    pub(super) owner: VariantDeclarationOwner,
    pub(super) declaration_base: usize,
    pub(super) item_role: GrammarRole,
    pub(super) from_type_role: GrammarRole,
    pub(super) positional_payload_role: GrammarRole,
    pub(super) field_driver: VariantFieldDriverSpec,
}

impl VariantDeclarationOwnerSpec {
    pub(super) fn variant_role(self, role: VariantDeclarationRole) -> GrammarRole {
        match self.owner {
            VariantDeclarationOwner::Enum => {
                GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(role)))
            }
            VariantDeclarationOwner::Error => GrammarRole::Declaration(DeclarationRole::Error(
                ErrorDeclarationRole::Variant(role),
            )),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum EnumVariantTypeExpressionSlot {
    FromType,
    PositionalPayload,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct EnumVariantTypeExpressionEpisodeSpec {
    pub(super) stops: StopSet,
    pub(super) scoped_frame: TypeExpressionScopedStopFrame,
    pub(super) policy: TypeExpressionEpisodePolicy,
    pub(super) outer_role: GrammarRole,
    outer_ml_arg: bool,
}

/// Builds the one outer episode that owns an Enum payload item.  The scoped
/// frame deliberately makes the Enum separator visible only at this item's
/// completed-tail and malformed-safe points; nested TypeExpression episodes
/// keep the same raw stop bits but do not inherit that ownership.
pub(super) fn variant_declaration_type_expression_episode_spec(
    owner: VariantDeclarationOwnerSpec,
    slot: EnumVariantTypeExpressionSlot,
    form: VariantDeclarationSequenceForm,
    incoming: StopSet,
    current_episode_depth: usize,
) -> EnumVariantTypeExpressionEpisodeSpec {
    let scoped_stops = match form {
        EnumVariantSequenceForm::Braced => StopSet::default()
            .with(StopKind::Comma)
            .with(StopKind::RightBrace),
        EnumVariantSequenceForm::EqualsInline => StopSet::default().with(StopKind::Pipe),
        EnumVariantSequenceForm::ColonIndented | EnumVariantSequenceForm::EqualsIndented => {
            StopSet::default()
                .with(StopKind::Comma)
                .with(StopKind::Pipe)
                .with(StopKind::Newline)
        }
    };
    let outer_role = match slot {
        EnumVariantTypeExpressionSlot::FromType => owner.from_type_role,
        EnumVariantTypeExpressionSlot::PositionalPayload => owner.positional_payload_role,
    };
    let stops = match form {
        EnumVariantSequenceForm::Braced => {
            incoming.with(StopKind::Comma).with(StopKind::RightBrace)
        }
        EnumVariantSequenceForm::EqualsInline => incoming.with(StopKind::Pipe),
        EnumVariantSequenceForm::ColonIndented | EnumVariantSequenceForm::EqualsIndented => {
            incoming
                .with(StopKind::Comma)
                .with(StopKind::Pipe)
                .with(StopKind::Newline)
        }
    };
    EnumVariantTypeExpressionEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default(),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role,
        outer_ml_arg: matches!(slot, EnumVariantTypeExpressionSlot::PositionalPayload),
    }
}

/// Tuple fields are owned by their local parenthesized field frame, not by an
/// outer Enum variant-payload slot.  Their scoped stops therefore name only
/// the local comma and matching parenthesis while preserving outer stops
/// underneath for the enclosing field-loop close handoff.
pub(super) fn variant_declaration_tuple_field_type_expression_episode_spec(
    field_driver: VariantFieldDriverSpec,
    incoming: StopSet,
    current_episode_depth: usize,
) -> EnumVariantTypeExpressionEpisodeSpec {
    let scoped_stops = StopSet::default()
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis);
    let stops = incoming
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis);
    EnumVariantTypeExpressionEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops: StopSet::default(),
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role: field_driver.tuple_payload().type_role(),
        outer_ml_arg: false,
    }
}

pub(super) fn parse_required_variant_declaration_type_expression<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    slot: EnumVariantTypeExpressionSlot,
    form: VariantDeclarationSequenceForm,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = variant_declaration_type_expression_episode_spec(
        owner,
        slot,
        form,
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let saved_ml_arg = i.local.type_ml_arg();
    i.local.set_type_ml_arg(episode.outer_ml_arg);
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
        .expect("the mandatory Enum payload TypeExpression entry is total");
    i.local.set_type_ml_arg(saved_ml_arg);
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

pub(super) fn commit_required_variant_declaration_type_expression<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    slot: EnumVariantTypeExpressionSlot,
    form: VariantDeclarationSequenceForm,
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
        variant_declaration_type_expression_episode_spec(
            owner,
            slot,
            form,
            i.local.stop_set().unwrap_or_default(),
            i.local.type_expression_episode_depth(),
        )
    });
    let saved_ml_arg = committed.probe(|probe| probe.input().local.type_ml_arg());
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
        i.local.set_type_ml_arg(episode.outer_ml_arg);
    });
    let parsed = commit_direct_type_expression_with_outer_missing_role_and_policy(
        Some(episode.outer_role),
        episode.policy,
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        i.local.set_type_ml_arg(saved_ml_arg);
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

fn companion_variant_type_expression_episode_spec<E>(
    owner: VariantDeclarationOwnerSpec,
    slot: EnumVariantTypeExpressionSlot,
    i: &SynIn<E>,
) -> EnumVariantTypeExpressionEpisodeSpec
where
    E: ErrorSink<usize>,
{
    let ordinary = variant_declaration_type_expression_episode_spec(
        owner,
        slot,
        VariantDeclarationSequenceForm::EqualsInline,
        i.local.stop_set().unwrap_or_default(),
        i.local.type_expression_episode_depth(),
    );
    EnumVariantTypeExpressionEpisodeSpec {
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
        outer_ml_arg: ordinary.outer_ml_arg,
    }
}

fn parse_required_companion_variant_type_expression<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    slot: EnumVariantTypeExpressionSlot,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> CompanionVariantTypeResult<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = companion_variant_type_expression_episode_spec(owner, slot, i);
    let recovered_primary_fallback = !enum_variant_type_primary_pending(i);
    i.local.push_stop_set(episode.stops);
    i.local
        .push_type_expression_scoped_stop_frame(episode.scoped_frame);
    let saved_ml_arg = i.local.type_ml_arg();
    i.local.set_type_ml_arg(episode.outer_ml_arg);
    let parsed = i
        .run(from_fn(|i| {
            Some(
                parse_required_type_expression_with_handoff_recovery_isolated(
                    Some(episode.outer_role),
                    episode.policy,
                    |i| {
                        recognize_declaration_companion_handoff(owner.declaration_base, i).is_some()
                    },
                    i,
                ),
            )
        }))
        .expect("the isolated companion-aware variant TypeExpression entry is total");
    i.local.set_type_ml_arg(saved_ml_arg);
    assert_eq!(
        i.local.pop_type_expression_scoped_stop_frame(),
        Some(episode.scoped_frame),
    );
    assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    let value = match parsed {
        Recovered::Complete(parsed) => Recovered::Complete(Box::new(parsed)),
        Recovered::Incomplete => Recovered::Incomplete,
    };
    let exit = if recovered_primary_fallback
        && matches!(&value, Recovered::Complete(_))
        && i.input.remainder().starts_with(':')
    {
        CompanionVariantTypeExit::ItemContinuation
    } else {
        CompanionVariantTypeExit::Normal
    };
    CompanionVariantTypeResult { value, exit }
}

fn commit_required_companion_variant_type_expression<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    slot: EnumVariantTypeExpressionSlot,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CompanionVariantTypeResult<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered_primary_fallback =
        committed.probe(|probe| !enum_variant_type_primary_pending(probe.input()));
    let episode = committed
        .probe(|probe| companion_variant_type_expression_episode_spec(owner, slot, probe.input()));
    let saved_ml_arg = committed.probe(|probe| probe.input().local.type_ml_arg());
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(episode.stops);
        i.local
            .push_type_expression_scoped_stop_frame(episode.scoped_frame);
        i.local.set_type_ml_arg(episode.outer_ml_arg);
    });
    let parsed = commit_direct_type_expression_with_handoff_recovery_isolated(
        Some(episode.outer_role),
        episode.policy,
        |i| recognize_declaration_companion_handoff(owner.declaration_base, i).is_some(),
        committed,
    );
    committed.probe(|probe| {
        let i = probe.input();
        i.local.set_type_ml_arg(saved_ml_arg);
        assert_eq!(
            i.local.pop_type_expression_scoped_stop_frame(),
            Some(episode.scoped_frame),
        );
        assert_eq!(i.local.pop_stop_set(), Some(episode.stops));
    });
    let range = parsed.range();
    let value = if range.is_empty() {
        Recovered::Incomplete
    } else {
        Recovered::Complete(range)
    };
    let exit = if recovered_primary_fallback
        && matches!(&value, Recovered::Complete(_))
        && committed.probe(|probe| probe.input().input.remainder().starts_with(':'))
    {
        CompanionVariantTypeExit::ItemContinuation
    } else {
        CompanionVariantTypeExit::Normal
    };
    CompanionVariantTypeResult { value, exit }
}

pub(super) fn parse_required_variant_declaration_tuple_field_type_expression<'source, E>(
    field_driver: VariantFieldDriverSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = variant_declaration_tuple_field_type_expression_episode_spec(
        field_driver,
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
        .expect("mandatory Enum tuple field TypeExpression is total");
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

pub(super) fn commit_required_variant_declaration_tuple_field_type_expression<
    'parse,
    'source,
    'local,
    E,
    O,
>(
    field_driver: VariantFieldDriverSpec,
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
        variant_declaration_tuple_field_type_expression_episode_spec(
            field_driver,
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

pub(super) fn enum_variant_type_primary_pending<E>(i: &mut SynIn<E>) -> bool
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

/// After the higher-priority `from` and delimiter forms have declined, every
/// non-boundary byte after a payload gap is positional-payload evidence.  The
/// mandatory TypeExpression entry then owns its malformed-run retry; treating
/// that byte as the next Enum item would split one malformed payload across
/// two recovery owners.
pub(super) fn enum_variant_positional_payload_pending<E>(
    form: EnumVariantSequenceForm,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if enum_variant_type_primary_pending(i) {
        return true;
    }
    if i.input.remainder().is_empty() || any_ambient_owner_claims(i) {
        return false;
    }
    if matches!(i.input.remainder().chars().next(), Some('\r' | '\n')) {
        return false;
    }
    let checkpoint = i.checkpoint();
    let punctuation = i
        .run(scan_punctuation)
        .map(|punctuation| punctuation.kind());
    i.rollback(checkpoint);
    !matches!(
        punctuation,
        Some(PunctuationKind::Comma | PunctuationKind::Semicolon | PunctuationKind::Close(_))
    ) && !(matches!(
        form,
        EnumVariantSequenceForm::EqualsInline
            | EnumVariantSequenceForm::ColonIndented
            | EnumVariantSequenceForm::EqualsIndented
    ) && i.input.remainder().starts_with('|'))
}

pub(super) fn consume_enum_variant_payload_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if trivia.is_empty() || enum_variant_trivia_has_newline(&trivia) {
        i.rollback(checkpoint);
        None
    } else {
        Some(trivia)
    }
}

pub(super) fn enum_variant_exact_from_pending<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let word = i.run(scan_word)?;
    if word.text() == "from" {
        Some(word.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}

pub(super) fn enum_variant_payload_open<E>(
    delimiter: Delimiter,
    i: &mut SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    if punctuation.kind() == PunctuationKind::Open(delimiter) {
        Some(punctuation.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}

pub(super) fn parse_variant_named_field_ast<'source, E>(
    spec: VariantFieldDriverSpec,
    ambient_sensitive: bool,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<StructNamedField<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let name_recovery = if struct_word_pending(i) || struct_colon_pending(i) {
        None
    } else {
        scan_struct_field_name_colon_recovery(i)
    };
    let name = if let Some(name) = i.run(scan_word) {
        Recovered::Complete(name)
    } else if struct_colon_pending(i)
        || matches!(
            name_recovery,
            Some(StructFieldInvalidRun {
                target: StructFieldInvalidTarget::Colon { .. },
                ..
            })
        )
    {
        Recovered::Incomplete
    } else {
        return None;
    };
    let name_end = match &name {
        Recovered::Complete(name) => name.range().end,
        Recovered::Incomplete => start,
    };
    let _ = consume_struct_field_name_trivia(i);
    let colon_recovery = if struct_colon_pending(i) || struct_field_boundary_pending(i) {
        None
    } else {
        scan_struct_field_invalid_run(true, i)
    };
    let colon = scan_struct_colon(i)
        .map(Recovered::Complete)
        .unwrap_or(Recovered::Incomplete);
    let type_expr = if (ambient_sensitive && any_ambient_owner_claims(i))
        || matches!(
            colon_recovery,
            Some(StructFieldInvalidRun {
                target: StructFieldInvalidTarget::Boundary,
                ..
            })
        )
        || (matches!(colon, Recovered::Incomplete) && struct_field_boundary_pending(i))
    {
        Recovered::Incomplete
    } else {
        let _ = consume_struct_field_type_trivia(i);
        let owner = spec.named_type_owner();
        i.local.push_type_delimited_owner(owner);
        let parsed = i
            .run(from_fn(|i| {
                Some(parse_required_type_expression_with_outer_missing_role(
                    Some(spec.type_role()),
                    i,
                ))
            }))
            .expect("mandatory shared named field TypeExpression is total");
        assert_eq!(i.local.pop_type_delimited_owner(), Some(owner));
        match parsed {
            Recovered::Complete(type_expr) => Recovered::Complete(Box::new(type_expr)),
            Recovered::Incomplete => Recovered::Incomplete,
        }
    };
    let end = match &type_expr {
        Recovered::Complete(type_expr) => type_expr.range().end,
        Recovered::Incomplete => match &colon {
            Recovered::Complete(colon) => colon.end,
            Recovered::Incomplete => name_end,
        },
    };
    Some(StructNamedField {
        name,
        colon,
        type_expr,
        range: start..end,
    })
}

pub(super) fn parse_variant_tuple_field_ast<'source, E>(
    spec: VariantFieldDriverSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<StructTupleField<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let owner = (spec != VariantFieldDriverSpec::Struct).then(|| spec.named_type_owner());
    if let Some(owner) = owner {
        i.local.push_type_delimited_owner(owner);
    }
    let parsed = match spec {
        VariantFieldDriverSpec::Struct => i
            .run(from_fn(|i| {
                Some(parse_required_type_expression_with_outer_missing_role(
                    Some(spec.type_role()),
                    i,
                ))
            }))
            .expect("mandatory Struct tuple field TypeExpression is total"),
        VariantFieldDriverSpec::EnumNamed
        | VariantFieldDriverSpec::EnumTuple
        | VariantFieldDriverSpec::ErrorNamed
        | VariantFieldDriverSpec::ErrorTuple => {
            match parse_required_variant_declaration_tuple_field_type_expression(spec, i) {
                Recovered::Complete(type_expr) => Recovered::Complete(*type_expr),
                Recovered::Incomplete => Recovered::Incomplete,
            }
        }
    };
    if let Some(owner) = owner {
        assert_eq!(i.local.pop_type_delimited_owner(), Some(owner));
    }
    match parsed {
        Recovered::Complete(type_expr) => {
            let range = type_expr.range();
            Recovered::Complete(StructTupleField {
                type_expr: Recovered::Complete(Box::new(type_expr)),
                range,
            })
        }
        Recovered::Incomplete => Recovered::Incomplete,
    }
}

/// Parse a complete variant payload after its raw name.  This stays detached
/// from the declaration header and real statement dispatch; Gate 7 owns that
/// form-level composition.  The priority is intentionally syntactic and
/// left-to-right so `from`, `{`, and `(` never leak into positional parsing.
pub(super) fn parse_variant_declaration_payload_ast<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    form: VariantDeclarationSequenceForm,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EnumVariantPayload<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    // Named and tuple payload delimiters are owned immediately after the raw
    // variant name. Their grammar has no required payload trivia, so `B(T)`
    // and `A { field: T }` must outrank both unit and positional evidence.
    if let Some(open) = enum_variant_payload_open(Delimiter::Brace, i) {
        return parse_variant_declaration_named_payload_ast(owner, form, open, i);
    }
    if let Some(open) = enum_variant_payload_open(Delimiter::Parenthesis, i) {
        return parse_variant_declaration_tuple_payload_ast(owner, form, open, i);
    }
    let Some(_) = consume_enum_variant_payload_trivia(i) else {
        return EnumVariantPayload::Unit;
    };
    if let Some(keyword) = enum_variant_exact_from_pending(i) {
        let _ = consume_enum_variant_payload_trivia(i);
        let type_expr = parse_required_variant_declaration_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::FromType,
            form,
            i,
        );
        let end = match &type_expr {
            Recovered::Complete(type_expr) => type_expr.range().end,
            Recovered::Incomplete => keyword.end,
        };
        return EnumVariantPayload::From {
            keyword: keyword.clone(),
            type_expr,
            range: keyword.start..end,
        };
    }
    if let Some(open) = enum_variant_payload_open(Delimiter::Brace, i) {
        return parse_variant_declaration_named_payload_ast(owner, form, open, i);
    }
    if let Some(open) = enum_variant_payload_open(Delimiter::Parenthesis, i) {
        return parse_variant_declaration_tuple_payload_ast(owner, form, open, i);
    }
    if enum_variant_positional_payload_pending(form, i) {
        let first = parse_required_variant_declaration_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::PositionalPayload,
            form,
            i,
        );
        let start = match &first {
            Recovered::Complete(type_expr) => type_expr.range().start,
            Recovered::Incomplete => i.pos(),
        };
        let mut types = vec![first];
        loop {
            let position = i.checkpoint();
            if consume_enum_variant_payload_trivia(i).is_none()
                || !enum_variant_positional_payload_pending(form, i)
            {
                i.rollback(position);
                break;
            }
            types.push(parse_required_variant_declaration_type_expression(
                owner,
                EnumVariantTypeExpressionSlot::PositionalPayload,
                form,
                i,
            ));
        }
        let end = types
            .iter()
            .rev()
            .find_map(|item| match item {
                Recovered::Complete(type_expr) => Some(type_expr.range().end),
                Recovered::Incomplete => None,
            })
            .unwrap_or(start);
        return EnumVariantPayload::Positional {
            types,
            range: start..end,
        };
    }
    i.rollback(checkpoint);
    EnumVariantPayload::Unit
}

struct CompanionVariantPayloadResult<'source> {
    payload: EnumVariantPayload<'source>,
    exit: CompanionVariantTypeExit,
}

fn companion_variant_payload_normal(
    payload: EnumVariantPayload<'_>,
) -> CompanionVariantPayloadResult<'_> {
    CompanionVariantPayloadResult {
        payload,
        exit: CompanionVariantTypeExit::Normal,
    }
}

fn parse_companion_variant_payload_ast<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> CompanionVariantPayloadResult<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    if let Some(open) = enum_variant_payload_open(Delimiter::Brace, i) {
        return companion_variant_payload_normal(parse_variant_declaration_named_payload_ast(
            owner,
            VariantDeclarationSequenceForm::EqualsInline,
            open,
            i,
        ));
    }
    if let Some(open) = enum_variant_payload_open(Delimiter::Parenthesis, i) {
        return companion_variant_payload_normal(parse_variant_declaration_tuple_payload_ast(
            owner,
            VariantDeclarationSequenceForm::EqualsInline,
            open,
            i,
        ));
    }
    if recognize_declaration_companion_handoff(owner.declaration_base, i).is_some() {
        return companion_variant_payload_normal(EnumVariantPayload::Unit);
    }
    let Some(_) = consume_enum_variant_payload_trivia(i) else {
        return companion_variant_payload_normal(EnumVariantPayload::Unit);
    };
    if let Some(keyword) = enum_variant_exact_from_pending(i) {
        let type_result =
            if recognize_declaration_companion_handoff(owner.declaration_base, i).is_some() {
                CompanionVariantTypeResult {
                    value: Recovered::Incomplete,
                    exit: CompanionVariantTypeExit::Normal,
                }
            } else {
                let _ = consume_enum_variant_payload_trivia(i);
                parse_required_companion_variant_type_expression(
                    owner,
                    EnumVariantTypeExpressionSlot::FromType,
                    i,
                )
            };
        let type_expr = type_result.value;
        let end = match &type_expr {
            Recovered::Complete(type_expr) => type_expr.range().end,
            Recovered::Incomplete => keyword.end,
        };
        return CompanionVariantPayloadResult {
            payload: EnumVariantPayload::From {
                keyword: keyword.clone(),
                type_expr,
                range: keyword.start..end,
            },
            exit: type_result.exit,
        };
    }
    if let Some(open) = enum_variant_payload_open(Delimiter::Brace, i) {
        return companion_variant_payload_normal(parse_variant_declaration_named_payload_ast(
            owner,
            VariantDeclarationSequenceForm::EqualsInline,
            open,
            i,
        ));
    }
    if let Some(open) = enum_variant_payload_open(Delimiter::Parenthesis, i) {
        return companion_variant_payload_normal(parse_variant_declaration_tuple_payload_ast(
            owner,
            VariantDeclarationSequenceForm::EqualsInline,
            open,
            i,
        ));
    }
    if enum_variant_positional_payload_pending(VariantDeclarationSequenceForm::EqualsInline, i)
        || companion_variant_malformed_positional_pending(owner, i)
    {
        let first = parse_required_companion_variant_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::PositionalPayload,
            i,
        );
        let mut exit = first.exit;
        let start = match &first.value {
            Recovered::Complete(type_expr) => type_expr.range().start,
            Recovered::Incomplete => i.pos(),
        };
        let mut types = vec![first.value];
        loop {
            let position = i.checkpoint();
            if recognize_declaration_companion_handoff(owner.declaration_base, i).is_some()
                || consume_enum_variant_payload_trivia(i).is_none()
                || !enum_variant_positional_payload_pending(
                    VariantDeclarationSequenceForm::EqualsInline,
                    i,
                )
            {
                i.rollback(position);
                break;
            }
            let next = parse_required_companion_variant_type_expression(
                owner,
                EnumVariantTypeExpressionSlot::PositionalPayload,
                i,
            );
            if matches!(next.exit, CompanionVariantTypeExit::ItemContinuation) {
                exit = next.exit;
            }
            types.push(next.value);
        }
        let end = types
            .iter()
            .rev()
            .find_map(|item| match item {
                Recovered::Complete(type_expr) => Some(type_expr.range().end),
                Recovered::Incomplete => None,
            })
            .unwrap_or(start);
        return CompanionVariantPayloadResult {
            payload: EnumVariantPayload::Positional {
                types,
                range: start..end,
            },
            exit,
        };
    }
    i.rollback(checkpoint);
    companion_variant_payload_normal(EnumVariantPayload::Unit)
}

fn companion_variant_malformed_positional_pending<E>(
    owner: VariantDeclarationOwnerSpec,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() || any_ambient_owner_claims(i) {
        return false;
    }
    let spec = variant_declaration_sequence_spec(
        VariantDeclarationSequenceForm::EqualsInline,
        LayoutDelimitedFrame::inline(owner.declaration_base),
        owner.declaration_base,
    );
    let checkpoint = i.checkpoint();
    let separator = scan_enum_variant_separator_at_cursor(spec, i).is_some();
    i.rollback(checkpoint);
    !separator && !enum_variant_terminal_boundary_pending(spec, i)
}

pub(super) fn parse_variant_declaration_named_payload_ast<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    _form: VariantDeclarationSequenceForm,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EnumVariantPayload<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .without(StopKind::Newline)
        .with(StopKind::Comma)
        .with(StopKind::RightBrace);
    i.local.push_delimiter(Delimiter::Brace);
    i.local.push_stop_set(stops);
    let opening = i.run(scan_trivia).expect("trivia is total");
    let layout =
        LayoutDelimitedFrame::after_opening_trivia(0, &opening, i.local.line().line_indent);
    push_struct_layout(layout, i);
    let mut fields = Vec::new();
    let mut trailing_comma = None;
    let close = loop {
        if let Some(close) = scan_struct_close_brace(i) {
            break Recovered::Complete(close);
        }
        if i.input.remainder().is_empty() || struct_outer_owned_mismatched_close_pending(i) {
            break Recovered::Incomplete;
        }
        if scan_struct_comma(i).is_some() {
            fields.push(Recovered::Incomplete);
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        let field = parse_variant_named_field_ast(owner.field_driver, true, i)
            .map(Recovered::Complete)
            .unwrap_or(Recovered::Incomplete);
        let incomplete = matches!(field, Recovered::Incomplete);
        fields.push(field);
        if incomplete || any_ambient_owner_claims(i) {
            break Recovered::Incomplete;
        }
        let trivia = i.run(scan_trivia).expect("trivia is total");
        if let Some(comma) = scan_struct_comma(i) {
            let _ = i.run(scan_trivia).expect("trivia is total");
            if let Some(close) = scan_struct_close_brace(i) {
                trailing_comma = Some(comma);
                break Recovered::Complete(close);
            }
            continue;
        }
        if let Some(close) = scan_struct_close_brace(i) {
            break Recovered::Complete(close);
        }
        if layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
            == LayoutDelimitedBoundary::ImplicitNewline
        {
            continue;
        }
        break Recovered::Incomplete;
    };
    pop_struct_layout(layout, i);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    EnumVariantPayload::Named {
        open: open.clone(),
        fields,
        trailing_comma,
        close,
        range: open.start..end,
    }
}

pub(super) fn parse_variant_declaration_tuple_payload_ast<'source, E>(
    owner: VariantDeclarationOwnerSpec,
    _form: VariantDeclarationSequenceForm,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EnumVariantPayload<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .without(StopKind::Newline)
        .with(StopKind::Comma)
        .with(StopKind::RightParenthesis);
    i.local.push_delimiter(Delimiter::Parenthesis);
    i.local.push_stop_set(stops);
    let _ = i.run(scan_trivia).expect("trivia is total");
    let mut fields = Vec::new();
    let mut trailing_comma = None;
    let close = loop {
        if let Some(close) = scan_struct_close_parenthesis(i) {
            break Recovered::Complete(close);
        }
        if i.input.remainder().is_empty()
            || struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, i)
        {
            break Recovered::Incomplete;
        }
        if scan_struct_comma(i).is_some() {
            fields.push(Recovered::Incomplete);
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        let field = parse_variant_tuple_field_ast(owner.field_driver.tuple_payload(), i);
        let incomplete = matches!(field, Recovered::Incomplete);
        fields.push(field);
        if incomplete || any_ambient_owner_claims(i) {
            break Recovered::Incomplete;
        }
        let trivia = i.run(scan_trivia).expect("trivia is total");
        if let Some(comma) = scan_struct_comma(i) {
            let _ = i.run(scan_trivia).expect("trivia is total");
            if let Some(close) = scan_struct_close_parenthesis(i) {
                trailing_comma = Some(comma);
                break Recovered::Complete(close);
            }
            continue;
        }
        if let Some(close) = scan_struct_close_parenthesis(i) {
            break Recovered::Complete(close);
        }
        if LayoutDelimitedFrame::inline(0)
            .boundary_after_trivia(&trivia, i.local.line().line_indent)
            == LayoutDelimitedBoundary::ImplicitNewline
        {
            continue;
        }
        break Recovered::Incomplete;
    };
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    EnumVariantPayload::Tuple {
        open: open.clone(),
        fields,
        trailing_comma,
        close,
        range: open.start..end,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedEnumVariantSequence<'source> {
    pub(super) variants: Vec<Recovered<EnumVariant<'source>>>,
    pub(super) trailing_comma: Option<Range<usize>>,
    pub(super) trailing_pipe: Option<Range<usize>>,
    pub(super) close: Recovered<Range<usize>>,
    pub(super) termination: EnumVariantSequenceTermination,
}

pub(super) struct AstEnumVariantPayloadContext<
    'context,
    'parse,
    'source,
    'local,
    E: ErrorSink<usize>,
> {
    pub(super) i: &'context mut SynIn<'parse, 'source, 'local, E>,
    pub(super) spec: VariantDeclarationSequenceSpec,
    pub(super) owner: VariantDeclarationOwnerSpec,
    pub(super) variants: Vec<Recovered<EnumVariant<'source>>>,
    pub(super) trailing_comma: Option<Range<usize>>,
    pub(super) trailing_pipe: Option<Range<usize>>,
    pub(super) close: Recovered<Range<usize>>,
}

impl<'source, E> VariantDeclarationSequenceContext<'source>
    for AstEnumVariantPayloadContext<'_, '_, 'source, '_, E>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    type Error = E;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, E>) -> R) -> R {
        f(self.i)
    }

    fn emit_trivia(&mut self, _trivia: &TriviaRun) {}

    fn emit_missing_variant(&mut self) {
        self.variants.push(Recovered::Incomplete);
    }

    fn emit_separator(&mut self, _separator: EnumVariantSeparator) {}

    fn set_trailing_separator(&mut self, separator: EnumVariantSeparator) {
        match separator {
            EnumVariantSeparator::Comma(range) => self.trailing_comma = Some(range),
            EnumVariantSeparator::Pipe(range) => self.trailing_pipe = Some(range),
        }
    }

    fn emit_matching_close(&mut self, close: Range<usize>) {
        self.close = Recovered::Complete(close);
    }

    fn parse_variant_item(&mut self, malformed: Option<Range<usize>>) -> bool {
        let start = malformed
            .as_ref()
            .map_or_else(|| self.i.pos(), |range| range.start);
        if let Some(range) = malformed {
            while self.i.pos() < range.end {
                self.i
                    .input
                    .next()
                    .expect("the selected Enum variant error range remains available");
                let mut line = self.i.local.line();
                line.at_line_start = false;
                self.i.local.set_line(line);
            }
        }
        let Some(name) = self.i.run(scan_word) else {
            self.variants.push(Recovered::Incomplete);
            return true;
        };
        let payload = parse_variant_declaration_payload_ast(self.owner, self.spec.form, self.i);
        let end = match &payload {
            EnumVariantPayload::Unit => name.range().end,
            EnumVariantPayload::From { range, .. }
            | EnumVariantPayload::Named { range, .. }
            | EnumVariantPayload::Tuple { range, .. }
            | EnumVariantPayload::Positional { range, .. } => range.end,
        };
        self.variants.push(Recovered::Complete(EnumVariant {
            name: Recovered::Complete(name),
            payload,
            range: start..end,
        }));
        true
    }
}

/// The Gate 6 payload adapter replaces Gate 5's raw-word stub without taking
/// ownership of an Enum header or body-form starter.  Later form adapters
/// supply the frame and consume the returned close/boundary fact.
pub(super) fn parse_variant_declaration_sequence_with_payload<'source, E>(
    spec: VariantDeclarationSequenceSpec,
    owner: VariantDeclarationOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedEnumVariantSequence<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut context = AstEnumVariantPayloadContext {
        i,
        spec,
        owner,
        variants: Vec::new(),
        trailing_comma: None,
        trailing_pipe: None,
        close: Recovered::Incomplete,
    };
    debug_assert_eq!(spec.declaration_base, owner.declaration_base);
    let termination = drive_variant_declaration_sequence(&mut context, spec);
    ParsedEnumVariantSequence {
        variants: context.variants,
        trailing_comma: context.trailing_comma,
        trailing_pipe: context.trailing_pipe,
        close: context.close,
        termination,
    }
}

struct AstCompanionVariantPayloadContext<'context, 'parse, 'source, 'local, E: ErrorSink<usize>> {
    i: &'context mut SynIn<'parse, 'source, 'local, E>,
    owner: VariantDeclarationOwnerSpec,
    variants: Vec<Recovered<EnumVariant<'source>>>,
    trailing_comma: Option<Range<usize>>,
    trailing_pipe: Option<Range<usize>>,
    close: Recovered<Range<usize>>,
    item_continuation: bool,
}

impl<'source, E> VariantDeclarationSequenceContext<'source>
    for AstCompanionVariantPayloadContext<'_, '_, 'source, '_, E>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    type Error = E;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, E>) -> R) -> R {
        f(self.i)
    }

    fn emit_trivia(&mut self, _trivia: &TriviaRun) {}

    fn emit_missing_variant(&mut self) {
        self.variants.push(Recovered::Incomplete);
    }

    fn emit_separator(&mut self, _separator: EnumVariantSeparator) {}

    fn set_trailing_separator(&mut self, separator: EnumVariantSeparator) {
        match separator {
            EnumVariantSeparator::Comma(range) => self.trailing_comma = Some(range),
            EnumVariantSeparator::Pipe(range) => self.trailing_pipe = Some(range),
        }
    }

    fn emit_matching_close(&mut self, close: Range<usize>) {
        self.close = Recovered::Complete(close);
    }

    fn parse_variant_item(&mut self, malformed: Option<Range<usize>>) -> bool {
        let start = malformed
            .as_ref()
            .map_or_else(|| self.i.pos(), |range| range.start);
        if let Some(range) = malformed {
            while self.i.pos() < range.end {
                self.i
                    .input
                    .next()
                    .expect("the selected companion variant error range remains available");
                let mut line = self.i.local.line();
                line.at_line_start = false;
                self.i.local.set_line(line);
            }
        }
        let Some(name) = self.i.run(scan_word) else {
            self.variants.push(Recovered::Incomplete);
            return true;
        };
        let payload = parse_companion_variant_payload_ast(self.owner, self.i);
        self.item_continuation = matches!(payload.exit, CompanionVariantTypeExit::ItemContinuation);
        let end = match &payload.payload {
            EnumVariantPayload::Unit => name.range().end,
            EnumVariantPayload::From { range, .. }
            | EnumVariantPayload::Named { range, .. }
            | EnumVariantPayload::Tuple { range, .. }
            | EnumVariantPayload::Positional { range, .. } => range.end,
        };
        self.variants.push(Recovered::Complete(EnumVariant {
            name: Recovered::Complete(name),
            payload: payload.payload,
            range: start..end,
        }));
        true
    }
}

impl<'source, E> CompanionVariantSequenceContext<'source>
    for AstCompanionVariantPayloadContext<'_, '_, 'source, '_, E>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    fn take_item_continuation(&mut self) -> bool {
        std::mem::take(&mut self.item_continuation)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedVariantDeclarationSequenceWithTail<'source> {
    pub(super) sequence: ParsedEnumVariantSequence<'source>,
    pub(super) tail: Option<VariantDeclarationCompanionOwnerTail>,
}

pub(super) fn parse_variant_declaration_sequence_with_companion_handoff_isolated<'source, E>(
    spec: VariantDeclarationSequenceSpec,
    owner: VariantDeclarationOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedVariantDeclarationSequenceWithTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    debug_assert_eq!(spec.declaration_base, owner.declaration_base);
    let mut context = AstCompanionVariantPayloadContext {
        i,
        owner,
        variants: Vec::new(),
        trailing_comma: None,
        trailing_pipe: None,
        close: Recovered::Incomplete,
        item_continuation: false,
    };
    let (termination, handed_off) =
        drive_equals_inline_variant_sequence_with_companion_handoff(&mut context, spec);
    ParsedVariantDeclarationSequenceWithTail {
        sequence: ParsedEnumVariantSequence {
            variants: context.variants,
            trailing_comma: context.trailing_comma,
            trailing_pipe: context.trailing_pipe,
            close: context.close,
            termination,
        },
        tail: handed_off.then_some(VariantDeclarationCompanionOwnerTail { owner: owner.owner }),
    }
}

/// Retains the Enum-only fixture entry point while production body adapters
/// pass their owner spec explicitly to the neutral core.
pub(super) fn parse_enum_variant_sequence_with_payload<'source, E>(
    spec: EnumVariantSequenceSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedEnumVariantSequence<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_variant_declaration_sequence_with_payload(
        spec,
        enum_variant_declaration_owner_spec(spec.declaration_base),
        i,
    )
}

pub(super) fn emit_variant_declaration_missing<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
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

fn emit_variant_declaration_missing_at<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    at: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: ExpectedSyntax,
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
                expected,
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

pub(super) fn emit_enum_variant_item_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(SyntaxKind::EnumVariant);
    emit_variant_declaration_missing(
        enum_variant_declaration_owner_spec(0).item_role,
        committed,
        ExpectedSyntax::Identifier,
    );
    committed.finish_node();
}

pub(super) fn emit_error_variant_item_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(SyntaxKind::EnumVariant);
    emit_variant_declaration_missing(
        error_variant_declaration_owner_spec(0).item_role,
        committed,
        ExpectedSyntax::Identifier,
    );
    committed.finish_node();
}

pub(super) fn emit_enum_declaration_error<'parse, 'source, 'local, E, O>(
    enum_role: EnumDeclarationRole,
    range: Range<usize>,
    expected: ExpectedSyntax,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Enum(enum_role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
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

pub(super) fn emit_error_declaration_error<'parse, 'source, 'local, E, O>(
    error_role: ErrorDeclarationRole,
    range: Range<usize>,
    expected: ExpectedSyntax,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Error(error_role));
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
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

pub(super) fn emit_enum_braced_close_error<'parse, 'source, 'local, E, O>(
    range: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::EnumBracedVariantBody,
            delimiter: Delimiter::Brace,
        };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    Delimiter::Brace,
                )),
                range: range.clone(),
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

pub(super) fn emit_enum_braced_close_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter {
            owner: ConstructRole::EnumBracedVariantBody,
            delimiter: Delimiter::Brace,
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
                    Delimiter::Brace,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

pub(super) fn emit_variant_declaration_error<'parse, 'source, 'local, E, O>(
    role: GrammarRole,
    range: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
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

pub(super) fn emit_variant_payload_missing_close<'parse, 'source, 'local, E, O>(
    owner: ConstructRole,
    delimiter: Delimiter,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::ClosingDelimiter { owner, delimiter };
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
                    delimiter,
                )),
                range: at..at,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_missing(record);
}

pub(super) fn commit_variant_tuple_field<'parse, 'source, 'local, E, O>(
    spec: VariantFieldDriverSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::StructField);
    let owner = (spec != VariantFieldDriverSpec::Struct).then(|| spec.named_type_owner());
    if let Some(owner) = owner {
        committed.probe(|probe| {
            probe.input().local.push_type_delimited_owner(owner);
        });
    }
    match spec {
        VariantFieldDriverSpec::Struct => {
            let _ = commit_direct_type_expression_with_outer_missing_role(
                Some(spec.type_role()),
                committed,
            );
        }
        VariantFieldDriverSpec::EnumNamed
        | VariantFieldDriverSpec::EnumTuple
        | VariantFieldDriverSpec::ErrorNamed
        | VariantFieldDriverSpec::ErrorTuple => {
            let _ =
                commit_required_variant_declaration_tuple_field_type_expression(spec, committed);
        }
    }
    if let Some(owner) = owner {
        committed.probe(|probe| {
            assert_eq!(probe.input().local.pop_type_delimited_owner(), Some(owner));
        });
    }
    committed.finish_node();
}

pub(super) fn commit_variant_declaration_named_payload<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    _form: VariantDeclarationSequenceForm,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.token(SyntaxKind::LBrace, open);
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
            .with(StopKind::RightBrace)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_delimiter(Delimiter::Brace);
        i.local.push_stop_set(stops);
    });
    let opening = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia is total");
    committed.emit_trivia(&opening);
    let layout = committed.probe(|probe| {
        LayoutDelimitedFrame::after_opening_trivia(
            0,
            &opening,
            probe.input().local.line().line_indent,
        )
    });
    committed.probe(|probe| push_struct_layout(layout, probe.input()));
    loop {
        if let Some(close) = committed.probe(|probe| scan_struct_close_brace(probe.input())) {
            committed.token(SyntaxKind::RBrace, close);
            break;
        }
        if committed.probe(|probe| {
            probe.input().input.remainder().is_empty()
                || struct_outer_owned_mismatched_close_pending(probe.input())
        }) {
            emit_variant_payload_missing_close(
                ConstructRole::VariantNamedPayload,
                Delimiter::Brace,
                committed,
            );
            break;
        }
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.start_node(SyntaxKind::StructField);
            emit_variant_field_missing(
                owner.field_driver,
                VariantFieldRecoverySlot::Item,
                committed,
                ExpectedSyntax::Identifier,
            );
            committed.finish_node();
            committed.token(SyntaxKind::Comma, comma);
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if !commit_variant_named_field(owner.field_driver, true, committed) {
            if let Some(run) =
                committed.probe(|probe| scan_struct_field_invalid_run(false, probe.input()))
            {
                committed.start_node(SyntaxKind::StructField);
                emit_variant_field_error(
                    owner.field_driver,
                    VariantFieldRecoverySlot::Item,
                    committed,
                    run.range.clone(),
                    ExpectedSyntax::Identifier,
                );
                committed.probe(|probe| consume_source_range(run.range, probe.input()));
                committed.finish_node();
            } else {
                committed.start_node(SyntaxKind::StructField);
                emit_variant_field_missing(
                    owner.field_driver,
                    VariantFieldRecoverySlot::Item,
                    committed,
                    ExpectedSyntax::Identifier,
                );
                committed.finish_node();
                emit_variant_payload_missing_close(
                    ConstructRole::VariantNamedPayload,
                    Delimiter::Brace,
                    committed,
                );
                break;
            }
        }
        let trivia = committed
            .probe(|probe| probe.input().run(scan_trivia))
            .expect("trivia is total");
        committed.emit_trivia(&trivia);
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            let post = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&post);
            continue;
        }
        if let Some(close) = committed.probe(|probe| scan_struct_close_brace(probe.input())) {
            committed.token(SyntaxKind::RBrace, close);
            break;
        }
        if committed.probe(|probe| {
            layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)
                == LayoutDelimitedBoundary::ImplicitNewline
        }) {
            continue;
        }
        emit_variant_payload_missing_close(
            ConstructRole::VariantNamedPayload,
            Delimiter::Brace,
            committed,
        );
        break;
    }
    committed.probe(|probe| {
        let i = probe.input();
        pop_struct_layout(layout, i);
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    });
}

pub(super) fn commit_variant_declaration_tuple_payload<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    _form: VariantDeclarationSequenceForm,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.token(SyntaxKind::LParen, open);
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
            .with(StopKind::RightParenthesis)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_delimiter(Delimiter::Parenthesis);
        i.local.push_stop_set(stops);
    });
    let opening = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia is total");
    committed.emit_trivia(&opening);
    loop {
        if let Some(close) = committed.probe(|probe| scan_struct_close_parenthesis(probe.input())) {
            committed.token(SyntaxKind::RParen, close);
            break;
        }
        if committed.probe(|probe| {
            probe.input().input.remainder().is_empty()
                || struct_outer_owned_mismatched_close_pending_for(
                    Delimiter::Parenthesis,
                    probe.input(),
                )
        }) {
            emit_variant_payload_missing_close(
                ConstructRole::VariantTuplePayload,
                Delimiter::Parenthesis,
                committed,
            );
            break;
        }
        if committed.probe(|probe| scan_struct_comma_pending(probe.input())) {
            commit_variant_tuple_field(owner.field_driver.tuple_payload(), committed);
            let comma = committed
                .probe(|probe| scan_struct_comma(probe.input()))
                .expect("the empty Enum tuple field slot is followed by its comma");
            committed.token(SyntaxKind::Comma, comma);
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        commit_variant_tuple_field(owner.field_driver.tuple_payload(), committed);
        let trivia = committed
            .probe(|probe| probe.input().run(scan_trivia))
            .expect("trivia is total");
        committed.emit_trivia(&trivia);
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            let post = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&post);
            continue;
        }
        if let Some(close) = committed.probe(|probe| scan_struct_close_parenthesis(probe.input())) {
            committed.token(SyntaxKind::RParen, close);
            break;
        }
        emit_variant_payload_missing_close(
            ConstructRole::VariantTuplePayload,
            Delimiter::Parenthesis,
            committed,
        );
        break;
    }
    committed.probe(|probe| {
        let i = probe.input();
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    });
}

pub(super) fn commit_variant_declaration_payload<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    form: VariantDeclarationSequenceForm,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Brace, probe.input()))
    {
        commit_variant_declaration_named_payload(owner, form, open, committed);
        return;
    }
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Parenthesis, probe.input()))
    {
        commit_variant_declaration_tuple_payload(owner, form, open, committed);
        return;
    }
    let gap = committed.probe(|probe| consume_enum_variant_payload_trivia(probe.input()));
    let Some(gap) = gap else {
        return;
    };
    if let Some(keyword) = committed.probe(|probe| enum_variant_exact_from_pending(probe.input())) {
        committed.emit_trivia(&gap);
        committed.token(SyntaxKind::FromKw, keyword);
        if let Some(trivia) =
            committed.probe(|probe| consume_enum_variant_payload_trivia(probe.input()))
        {
            committed.emit_trivia(&trivia);
        }
        let _ = commit_required_variant_declaration_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::FromType,
            form,
            committed,
        );
        return;
    }
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Brace, probe.input()))
    {
        committed.emit_trivia(&gap);
        commit_variant_declaration_named_payload(owner, form, open, committed);
        return;
    }
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Parenthesis, probe.input()))
    {
        committed.emit_trivia(&gap);
        commit_variant_declaration_tuple_payload(owner, form, open, committed);
        return;
    }
    if committed.probe(|probe| enum_variant_positional_payload_pending(form, probe.input())) {
        committed.emit_trivia(&gap);
        let _ = commit_required_variant_declaration_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::PositionalPayload,
            form,
            committed,
        );
        loop {
            let checkpoint = committed.probe(|probe| probe.input().checkpoint());
            let Some(trivia) =
                committed.probe(|probe| consume_enum_variant_payload_trivia(probe.input()))
            else {
                break;
            };
            if !committed
                .probe(|probe| enum_variant_positional_payload_pending(form, probe.input()))
            {
                committed.probe(|probe| probe.input().rollback(checkpoint));
                break;
            }
            committed.emit_trivia(&trivia);
            let _ = commit_required_variant_declaration_type_expression(
                owner,
                EnumVariantTypeExpressionSlot::PositionalPayload,
                form,
                committed,
            );
        }
        return;
    }
    committed.probe(|probe| probe.input().rollback(checkpoint));
}

fn commit_companion_variant_payload<'parse, 'source, 'local, E, O>(
    owner: VariantDeclarationOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> CompanionVariantTypeExit
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = committed.probe(|probe| probe.input().checkpoint());
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Brace, probe.input()))
    {
        commit_variant_declaration_named_payload(
            owner,
            VariantDeclarationSequenceForm::EqualsInline,
            open,
            committed,
        );
        return CompanionVariantTypeExit::Normal;
    }
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Parenthesis, probe.input()))
    {
        commit_variant_declaration_tuple_payload(
            owner,
            VariantDeclarationSequenceForm::EqualsInline,
            open,
            committed,
        );
        return CompanionVariantTypeExit::Normal;
    }
    if committed.probe(|probe| {
        recognize_declaration_companion_handoff(owner.declaration_base, probe.input()).is_some()
    }) {
        return CompanionVariantTypeExit::Normal;
    }
    let gap = committed.probe(|probe| consume_enum_variant_payload_trivia(probe.input()));
    let Some(gap) = gap else {
        return CompanionVariantTypeExit::Normal;
    };
    if let Some(keyword) = committed.probe(|probe| enum_variant_exact_from_pending(probe.input())) {
        committed.emit_trivia(&gap);
        committed.token(SyntaxKind::FromKw, keyword.clone());
        if let Some(with) = committed.probe(|probe| {
            recognize_declaration_companion_handoff(owner.declaration_base, probe.input())
        }) {
            emit_variant_declaration_missing_at(
                owner.from_type_role,
                with.start,
                committed,
                ExpectedSyntax::TypeExpression,
            );
            return CompanionVariantTypeExit::Normal;
        } else {
            if let Some(trivia) =
                committed.probe(|probe| consume_enum_variant_payload_trivia(probe.input()))
            {
                committed.emit_trivia(&trivia);
            }
            let type_result = commit_required_companion_variant_type_expression(
                owner,
                EnumVariantTypeExpressionSlot::FromType,
                committed,
            );
            return type_result.exit;
        }
    }
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Brace, probe.input()))
    {
        committed.emit_trivia(&gap);
        commit_variant_declaration_named_payload(
            owner,
            VariantDeclarationSequenceForm::EqualsInline,
            open,
            committed,
        );
        return CompanionVariantTypeExit::Normal;
    }
    if let Some(open) =
        committed.probe(|probe| enum_variant_payload_open(Delimiter::Parenthesis, probe.input()))
    {
        committed.emit_trivia(&gap);
        commit_variant_declaration_tuple_payload(
            owner,
            VariantDeclarationSequenceForm::EqualsInline,
            open,
            committed,
        );
        return CompanionVariantTypeExit::Normal;
    }
    if committed.probe(|probe| {
        let i = probe.input();
        enum_variant_positional_payload_pending(VariantDeclarationSequenceForm::EqualsInline, i)
            || companion_variant_malformed_positional_pending(owner, i)
    }) {
        committed.emit_trivia(&gap);
        let first = commit_required_companion_variant_type_expression(
            owner,
            EnumVariantTypeExpressionSlot::PositionalPayload,
            committed,
        );
        let mut exit = first.exit;
        loop {
            let position = committed.probe(|probe| probe.input().checkpoint());
            if committed.probe(|probe| {
                recognize_declaration_companion_handoff(owner.declaration_base, probe.input())
                    .is_some()
            }) {
                break;
            }
            let Some(trivia) =
                committed.probe(|probe| consume_enum_variant_payload_trivia(probe.input()))
            else {
                break;
            };
            if !committed.probe(|probe| {
                enum_variant_positional_payload_pending(
                    VariantDeclarationSequenceForm::EqualsInline,
                    probe.input(),
                )
            }) {
                committed.probe(|probe| probe.input().rollback(position));
                break;
            }
            committed.emit_trivia(&trivia);
            let next = commit_required_companion_variant_type_expression(
                owner,
                EnumVariantTypeExpressionSlot::PositionalPayload,
                committed,
            );
            if matches!(next.exit, CompanionVariantTypeExit::ItemContinuation) {
                exit = next.exit;
            }
        }
        return exit;
    }
    committed.probe(|probe| probe.input().rollback(checkpoint));
    CompanionVariantTypeExit::Normal
}

pub(super) struct DirectEnumVariantPayloadContext<
    'context,
    'parse,
    'source,
    'local,
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
> {
    pub(super) committed: &'context mut Committed<'parse, 'source, 'local, E, O>,
    pub(super) spec: VariantDeclarationSequenceSpec,
    pub(super) owner: VariantDeclarationOwnerSpec,
}

impl<'source, E, O> VariantDeclarationSequenceContext<'source>
    for DirectEnumVariantPayloadContext<'_, '_, 'source, '_, E, O>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    type Error = E;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, E>) -> R) -> R {
        self.committed.probe(|probe| f(probe.input()))
    }

    fn emit_trivia(&mut self, trivia: &TriviaRun) {
        self.committed.emit_trivia(trivia);
    }

    fn emit_missing_variant(&mut self) {
        self.committed.start_node(SyntaxKind::EnumVariant);
        emit_variant_declaration_missing(
            self.owner.item_role,
            self.committed,
            ExpectedSyntax::Identifier,
        );
        self.committed.finish_node();
    }

    fn emit_separator(&mut self, separator: EnumVariantSeparator) {
        match separator {
            EnumVariantSeparator::Comma(range) => self.committed.token(SyntaxKind::Comma, range),
            EnumVariantSeparator::Pipe(range) => self.committed.token(SyntaxKind::Pipe, range),
        }
    }

    fn set_trailing_separator(&mut self, _separator: EnumVariantSeparator) {}

    fn emit_matching_close(&mut self, close: Range<usize>) {
        self.committed.token(SyntaxKind::RBrace, close);
    }

    fn parse_variant_item(&mut self, malformed: Option<Range<usize>>) -> bool {
        self.committed.start_node(SyntaxKind::EnumVariant);
        if let Some(range) = malformed {
            let has_raw_name_retry = self
                .committed
                .probe(|probe| enum_variant_raw_name_pending(probe.input()));
            emit_variant_declaration_error(
                if has_raw_name_retry {
                    self.owner.variant_role(VariantDeclarationRole::Name)
                } else {
                    self.owner.item_role
                },
                range.clone(),
                self.committed,
                ExpectedSyntax::Identifier,
            );
            if !has_raw_name_retry {
                self.committed.finish_node();
                return true;
            }
        }
        let Some(name) = self.committed.probe(|probe| probe.input().run(scan_word)) else {
            emit_variant_declaration_missing(
                self.owner.variant_role(VariantDeclarationRole::Name),
                self.committed,
                ExpectedSyntax::Identifier,
            );
            self.committed.finish_node();
            return true;
        };
        self.committed.token(SyntaxKind::Identifier, name.range());
        commit_variant_declaration_payload(self.owner, self.spec.form, self.committed);
        self.committed.finish_node();
        true
    }
}

pub(super) fn commit_variant_declaration_sequence_with_payload<'parse, 'source, 'local, E, O>(
    spec: VariantDeclarationSequenceSpec,
    owner: VariantDeclarationOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> EnumVariantSequenceTermination
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    debug_assert_eq!(spec.declaration_base, owner.declaration_base);
    let mut context = DirectEnumVariantPayloadContext {
        committed,
        spec,
        owner,
    };
    drive_variant_declaration_sequence(&mut context, spec)
}

struct DirectCompanionVariantPayloadContext<
    'context,
    'parse,
    'source,
    'local,
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
> {
    committed: &'context mut Committed<'parse, 'source, 'local, E, O>,
    owner: VariantDeclarationOwnerSpec,
    item_continuation: bool,
}

impl<'source, E, O> VariantDeclarationSequenceContext<'source>
    for DirectCompanionVariantPayloadContext<'_, '_, 'source, '_, E, O>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    type Error = E;

    fn with_input<R>(&mut self, f: impl FnOnce(&mut SynIn<'_, 'source, '_, E>) -> R) -> R {
        self.committed.probe(|probe| f(probe.input()))
    }

    fn emit_trivia(&mut self, trivia: &TriviaRun) {
        self.committed.emit_trivia(trivia);
    }

    fn emit_missing_variant(&mut self) {
        self.committed.start_node(SyntaxKind::EnumVariant);
        emit_variant_declaration_missing(
            self.owner.item_role,
            self.committed,
            ExpectedSyntax::Identifier,
        );
        self.committed.finish_node();
    }

    fn emit_separator(&mut self, separator: EnumVariantSeparator) {
        match separator {
            EnumVariantSeparator::Comma(range) => self.committed.token(SyntaxKind::Comma, range),
            EnumVariantSeparator::Pipe(range) => self.committed.token(SyntaxKind::Pipe, range),
        }
    }

    fn set_trailing_separator(&mut self, _separator: EnumVariantSeparator) {}

    fn emit_matching_close(&mut self, close: Range<usize>) {
        self.committed.token(SyntaxKind::RBrace, close);
    }

    fn parse_variant_item(&mut self, malformed: Option<Range<usize>>) -> bool {
        self.committed.start_node(SyntaxKind::EnumVariant);
        if let Some(range) = malformed {
            let has_raw_name_retry = self
                .committed
                .probe(|probe| enum_variant_raw_name_pending(probe.input()));
            emit_variant_declaration_error(
                if has_raw_name_retry {
                    self.owner.variant_role(VariantDeclarationRole::Name)
                } else {
                    self.owner.item_role
                },
                range,
                self.committed,
                ExpectedSyntax::Identifier,
            );
            if !has_raw_name_retry {
                self.committed.finish_node();
                return true;
            }
        }
        let Some(name) = self.committed.probe(|probe| probe.input().run(scan_word)) else {
            emit_variant_declaration_missing(
                self.owner.variant_role(VariantDeclarationRole::Name),
                self.committed,
                ExpectedSyntax::Identifier,
            );
            self.committed.finish_node();
            return true;
        };
        self.committed.token(SyntaxKind::Identifier, name.range());
        self.item_continuation = matches!(
            commit_companion_variant_payload(self.owner, self.committed),
            CompanionVariantTypeExit::ItemContinuation
        );
        self.committed.finish_node();
        true
    }
}

impl<'source, E, O> CompanionVariantSequenceContext<'source>
    for DirectCompanionVariantPayloadContext<'_, '_, 'source, '_, E, O>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    fn take_item_continuation(&mut self) -> bool {
        std::mem::take(&mut self.item_continuation)
    }
}

pub(super) fn commit_variant_declaration_sequence_with_companion_handoff_isolated<
    'parse,
    'source,
    'local,
    E,
    O,
>(
    spec: VariantDeclarationSequenceSpec,
    owner: VariantDeclarationOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<VariantDeclarationCompanionOwnerTail>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    debug_assert_eq!(spec.declaration_base, owner.declaration_base);
    let mut context = DirectCompanionVariantPayloadContext {
        committed,
        owner,
        item_continuation: false,
    };
    let (_, handed_off) =
        drive_equals_inline_variant_sequence_with_companion_handoff(&mut context, spec);
    handed_off.then_some(VariantDeclarationCompanionOwnerTail { owner: owner.owner })
}

/// Retains Enum's fixture entry point while its declaration adapters call
/// the neutral core with their owner spec explicitly.
pub(super) fn commit_enum_variant_sequence_with_payload<'parse, 'source, 'local, E, O>(
    spec: EnumVariantSequenceSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> EnumVariantSequenceTermination
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_variant_declaration_sequence_with_payload(
        spec,
        enum_variant_declaration_owner_spec(spec.declaration_base),
        committed,
    )
}

pub(super) fn variant_declaration_sequence_spec(
    form: VariantDeclarationSequenceForm,
    layout: LayoutDelimitedFrame,
    declaration_base: usize,
) -> VariantDeclarationSequenceSpec {
    match form {
        VariantDeclarationSequenceForm::Braced => VariantDeclarationSequenceSpec {
            form,
            layout,
            declaration_base,
            explicit_separators: EnumVariantSeparatorSet::new(true, false),
            matching_close: Some(Delimiter::Brace),
            allow_leading_pipe: false,
            allow_trailing_pipe: false,
        },
        VariantDeclarationSequenceForm::ColonIndented
        | VariantDeclarationSequenceForm::EqualsIndented => VariantDeclarationSequenceSpec {
            form,
            layout,
            declaration_base,
            explicit_separators: EnumVariantSeparatorSet::new(true, true),
            matching_close: None,
            allow_leading_pipe: true,
            allow_trailing_pipe: true,
        },
        VariantDeclarationSequenceForm::EqualsInline => VariantDeclarationSequenceSpec {
            form,
            layout,
            declaration_base,
            explicit_separators: EnumVariantSeparatorSet::new(false, true),
            matching_close: None,
            allow_leading_pipe: true,
            allow_trailing_pipe: true,
        },
    }
}

pub(super) fn struct_word_pending<E>(i: &mut SynIn<E>) -> bool
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

pub(super) enum VariantFieldRecoverySlot {
    Item,
    Name,
    Colon,
    Type,
    Separator,
}

pub(super) fn variant_field_recovery_role(
    spec: VariantFieldDriverSpec,
    slot: VariantFieldRecoverySlot,
) -> GrammarRole {
    match (spec, slot) {
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Item) => {
            GrammarRole::Declaration(DeclarationRole::Struct(crate::session::StructRole::Field))
        }
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Name) => {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldName,
            ))
        }
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Colon) => {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldColon,
            ))
        }
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Type) => {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldType,
            ))
        }
        (VariantFieldDriverSpec::Struct, VariantFieldRecoverySlot::Separator) => {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::FieldSeparator,
            ))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Item) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedField,
            )))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Name) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldName,
            )))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Colon) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldColon,
            )))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Type) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldType,
            )))
        }
        (VariantFieldDriverSpec::EnumNamed, VariantFieldRecoverySlot::Separator) => {
            GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldSeparator,
            )))
        }
        (VariantFieldDriverSpec::EnumTuple, _) => GrammarRole::Declaration(DeclarationRole::Enum(
            EnumDeclarationRole::Variant(VariantDeclarationRole::TupleFieldType),
        )),
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Item) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedField,
            )))
        }
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Name) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldName,
            )))
        }
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Colon) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldColon,
            )))
        }
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Type) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldType,
            )))
        }
        (VariantFieldDriverSpec::ErrorNamed, VariantFieldRecoverySlot::Separator) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldSeparator,
            )))
        }
        (VariantFieldDriverSpec::ErrorTuple, _) => {
            GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::TupleFieldType,
            )))
        }
    }
}

pub(super) fn emit_variant_field_missing<'parse, 'source, 'local, E, O>(
    spec: VariantFieldDriverSpec,
    slot: VariantFieldRecoverySlot,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = variant_field_recovery_role(spec, slot);
        let at = i.pos();
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

pub(super) fn emit_variant_field_error<'parse, 'source, 'local, E, O>(
    spec: VariantFieldDriverSpec,
    slot: VariantFieldRecoverySlot,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = variant_field_recovery_role(spec, slot);
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([UnexpectedSyntax::Token {
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

/// The owner-parameterized direct field item core.  Struct reaches it through
/// its existing wrapper, so its node order and `StructRole` records remain
/// unchanged; Enum selects the corresponding Variant roles instead.
pub(super) fn commit_variant_named_field<'parse, 'source, 'local, E, O>(
    spec: VariantFieldDriverSpec,
    ambient_sensitive: bool,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name = commit_word(committed);
    let colon_without_name = if name.is_none() {
        committed.probe(|probe| scan_struct_colon(probe.input()))
    } else {
        None
    };
    let malformed_name = if name.is_none() && colon_without_name.is_none() {
        committed.probe(|probe| scan_struct_field_name_colon_recovery(probe.input()))
    } else {
        None
    };
    if name.is_none() && colon_without_name.is_none() && malformed_name.is_none() {
        return false;
    }
    committed.start_node(SyntaxKind::StructField);
    if let Some(name) = name {
        committed.token(SyntaxKind::Identifier, name.range());
        if let Some(trivia) =
            committed.probe(|probe| consume_struct_field_name_trivia(probe.input()))
        {
            committed.emit_trivia(&trivia);
        }
    } else {
        match malformed_name {
            Some(StructFieldInvalidRun {
                range,
                target: StructFieldInvalidTarget::Colon { trivia },
            }) => {
                emit_variant_field_error(
                    spec,
                    VariantFieldRecoverySlot::Name,
                    committed,
                    range,
                    ExpectedSyntax::Identifier,
                );
                if let Some(trivia) = trivia {
                    committed.emit_trivia(&trivia);
                }
            }
            _ => emit_variant_field_missing(
                spec,
                VariantFieldRecoverySlot::Name,
                committed,
                ExpectedSyntax::Identifier,
            ),
        }
    }
    let colon =
        colon_without_name.or_else(|| committed.probe(|probe| scan_struct_colon(probe.input())));
    if let Some(colon) = colon {
        committed.token(SyntaxKind::Colon, colon);
    } else {
        let recovery = if committed.probe(|probe| struct_field_boundary_pending(probe.input())) {
            None
        } else {
            committed.probe(|probe| scan_struct_field_invalid_run(true, probe.input()))
        };
        let type_expected = match recovery {
            Some(StructFieldInvalidRun { range, target }) => {
                emit_variant_field_error(
                    spec,
                    VariantFieldRecoverySlot::Colon,
                    committed,
                    range,
                    ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
                );
                match target {
                    StructFieldInvalidTarget::Colon { trivia } => {
                        if let Some(trivia) = trivia {
                            committed.emit_trivia(&trivia);
                        }
                        let colon = committed
                            .probe(|probe| scan_struct_colon(probe.input()))
                            .expect("field-colon recovery stopped at a colon");
                        committed.token(SyntaxKind::Colon, colon);
                        true
                    }
                    StructFieldInvalidTarget::TypePrimary { trivia } => {
                        if let Some(trivia) = trivia {
                            committed.emit_trivia(&trivia);
                        }
                        true
                    }
                    StructFieldInvalidTarget::Boundary => false,
                }
            }
            None => {
                emit_variant_field_missing(
                    spec,
                    VariantFieldRecoverySlot::Colon,
                    committed,
                    ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
                );
                !committed.probe(|probe| struct_field_boundary_pending(probe.input()))
            }
        };
        if !type_expected {
            committed.finish_node();
            return true;
        }
    }
    if ambient_sensitive && committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        emit_variant_field_missing(
            spec,
            VariantFieldRecoverySlot::Type,
            committed,
            ExpectedSyntax::TypeExpression,
        );
        committed.finish_node();
        return true;
    }
    if let Some(trivia) = committed.probe(|probe| consume_struct_field_type_trivia(probe.input())) {
        committed.emit_trivia(&trivia);
    }
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_type_delimited_owner(spec.named_type_owner());
    });
    let _ =
        commit_direct_type_expression_with_outer_missing_role(Some(spec.type_role()), committed);
    committed.probe(|probe| {
        assert_eq!(
            probe.input().local.pop_type_delimited_owner(),
            Some(spec.named_type_owner()),
        );
    });
    committed.finish_node();
    true
}

pub(super) fn push_struct_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_indentation_baseline(IndentationBaseline {
        column: layout.base_indent(),
        kind: IndentationBaselineKind::Introducer,
    });
}

pub(super) fn pop_struct_layout<E>(layout: LayoutDelimitedFrame, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline {
            column: layout.base_indent(),
            kind: IndentationBaselineKind::Introducer
        }),
    );
}

pub(super) fn consume_struct_field_name_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    if struct_trivia_has_newline(&trivia) {
        i.rollback(checkpoint);
        None
    } else {
        Some(trivia)
    }
}

pub(super) fn consume_struct_field_type_trivia<E>(i: &mut SynIn<E>) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    if struct_trivia_has_newline(&trivia) && i.local.line().line_indent <= base {
        i.rollback(checkpoint);
        None
    } else {
        Some(trivia)
    }
}

#[derive(Clone, Debug)]
pub(super) struct StructFieldInvalidRun {
    pub(super) range: Range<usize>,
    pub(super) target: StructFieldInvalidTarget,
}

#[derive(Clone, Debug)]
pub(super) enum StructFieldInvalidTarget {
    Colon { trivia: Option<TriviaRun> },
    TypePrimary { trivia: Option<TriviaRun> },
    Boundary,
}

/// Scan one declaration-owned malformed field slot.  It is intentionally
/// narrower than header recovery: a field name can recover only to a colon
/// skeleton, while a field colon may also hand the same slot to a TypePrimary.
pub(super) fn scan_struct_field_invalid_run<E>(
    allow_type_primary: bool,
    i: &mut SynIn<E>,
) -> Option<StructFieldInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    let mut end = start;
    loop {
        if end == start
            && (struct_colon_pending(i) || (allow_type_primary && struct_type_primary_pending(i)))
        {
            return None;
        }
        if end > start {
            if struct_colon_pending(i) {
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::Colon { trivia: None },
                });
            }
            if allow_type_primary && struct_type_primary_pending(i) {
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::TypePrimary { trivia: None },
                });
            }
            if !allow_type_primary && struct_raw_field_head_pending(i) {
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::Boundary,
                });
            }

            let checkpoint = i.checkpoint();
            let trivia = i.run(scan_trivia).expect("trivia is total");
            if !trivia.is_empty() {
                if struct_trivia_has_newline(&trivia) {
                    i.rollback(checkpoint);
                    return Some(StructFieldInvalidRun {
                        range: start..end,
                        target: StructFieldInvalidTarget::Boundary,
                    });
                }
                if struct_colon_pending(i) {
                    return Some(StructFieldInvalidRun {
                        range: start..end,
                        target: StructFieldInvalidTarget::Colon {
                            trivia: Some(trivia),
                        },
                    });
                }
                if allow_type_primary && struct_type_primary_pending(i) {
                    return Some(StructFieldInvalidRun {
                        range: start..end,
                        target: StructFieldInvalidTarget::TypePrimary {
                            trivia: Some(trivia),
                        },
                    });
                }
                i.rollback(checkpoint);
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::Boundary,
                });
            }
            if struct_field_boundary_pending(i) || struct_mismatched_close_pending(i) {
                return Some(StructFieldInvalidRun {
                    range: start..end,
                    target: StructFieldInvalidTarget::Boundary,
                });
            }
        }

        if let Some(colon_colon) = scan_struct_colon_colon(i) {
            end = colon_colon.end;
            continue;
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < end).then_some(StructFieldInvalidRun {
                range: start..end,
                target: StructFieldInvalidTarget::Boundary,
            });
        }
        i.input.next()?;
        end = i.pos();
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

/// A malformed field name establishes field authority only if it reaches the
/// literal-colon skeleton.  Other malformed input remains sequence-owned.
pub(super) fn scan_struct_field_name_colon_recovery<E>(
    i: &mut SynIn<E>,
) -> Option<StructFieldInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let recovered = scan_struct_field_invalid_run(false, i);
    if matches!(
        recovered,
        Some(StructFieldInvalidRun {
            target: StructFieldInvalidTarget::Colon { .. },
            ..
        })
    ) {
        recovered
    } else {
        i.rollback(checkpoint);
        None
    }
}

pub(super) fn struct_type_primary_pending<E>(i: &mut SynIn<E>) -> bool
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

pub(super) fn struct_raw_field_head_pending<E>(i: &mut SynIn<E>) -> bool
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

pub(super) fn struct_field_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    i.input.remainder().is_empty()
        || scan_struct_comma_pending(i)
        || struct_close_brace_pending(i)
        || struct_semicolon_pending(i)
        || struct_mismatched_close_pending(i)
        || struct_field_newline_boundary_pending(i)
}

pub(super) fn struct_field_newline_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let pending = struct_trivia_has_newline(&trivia);
    i.rollback(checkpoint);
    pending
}

pub(super) fn scan_struct_comma_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_comma(i).is_some();
    i.rollback(checkpoint);
    pending
}

pub(super) fn struct_colon_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_colon(i).is_some();
    i.rollback(checkpoint);
    pending
}

pub(super) fn struct_close_brace_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_close_brace(i).is_some();
    i.rollback(checkpoint);
    pending
}

pub(super) fn struct_mismatched_close_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(punctuation.kind(), PunctuationKind::Close(delimiter) if delimiter != Delimiter::Brace)
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn scan_struct_mismatched_close_for<E>(
    expected: Delimiter,
    i: &mut SynIn<E>,
) -> Option<(Range<usize>, Delimiter)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    match punctuation.kind() {
        PunctuationKind::Close(delimiter) if delimiter != expected => {
            Some((punctuation.range(), delimiter))
        }
        _ => {
            i.rollback(checkpoint);
            None
        }
    }
}

/// Each Struct field frame keeps incoming stops beneath its own matching
/// delimiter. A mismatched closer is outer-owned exactly when its corresponding
/// incoming stop remains active; it must remain untouched for that owner.
pub(super) fn struct_outer_owned_mismatched_close_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_outer_owned_mismatched_close_pending_for(Delimiter::Brace, i)
}

pub(super) fn struct_outer_owned_mismatched_close_pending_for<E>(
    expected: Delimiter,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_mismatched_close_for(expected, i).is_some_and(|(_, delimiter)| {
        let stop = match delimiter {
            Delimiter::Parenthesis => StopKind::RightParenthesis,
            Delimiter::Bracket => StopKind::RightBracket,
            Delimiter::Brace => StopKind::RightBrace,
        };
        i.local.stop_set().is_some_and(|stops| stops.contains(stop))
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn scan_struct_comma<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::Comma, i)
}

pub(super) fn scan_struct_colon<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::Colon, i)
}

pub(super) fn scan_struct_close_brace<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_close(Delimiter::Brace, i)
}

pub(super) fn scan_struct_close_parenthesis<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_close(Delimiter::Parenthesis, i)
}

pub(super) fn scan_struct_close<E>(delimiter: Delimiter, i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::Close(delimiter), i)
}

pub(super) fn scan_struct_semicolon<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::Semicolon, i)
}

pub(super) fn struct_semicolon_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = scan_struct_semicolon(i).is_some();
    i.rollback(checkpoint);
    pending
}

pub(super) fn scan_struct_colon_colon<E>(i: &mut SynIn<E>) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_punctuation(PunctuationKind::ColonColon, i)
}

pub(super) fn scan_struct_punctuation<E>(
    kind: PunctuationKind,
    i: &mut SynIn<E>,
) -> Option<Range<usize>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    if punctuation.kind() == kind {
        Some(punctuation.range())
    } else {
        i.rollback(checkpoint);
        None
    }
}
