use super::*;

/// The sink-free prefix reserved for standalone Error declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 9 connects it to shared statement dispatch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ErrorStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) error_keyword: WordSpan<'source>,
    pub(super) error_base: usize,
}

/// Recognizes the sink-free prefix reserved for a standalone Error declaration.
///
/// `my error` preserves Yulang2's local-binding collision. It establishes
/// Error authority only when a raw TypeExpression name is visible after the
/// keyword; the lookahead rolls back so the later header driver owns the same
/// bytes.
pub(super) fn recognize_error_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ErrorStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let error_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(error_base, &mut i).filter(|trivia| !trivia.is_empty())
        else {
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
    if keyword.text() != "error" {
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
            mod_trivia(error_base, &mut i).is_some() && error_raw_type_head_candidate(&mut i);
        i.rollback(head_checkpoint);
        if !head_candidate {
            i.rollback(checkpoint);
            return None;
        }
    }
    Some(ErrorStatementIntro {
        start,
        visibility,
        after_visibility,
        error_keyword: keyword,
        error_base,
    })
}

/// Peeks the raw TypeExpression-name forms admitted by ERROR-J.
///
/// The shared path-segment scanner accepts ordinary words plus sigil-prefixed
/// forms. Error accepts only the ordinary and apostrophe forms as raw type
/// heads; `$` and `&` remain outside the current TypeExpression grammar.
pub(super) fn error_raw_type_head_candidate<E>(i: &mut SynIn<E>) -> bool
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedErrorHeader<'source> {
    pub(super) name: Recovered<WordSpan<'source>>,
    pub(super) parameters: Vec<DeclarationTypeParameter<'source>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum ErrorHeaderRecovery {
    Missing { at: usize },
    Error { range: Range<usize> },
}

/// Parses Error's mandatory raw name and optional same-line generic list.
///
/// The accepted-intro boundary check happens before its gap is consumed. A
/// failed name stops this adapter immediately: derives and body ownership
/// remain for their later gates, without a cascade from the same cause.
#[allow(dead_code)]
pub(super) fn parse_required_error_header_isolated<'source, E>(
    intro: &ErrorStatementIntro<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (ParsedErrorHeader<'source>, Vec<ErrorHeaderRecovery>)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut recoveries = Vec::new();
    let name_boundary = any_ambient_owner_claims(i);
    if !name_boundary {
        let _ = mod_trivia(intro.error_base, i);
    }
    let name = if name_boundary {
        recoveries.push(ErrorHeaderRecovery::Missing { at: i.pos() });
        Recovered::Incomplete
    } else if let Some(name) = i.run(scan_word) {
        Recovered::Complete(name)
    } else if let Some(recovery) = scan_error_name_invalid_run(i) {
        recoveries.push(ErrorHeaderRecovery::Error {
            range: recovery.range.clone(),
        });
        match recovery.target {
            ErrorNameInvalidTarget::RawName => Recovered::Complete(
                i.run(scan_word)
                    .expect("an Error name retry leaves its raw word at the cursor"),
            ),
            ErrorNameInvalidTarget::BodyStarterOrBoundary => Recovered::Incomplete,
        }
    } else {
        recoveries.push(ErrorHeaderRecovery::Missing { at: i.pos() });
        Recovered::Incomplete
    };
    let parameters = matches!(name, Recovered::Complete(_))
        .then(|| scan_declaration_type_parameter_list(i).unwrap_or_default())
        .unwrap_or_default();
    (ParsedErrorHeader { name, parameters }, recoveries)
}

/// Direct-CST's Error header adapter scans the same decision stream, then
/// realizes only its raw surface and typed Name recovery records.
#[allow(dead_code)]
pub(super) fn commit_required_error_header_isolated<'parse, 'source, 'local, E, O>(
    intro: &ErrorStatementIntro<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> ParsedErrorHeader<'source>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let (header, recoveries, header_end) = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let (header, recoveries) = parse_required_error_header_isolated(intro, i);
        let end = i.pos();
        i.rollback(checkpoint);
        (header, recoveries, end)
    });
    commit_error_header_surface(
        intro.error_base,
        &header,
        &recoveries,
        header_end,
        committed,
    );
    header
}

pub(super) fn commit_error_header_surface<'parse, 'source, 'local, E, O>(
    error_base: usize,
    header: &ParsedErrorHeader<'source>,
    recoveries: &[ErrorHeaderRecovery],
    header_end: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let name_target = recoveries
        .first()
        .map(error_header_recovery_start)
        .or_else(|| match &header.name {
            Recovered::Complete(name) => Some(name.range().start),
            Recovered::Incomplete => None,
        })
        .unwrap_or(header_end);
    let current = committed.probe(|probe| probe.input().pos());
    if current < name_target {
        let trivia = committed
            .probe(|probe| mod_trivia(error_base, probe.input()))
            .expect("the accepted Error header gap remains declaration-continuing trivia");
        debug_assert_eq!(trivia.range(), current..name_target);
        committed.emit_trivia(&trivia);
    }
    if let Some(recovery) = recoveries.first() {
        commit_error_header_recovery(recovery.clone(), committed);
    }
    if let Recovered::Complete(expected) = &header.name {
        let actual = commit_word(committed).expect("an accepted Error name remains at the cursor");
        debug_assert_eq!(actual.range(), expected.range());
        committed.token(SyntaxKind::Identifier, actual.range());
    }
    if !header.parameters.is_empty() {
        committed.start_node(SyntaxKind::DeclarationTypeParameterList);
        for parameter in &header.parameters {
            let trivia = committed
                .probe(|probe| scan_required_inline_trivia(probe.input()))
                .expect("an accepted Error parameter retains its same-line separator");
            committed.emit_trivia(&trivia);
            let actual = committed
                .probe(|probe| probe.input().run(scan_path_segment))
                .expect("an accepted Error parameter remains at the cursor");
            debug_assert_eq!(actual.range(), declaration_type_parameter_range(parameter));
            committed.token(declaration_type_parameter_kind(parameter), actual.range());
        }
        committed.finish_node();
    }
    debug_assert_eq!(committed.probe(|probe| probe.input().pos()), header_end);
}

pub(super) fn commit_error_header_recovery<'parse, 'source, 'local, E, O>(
    recovery: ErrorHeaderRecovery,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    if let ErrorHeaderRecovery::Error { range } = &recovery {
        committed.probe(|probe| {
            let i = probe.input();
            debug_assert_eq!(i.pos(), range.start);
            while i.pos() < range.end {
                i.input
                    .next()
                    .expect("a selected Error header error range remains available");
                let mut line = i.local.line();
                line.at_line_start = false;
                i.local.set_line(line);
            }
            debug_assert_eq!(i.pos(), range.end);
        });
    }
    emit_error_header_recovery(committed, recovery);
}

pub(super) fn error_header_recovery_start(recovery: &ErrorHeaderRecovery) -> usize {
    match recovery {
        ErrorHeaderRecovery::Missing { at } => *at,
        ErrorHeaderRecovery::Error { range } => range.start,
    }
}

pub(super) fn emit_error_header_recovery<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    recovery: ErrorHeaderRecovery,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let (kind, range, unexpected) = match recovery {
        ErrorHeaderRecovery::Missing { at } => (RecoveryKind::Missing, at..at, Arc::from([])),
        ErrorHeaderRecovery::Error { range } => {
            let unexpected = Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::OtherCharacter,
            }]);
            (RecoveryKind::Error, range, unexpected)
        }
    };
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Name));
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ErrorNameInvalidTarget {
    RawName,
    BodyStarterOrBoundary,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ErrorNameInvalidRun {
    pub(super) range: Range<usize>,
    pub(super) target: ErrorNameInvalidTarget,
}

pub(super) fn scan_error_name_invalid_run<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ErrorNameInvalidRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if error_raw_name_pending(i) {
            return (start < i.pos()).then_some(ErrorNameInvalidRun {
                range: start..i.pos(),
                target: ErrorNameInvalidTarget::RawName,
            });
        }
        if error_header_body_starter_or_boundary_pending(i) {
            return (start < i.pos()).then_some(ErrorNameInvalidRun {
                range: start..i.pos(),
                target: ErrorNameInvalidTarget::BodyStarterOrBoundary,
            });
        }
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n') {
            return (start < i.pos()).then_some(ErrorNameInvalidRun {
                range: start..i.pos(),
                target: ErrorNameInvalidTarget::BodyStarterOrBoundary,
            });
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
    }
}

pub(super) fn error_raw_name_pending<E>(i: &mut SynIn<E>) -> bool
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

pub(super) fn error_header_body_starter_or_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty()
        || any_ambient_owner_claims(i)
        || declaration_exact_equals_pending(i)
    {
        return true;
    }
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Semicolon
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon,
        )
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn error_variant_declaration_owner_spec(
    declaration_base: usize,
) -> VariantDeclarationOwnerSpec {
    VariantDeclarationOwnerSpec {
        owner: VariantDeclarationOwner::Error,
        declaration_base,
        item_role: GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Variant(
            VariantDeclarationRole::Item,
        ))),
        from_type_role: GrammarRole::Declaration(DeclarationRole::Error(
            ErrorDeclarationRole::Variant(VariantDeclarationRole::FromType),
        )),
        positional_payload_role: GrammarRole::Declaration(DeclarationRole::Error(
            ErrorDeclarationRole::Variant(VariantDeclarationRole::PositionalPayload),
        )),
        field_driver: VariantFieldDriverSpec::ErrorNamed,
    }
}

/// Parses one accepted Error continuation shared by isolated fixtures and
/// Gate 9's promoted public statement dispatch. Its declaration identity
/// remains Error-specific; only the established Enum body vocabulary is shared.
pub(crate) fn parse_error_declaration_isolated<'source, E>(
    i: SynIn<'_, 'source, '_, E>,
) -> Option<ErrorDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_error_declaration_with_operators(&crate::operator::OperatorTable::empty(), i)
}

pub(crate) fn parse_error_declaration_with_operators<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ErrorDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let declaration = (|| {
        let intro = i.run(recognize_error_statement_intro)?;
        let (header, _recoveries) = parse_required_error_header_isolated(&intro, &mut i);
        let header_complete = matches!(header.name, Recovered::Complete(_));
        let (mut derives, header_companion_tail) = if header_complete {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Error,
                DerivesAttachmentPosition::Header,
                intro.error_base,
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
        let mut companion = None;
        let header_companion_pending = header_complete
            && (header_companion_tail.is_some()
                || recognize_declaration_companion_handoff(intro.error_base, &mut i).is_some());
        let body = if header_companion_pending {
            if let Some(tail) = header_companion_tail {
                debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Error);
                debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
            }
            companion = Some(parse_error_declaration_companion_after_handoff(
                table,
                intro.error_base,
                &mut i,
            ));
            Recovered::Complete(EnumBody::Bodyless { semicolon: None })
        } else if header_complete {
            parse_error_body_ast(intro.error_base, &mut i)
        } else {
            Recovered::Incomplete
        };
        if enum_body_has_actual_trailing_close(&body) {
            let trailing = recognize_derives_attachment_start(
                DerivesAttachmentOwner::Error,
                DerivesAttachmentPosition::Trailing,
                intro.error_base,
                &mut i,
            )
            .map(|start| parse_derives_attachments_with_companion_handoff_isolated(start, &mut i));
            let trailing_companion_tail = trailing.as_ref().and_then(|parsed| parsed.tail);
            if let Some(parsed) = trailing {
                derives.extend(parsed.attachments);
            }
            let trailing_companion_pending = trailing_companion_tail.is_some()
                || recognize_declaration_companion_handoff(intro.error_base, &mut i).is_some();
            if trailing_companion_pending {
                if let Some(tail) = trailing_companion_tail {
                    debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Error);
                    debug_assert_eq!(tail.position, DerivesAttachmentPosition::Trailing);
                }
                companion = Some(parse_error_declaration_companion_after_handoff(
                    table,
                    intro.error_base,
                    &mut i,
                ));
            }
        }
        let header_end = match &header.name {
            Recovered::Complete(name) => header
                .parameters
                .last()
                .map_or_else(|| name.range().end, declaration_type_parameter_end),
            Recovered::Incomplete => intro.error_keyword.range().end,
        };
        let body_end = enum_body_range_end(&body).unwrap_or(header_end);
        let derives_end = derives
            .last()
            .map_or(0, |attachment| attachment.clause.range.end);
        let companion_end = companion
            .as_ref()
            .map_or(0, |companion| companion.range.end);
        Some(ErrorDeclaration {
            visibility: intro
                .visibility
                .map_or(Visibility::Private, |prefix| prefix.visibility),
            name: header.name,
            parameters: header.parameters,
            derives,
            companion,
            body,
            range: intro.start..header_end.max(body_end).max(derives_end).max(companion_end),
        })
    })();
    i.errors_rollback(errors_checkpoint);
    declaration
}

pub(super) fn parse_error_body_ast<'source, E>(
    error_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<EnumBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if enum_body_implicit_boundary_pending(error_base, i) {
        return Recovered::Complete(EnumBody::Bodyless { semicolon: None });
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(error_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Complete(EnumBody::Bodyless { semicolon: None });
    };
    if let Some(equals) = i.run(scan_declaration_exact_equals) {
        return Recovered::Complete(EnumBody::Equals {
            equals: equals.clone(),
            body: parse_error_equals_body_ast(error_base, equals, i),
        });
    }
    let punctuation_checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation);
    match punctuation.map(|punctuation| (punctuation.kind(), punctuation.range())) {
        Some((PunctuationKind::Semicolon, semicolon)) => Recovered::Complete(EnumBody::Bodyless {
            semicolon: Some(semicolon),
        }),
        Some((PunctuationKind::Open(Delimiter::Brace), open)) => Recovered::Complete(
            EnumBody::Braced(parse_error_braced_body_ast(error_base, open, i)),
        ),
        Some((PunctuationKind::Colon, colon)) => Recovered::Complete(EnumBody::Colon {
            colon: colon.clone(),
            body: parse_error_colon_body_ast(error_base, colon, i),
        }),
        _ => {
            i.rollback(punctuation_checkpoint);
            i.rollback(checkpoint);
            match enum_body_introducer_error_retry_ast(error_base, i) {
                Some(true) => parse_error_body_ast(error_base, i),
                Some(false) | None => Recovered::Incomplete,
            }
        }
    }
}

pub(super) fn parse_error_braced_body_ast<'source, E>(
    error_base: usize,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> EnumBracedBody<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let opening = i.run(scan_trivia).expect("trivia scanning is total");
    let layout = LayoutDelimitedFrame::after_opening_trivia(
        error_base,
        &opening,
        i.local.line().line_indent,
    );
    let sequence = parse_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::Braced,
            layout,
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        i,
    );
    let end = match &sequence.close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    EnumBracedBody {
        open: open.clone(),
        variants: sequence.variants,
        trailing_comma: sequence.trailing_comma,
        close: sequence.close,
        range: open.start..end,
    }
}

pub(super) fn parse_error_colon_body_ast<'source, E>(
    error_base: usize,
    colon: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<EnumIndentedVariantBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if !enum_variant_trivia_has_newline(&trivia) || i.local.line().line_indent <= error_base {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    }
    let block_indent = i.local.line().line_indent;
    let sequence = parse_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::ColonIndented,
            LayoutDelimitedFrame::inline(block_indent),
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        i,
    );
    let end = i.pos();
    let _ = sequence.trailing_pipe;
    Recovered::Complete(EnumIndentedVariantBody {
        base_indent: error_base,
        block_indent,
        variants: sequence.variants,
        range: colon.end..end,
    })
}

pub(super) fn parse_error_equals_body_ast<'source, E>(
    error_base: usize,
    equals: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<EnumEqualsVariantBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia scanning is total");
    if enum_variant_trivia_has_newline(&trivia) {
        if i.local.line().line_indent <= error_base {
            i.rollback(checkpoint);
            return Recovered::Incomplete;
        }
        let block_indent = i.local.line().line_indent;
        let sequence = parse_variant_declaration_sequence_with_payload(
            variant_declaration_sequence_spec(
                VariantDeclarationSequenceForm::EqualsIndented,
                LayoutDelimitedFrame::inline(block_indent),
                error_base,
            ),
            error_variant_declaration_owner_spec(error_base),
            i,
        );
        let end = i.pos();
        let _ = sequence.trailing_pipe;
        return Recovered::Complete(EnumEqualsVariantBody::Indented(EnumIndentedVariantBody {
            base_indent: error_base,
            block_indent,
            variants: sequence.variants,
            range: equals.end..end,
        }));
    }
    i.rollback(checkpoint);
    let parsed = parse_variant_declaration_sequence_with_companion_handoff_isolated(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::EqualsInline,
            LayoutDelimitedFrame::inline(error_base),
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        i,
    );
    if let Some(tail) = parsed.tail {
        debug_assert_eq!(tail.owner, VariantDeclarationOwner::Error);
    }
    let end = i.pos();
    Recovered::Complete(EnumEqualsVariantBody::Inline {
        variants: parsed.sequence.variants,
        trailing_pipe: parsed.sequence.trailing_pipe,
        range: equals.end..end,
    })
}

fn parse_error_declaration_companion_after_handoff<'source, E>(
    table: &crate::operator::OperatorTable,
    error_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DeclarationCompanion<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    mod_trivia(error_base, i).expect("an accepted Error companion handoff preserves its owner gap");
    parse_declaration_companion_isolated(table, error_base, i)
        .expect("an accepted Error companion handoff preserves exact `with`")
}

/// Direct-CST counterpart of [`parse_error_declaration_isolated`]. Gate 9
/// promotes this exact adapter into shared statement dispatch.
pub(crate) fn commit_error_declaration_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ErrorStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_error_declaration_with_operators(
        &crate::operator::OperatorTable::empty(),
        committed,
        intro,
    )
}

pub(crate) fn commit_error_declaration_with_operators<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ErrorStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::ErrorDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::ErrorKw, intro.error_keyword.range());
    let header = commit_required_error_header_isolated(&intro, committed);
    let header_complete = matches!(header.name, Recovered::Complete(_));
    let header_derives = if header_complete {
        committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Error,
                DerivesAttachmentPosition::Header,
                intro.error_base,
                probe.input(),
            )
        })
    } else {
        None
    }
    .map(|start| commit_derives_attachments_with_companion_handoff_isolated(start, committed));
    let header_companion_tail = header_derives.as_ref().and_then(|parsed| parsed.tail);
    let header_companion_pending = header_complete
        && (header_companion_tail.is_some()
            || committed.probe(|probe| {
                recognize_declaration_companion_handoff(intro.error_base, probe.input()).is_some()
            }));
    let has_actual_braced_close = if header_companion_pending {
        if let Some(tail) = header_companion_tail {
            debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Error);
            debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
        }
        let _ =
            commit_error_declaration_companion_after_handoff(table, intro.error_base, committed);
        false
    } else {
        header_complete && commit_error_body_isolated(intro.error_base, committed)
    };
    if has_actual_braced_close {
        let trailing = committed.probe(|probe| {
            recognize_derives_attachment_start(
                DerivesAttachmentOwner::Error,
                DerivesAttachmentPosition::Trailing,
                intro.error_base,
                probe.input(),
            )
        });
        let trailing = trailing.map(|start| {
            commit_derives_attachments_with_companion_handoff_isolated(start, committed)
        });
        let trailing_companion_tail = trailing.as_ref().and_then(|parsed| parsed.tail);
        let trailing_companion_pending = trailing_companion_tail.is_some()
            || committed.probe(|probe| {
                recognize_declaration_companion_handoff(intro.error_base, probe.input()).is_some()
            });
        if trailing_companion_pending {
            if let Some(tail) = trailing_companion_tail {
                debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Error);
                debug_assert_eq!(tail.position, DerivesAttachmentPosition::Trailing);
            }
            let _ = commit_error_declaration_companion_after_handoff(
                table,
                intro.error_base,
                committed,
            );
        }
    }
    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    Recovered::Complete(intro.start..end)
}

pub(super) fn commit_error_body_isolated<'parse, 'source, 'local, E, O>(
    error_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| enum_body_implicit_boundary_pending(error_base, probe.input())) {
        return false;
    }
    let starter = committed.probe(|probe| enum_direct_body_starter(error_base, probe.input()));
    let Some((trivia, starter)) = starter else {
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(error_base, i);
            i.rollback(checkpoint);
            trivia
        });
        if let Some(trivia) = trivia {
            let newline = committed
                .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
            if newline {
                return false;
            }
            let consumed = committed
                .probe(|probe| mod_trivia(error_base, probe.input()))
                .expect("the Error body-introducer recovery retains its leading trivia");
            assert_eq!(consumed.range(), trivia.range());
            committed.emit_trivia(&consumed);
        }
        match error_body_introducer_error_retry(error_base, committed) {
            Some(true) => return commit_error_body_isolated(error_base, committed),
            Some(false) | None => return false,
        }
    };
    let consumed_trivia = committed
        .probe(|probe| mod_trivia(error_base, probe.input()))
        .expect("the selected Error body starter retains its declaration-continuing trivia");
    assert_eq!(consumed_trivia.range(), trivia.range());
    committed.emit_trivia(&consumed_trivia);
    match starter {
        DirectEnumBodyStarter::Bodyless(range) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("the selected Error semicolon remains at the cursor");
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
            false
        }
        DirectEnumBodyStarter::Braced(range) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("the selected Error brace remains at the cursor");
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::LBrace, range);
            commit_error_braced_body_isolated(error_base, committed)
        }
        DirectEnumBodyStarter::Colon(range) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("the selected Error colon remains at the cursor");
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range);
            commit_error_colon_body_isolated(error_base, committed);
            false
        }
        DirectEnumBodyStarter::Equals(range) => {
            let equals = committed
                .probe(|probe| probe.input().run(scan_declaration_exact_equals))
                .expect("the selected Error equals remains at the cursor");
            assert_eq!(equals, range);
            committed.token(SyntaxKind::Equals, range);
            commit_error_equals_body_isolated(error_base, committed);
            false
        }
    }
}

pub(super) fn commit_error_braced_body_isolated<'parse, 'source, 'local, E, O>(
    error_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let layout = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let opening = i.run(scan_trivia).expect("trivia scanning is total");
        let layout = LayoutDelimitedFrame::after_opening_trivia(
            error_base,
            &opening,
            i.local.line().line_indent,
        );
        i.rollback(checkpoint);
        layout
    });
    match commit_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::Braced,
            layout,
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        committed,
    ) {
        EnumVariantSequenceTermination::MatchingClose(_) => true,
        EnumVariantSequenceTermination::MismatchedClose => {
            let range = committed.probe(|probe| {
                let i = probe.input();
                let checkpoint = i.checkpoint();
                let range = i
                    .run(scan_punctuation)
                    .map(|punctuation| punctuation.range());
                i.rollback(checkpoint);
                range.expect("a mismatched Error brace close remains at the cursor")
            });
            committed.probe(|probe| consume_source_range(range.clone(), probe.input()));
            emit_enum_braced_close_error(range, committed);
            emit_enum_braced_close_missing(committed);
            false
        }
        EnumVariantSequenceTermination::Dedent
        | EnumVariantSequenceTermination::OwnerBoundary
        | EnumVariantSequenceTermination::EndOfInput
        | EnumVariantSequenceTermination::ItemContinuation => {
            emit_enum_braced_close_missing(committed);
            false
        }
    }
}

pub(super) fn commit_error_colon_body_isolated<'parse, 'source, 'local, E, O>(
    error_base: usize,
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
        .expect("trivia scanning is total");
    let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
    if !enum_variant_trivia_has_newline(&trivia) || block_indent <= error_base {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_error_variant_item_missing(committed);
        return;
    }
    committed.emit_trivia(&trivia);
    let _ = commit_variant_declaration_sequence_with_payload(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::ColonIndented,
            LayoutDelimitedFrame::inline(block_indent),
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        committed,
    );
}

fn commit_error_declaration_companion_after_handoff<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    error_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Range<usize>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = committed
        .probe(|probe| mod_trivia(error_base, probe.input()))
        .expect("an accepted Error companion handoff preserves its owner gap");
    committed.emit_trivia(&leading);
    commit_declaration_companion_isolated(table, error_base, committed)
        .expect("an accepted Error companion handoff preserves exact `with`")
}

pub(super) fn commit_error_equals_body_isolated<'parse, 'source, 'local, E, O>(
    error_base: usize,
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
        .expect("trivia scanning is total");
    if enum_variant_trivia_has_newline(&trivia) {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        if block_indent <= error_base {
            committed.probe(|probe| probe.input().rollback(checkpoint));
            emit_error_variant_item_missing(committed);
            return;
        }
        committed.emit_trivia(&trivia);
        let _ = commit_variant_declaration_sequence_with_payload(
            variant_declaration_sequence_spec(
                VariantDeclarationSequenceForm::EqualsIndented,
                LayoutDelimitedFrame::inline(block_indent),
                error_base,
            ),
            error_variant_declaration_owner_spec(error_base),
            committed,
        );
        return;
    }
    committed.probe(|probe| probe.input().rollback(checkpoint));
    let tail = commit_variant_declaration_sequence_with_companion_handoff_isolated(
        variant_declaration_sequence_spec(
            VariantDeclarationSequenceForm::EqualsInline,
            LayoutDelimitedFrame::inline(error_base),
            error_base,
        ),
        error_variant_declaration_owner_spec(error_base),
        committed,
    );
    if let Some(tail) = tail {
        debug_assert_eq!(tail.owner, VariantDeclarationOwner::Error);
    }
}

pub(super) fn error_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    error_base: usize,
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
            if enum_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if enum_body_implicit_boundary_pending(error_base, i) {
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
    emit_error_declaration_error(
        ErrorDeclarationRole::BodyIntroducer,
        recovered.0,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Semicolon),
        committed,
    );
    Some(recovered.1)
}

/// A standalone Error declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition, variant
/// parsing, and body parsing remain unreachable until their later dedicated
/// gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ErrorDeclaration<'source> {
    pub(super) visibility: Visibility,
    pub(super) name: Recovered<WordSpan<'source>>,
    pub(super) parameters: Vec<DeclarationTypeParameter<'source>>,
    pub(super) derives: Vec<DerivesAttachment<'source>>,
    pub(super) companion: Option<DeclarationCompanion<'source>>,
    pub(super) body: Recovered<EnumBody<'source>>,
    pub(super) range: Range<usize>,
}

impl ErrorDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}
