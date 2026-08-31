use super::*;

/// The sink-free prefix shared by root and canonical-statement Struct parsing.
///
/// `struct_base` is captured when the first accepted starter is still current;
/// later body parsing must not reconstruct it from the name or body opener.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) struct_keyword: WordSpan<'source>,
    pub(super) struct_base: usize,
}

pub(super) fn recognize_struct_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<StructStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let struct_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(struct_base, &mut i) else {
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
    if keyword.text() != "struct" {
        i.rollback(checkpoint);
        return None;
    }
    Some(StructStatementIntro {
        start,
        visibility,
        after_visibility,
        struct_keyword: keyword,
        struct_base,
    })
}

pub(crate) fn commit_struct_declaration<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: StructStatementIntro<'source>,
) -> Recovered<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_struct_declaration_with_operators(
        &crate::operator::OperatorTable::empty(),
        committed,
        intro,
    )
}

pub(crate) fn commit_struct_declaration_with_operators<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: StructStatementIntro<'source>,
) -> Recovered<()>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_struct_declaration_with_derives_and_companion_isolated(table, committed, intro).0
}

/// Direct-CST counterpart of
/// [`parse_struct_declaration_with_derives_isolated`]. The public entry and
/// the focused harness both use this one attachment-owning core.
pub(super) fn commit_struct_declaration_with_derives_isolated<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: StructStatementIntro<'source>,
) -> (Recovered<()>, Vec<DirectDerivesAttachment>)
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_struct_declaration_with_derives_and_companion_isolated(
        &crate::operator::OperatorTable::empty(),
        committed,
        intro,
    )
}

fn commit_struct_declaration_with_derives_and_companion_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: StructStatementIntro<'source>,
) -> (Recovered<()>, Vec<DirectDerivesAttachment>)
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    committed.start_node(SyntaxKind::StructDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::StructKw, intro.struct_keyword.range());
    if let Some(trivia) =
        committed.probe(|probe| struct_continuation_trivia(intro.struct_base, probe.input()))
    {
        committed.emit_trivia(&trivia);
    }

    let mut name_incomplete = false;
    if let Some(name) = commit_word(committed) {
        committed.token(SyntaxKind::Identifier, name.range());
    } else {
        let recovery = struct_name_error_retry(committed);
        match recovery {
            Some(true) => {
                let name = commit_word(committed)
                    .expect("a Struct name retry must leave its raw word at the cursor");
                committed.token(SyntaxKind::Identifier, name.range());
            }
            Some(false) => {
                name_incomplete = true;
            }
            None => {
                name_incomplete = true;
                emit_struct_missing(
                    committed,
                    crate::session::StructRole::Name,
                    ExpectedSyntax::Identifier,
                );
            }
        }
    }

    let (mut derives, header_companion_tail) = if !name_incomplete {
        committed
            .probe(|probe| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Struct,
                    DerivesAttachmentPosition::Header,
                    intro.struct_base,
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

    let mut body_starter = None;
    let header_companion_pending = !name_incomplete
        && (header_companion_tail.is_some()
            || committed.probe(|probe| {
                recognize_declaration_companion_handoff(intro.struct_base, probe.input()).is_some()
            }));
    if header_companion_pending {
        if let Some(tail) = header_companion_tail {
            debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Struct);
            debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
        }
        let _ =
            commit_struct_declaration_companion_after_handoff(table, intro.struct_base, committed);
    } else {
        let body_starter_pending =
            committed.probe(|probe| struct_body_starter_pending(probe.input()));
        if !name_incomplete || body_starter_pending {
            if let Some(trivia) = committed
                .probe(|probe| struct_continuation_trivia(intro.struct_base, probe.input()))
            {
                committed.emit_trivia(&trivia);
            }
            body_starter = committed.probe(|probe| struct_body_starter(probe.input()));
            commit_struct_body_introducer(intro.struct_base, committed);
        }
    }
    if committed_struct_body_has_actual_trailing_close(committed, body_starter) {
        let trailing = committed
            .probe(|probe| {
                recognize_derives_attachment_start(
                    DerivesAttachmentOwner::Struct,
                    DerivesAttachmentPosition::Trailing,
                    intro.struct_base,
                    probe.input(),
                )
            })
            .map(|start| {
                commit_derives_attachments_with_companion_handoff_isolated(start, committed)
            });
        let trailing_companion_tail = trailing.as_ref().and_then(|parsed| parsed.tail);
        if let Some(parsed) = trailing {
            derives.extend(parsed.attachments);
        }
        let trailing_companion_pending = trailing_companion_tail.is_some()
            || committed.probe(|probe| {
                recognize_declaration_companion_handoff(intro.struct_base, probe.input()).is_some()
            });
        if trailing_companion_pending {
            if let Some(tail) = trailing_companion_tail {
                debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Struct);
                debug_assert_eq!(tail.position, DerivesAttachmentPosition::Trailing);
            }
            let _ = commit_struct_declaration_companion_after_handoff(
                table,
                intro.struct_base,
                committed,
            );
        }
    }
    committed.finish_node();
    (Recovered::Complete(()), derives)
}

fn commit_struct_declaration_companion_after_handoff<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    struct_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Range<usize>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let leading = committed
        .probe(|probe| struct_continuation_trivia(struct_base, probe.input()))
        .expect("an accepted Struct companion handoff preserves its owner gap");
    committed.emit_trivia(&leading);
    commit_declaration_companion_isolated(table, struct_base, committed)
        .expect("an accepted Struct companion handoff preserves exact `with`")
}

pub(super) fn committed_struct_body_has_actual_trailing_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    starter: Option<StructBodyStarter>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.probe(|probe| {
        let i = probe.input();
        let expected_close = match starter {
            Some(StructBodyStarter::NamedBraced(_)) => b'}',
            Some(StructBodyStarter::Tuple(_)) => b')',
            Some(StructBodyStarter::Bodyless(_) | StructBodyStarter::NamedIndented(_)) | None => {
                return false;
            }
        };
        i.pos() > 0 && i.input.source().as_bytes().get(i.pos() - 1) == Some(&expected_close)
    })
}

pub(super) fn commit_struct_body_introducer<'parse, 'source, 'local, E, O>(
    struct_base: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut starter = committed.probe(|probe| struct_body_starter(probe.input()));
    let mut body_introducer_error = false;
    if starter.is_none() && !commit_word_candidate(committed) {
        match struct_body_introducer_error_retry(committed) {
            Some(true) => {
                starter = committed.probe(|probe| struct_body_starter(probe.input()));
            }
            Some(false) => body_introducer_error = true,
            None => {}
        }
    }

    match starter {
        Some(StructBodyStarter::Bodyless(range)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("a selected Struct semicolon remains available");
            debug_assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
        }
        Some(StructBodyStarter::NamedBraced(range)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("a selected Struct brace remains available");
            debug_assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::LBrace, range.clone());
            commit_struct_named_braced_body(struct_base, range, committed);
        }
        Some(StructBodyStarter::Tuple(range)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("a selected Struct parenthesis remains available");
            debug_assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::LParen, range.clone());
            commit_struct_tuple_body(struct_base, range, committed);
        }
        Some(StructBodyStarter::NamedIndented(range)) => {
            let punctuation = committed
                .probe(|probe| probe.input().run(scan_punctuation))
                .expect("a selected Struct colon remains available");
            debug_assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range.clone());
            commit_struct_named_indented_body(struct_base, range, committed);
        }
        None if !body_introducer_error => emit_struct_body_introducer_missing(committed),
        None => {}
    }
}

pub(super) fn commit_struct_named_indented_body<'parse, 'source, 'local, E, O>(
    struct_base: usize,
    colon: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let opening =
        committed.probe(|probe| consume_struct_indented_opening(struct_base, probe.input()));
    let Some((opening, block_indent)) = opening else {
        emit_struct_missing(
            committed,
            crate::session::StructRole::Field,
            ExpectedSyntax::Identifier,
        );
        return;
    };
    committed.emit_trivia(&opening);
    let stops = committed.probe(|probe| {
        probe
            .input()
            .local
            .stop_set()
            .unwrap_or_default()
            .without(StopKind::Newline)
            .with(StopKind::Comma)
    });
    committed.probe(|probe| {
        let i = probe.input();
        i.local.push_stop_set(stops);
        push_struct_indented_layout(block_indent, i);
    });

    let mut field_count = 0usize;
    loop {
        if committed
            .probe(|probe| struct_indented_terminal_boundary_pending(block_indent, probe.input()))
        {
            if field_count == 0 {
                commit_empty_struct_named_field(committed);
            }
            break;
        }
        if committed.probe(|probe| scan_struct_comma_pending(probe.input())) {
            commit_empty_struct_named_field(committed);
            field_count += 1;
            let comma = committed
                .probe(|probe| scan_struct_comma(probe.input()))
                .expect("the empty Struct field slot is followed by its comma");
            committed.token(SyntaxKind::Comma, comma);
            match commit_struct_indented_gap(block_indent, committed) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_)
                    if committed.probe(|probe| {
                        struct_indented_terminal_boundary_pending(block_indent, probe.input())
                    }) =>
                {
                    break;
                }
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            match commit_struct_indented_gap(block_indent, committed) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_) => continue,
            }
        }

        if !commit_struct_named_field(false, committed) {
            if let Some(run) =
                committed.probe(|probe| scan_struct_field_invalid_run(false, probe.input()))
            {
                emit_struct_error(
                    committed,
                    crate::session::StructRole::Field,
                    run.range,
                    ExpectedSyntax::Identifier,
                );
                field_count += 1;
                match commit_struct_indented_gap(block_indent, committed) {
                    StructIndentedGap::Dedent => break,
                    StructIndentedGap::Trivia(_) => continue,
                }
            } else {
                commit_empty_struct_named_field(committed);
                break;
            }
        }
        field_count += 1;

        let gap = commit_struct_indented_gap(block_indent, committed);
        if matches!(gap, StructIndentedGap::Dedent) {
            break;
        }
        let StructIndentedGap::Trivia(trivia) = gap else {
            unreachable!()
        };
        let newline_boundary = committed.probe(|probe| {
            struct_trivia_has_newline(&trivia)
                && probe.input().local.line().line_indent == block_indent
        });
        if newline_boundary {
            continue;
        }
        if let Some(comma) = committed.probe(|probe| scan_struct_comma(probe.input())) {
            committed.token(SyntaxKind::Comma, comma);
            match commit_struct_indented_gap(block_indent, committed) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_)
                    if committed.probe(|probe| {
                        struct_indented_terminal_boundary_pending(block_indent, probe.input())
                    }) =>
                {
                    break;
                }
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            let _ = commit_struct_indented_gap(block_indent, committed);
            continue;
        }
        if committed
            .probe(|probe| struct_indented_terminal_boundary_pending(block_indent, probe.input()))
        {
            break;
        }
        if committed.probe(|probe| struct_next_named_field_candidate(probe.input(), &trivia)) {
            emit_struct_missing(
                committed,
                crate::session::StructRole::FieldSeparator,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            continue;
        }
        break;
    }

    committed.probe(|probe| {
        let i = probe.input();
        pop_struct_indented_layout(block_indent, i);
        assert_eq!(i.local.pop_stop_set(), Some(stops));
    });
    let _ = colon;
}

pub(super) fn commit_struct_tuple_body<'parse, 'source, 'local, E, O>(
    struct_base: usize,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
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
    let layout = committed.probe(|probe| {
        LayoutDelimitedFrame::after_opening_trivia(
            struct_base,
            &opening,
            probe.input().local.line().line_indent,
        )
    });
    committed.probe(|probe| push_struct_layout(layout, probe.input()));

    loop {
        if let Some(close) = committed.probe(|probe| scan_struct_close_parenthesis(probe.input())) {
            committed.token(SyntaxKind::RParen, close);
            break;
        }
        if committed.probe(|probe| {
            struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, probe.input())
        }) {
            emit_struct_missing_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
            );
            break;
        }
        if let Some((range, actual)) = committed
            .probe(|probe| scan_struct_mismatched_close_for(Delimiter::Parenthesis, probe.input()))
        {
            emit_struct_mismatched_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
                range,
                actual,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if committed.probe(|probe| probe.input().input.remainder().is_empty()) {
            emit_struct_missing_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
            );
            break;
        }
        if committed.probe(|probe| scan_struct_comma_pending(probe.input())) {
            commit_empty_struct_tuple_field(committed);
            let comma = committed
                .probe(|probe| scan_struct_comma(probe.input()))
                .expect("the empty Struct tuple slot is followed by its comma");
            committed.token(SyntaxKind::Comma, comma);
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }

        commit_struct_tuple_field(committed);
        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            emit_struct_missing_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
            );
            break;
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
            if let Some(close) =
                committed.probe(|probe| scan_struct_close_parenthesis(probe.input()))
            {
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
                commit_empty_struct_tuple_field(committed);
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            continue;
        }
        if let Some(close) = committed.probe(|probe| scan_struct_close_parenthesis(probe.input())) {
            committed.token(SyntaxKind::RParen, close);
            break;
        }
        if committed.probe(|probe| {
            layout.boundary_after_trivia(&trivia, probe.input().local.line().line_indent)
                == LayoutDelimitedBoundary::ImplicitNewline
        }) {
            continue;
        }
        if committed.probe(|probe| {
            struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, probe.input())
        }) {
            emit_struct_missing_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
            );
            break;
        }
        if let Some((range, actual)) = committed
            .probe(|probe| scan_struct_mismatched_close_for(Delimiter::Parenthesis, probe.input()))
        {
            emit_struct_mismatched_close_for(
                committed,
                ConstructRole::StructTupleFields,
                Delimiter::Parenthesis,
                range,
                actual,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close_for(
                    committed,
                    ConstructRole::StructTupleFields,
                    Delimiter::Parenthesis,
                );
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        emit_struct_missing_close_for(
            committed,
            ConstructRole::StructTupleFields,
            Delimiter::Parenthesis,
        );
        break;
    }

    committed.probe(|probe| {
        let i = probe.input();
        pop_struct_layout(layout, i);
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    });
    let _ = open;
}

pub(super) fn commit_empty_struct_tuple_field<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_variant_tuple_field(VariantFieldDriverSpec::Struct, committed);
}

pub(super) fn commit_struct_tuple_field<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_variant_tuple_field(VariantFieldDriverSpec::Struct, committed);
}

#[derive(Clone)]
pub(super) enum StructBodyStarter {
    Bodyless(Range<usize>),
    NamedBraced(Range<usize>),
    Tuple(Range<usize>),
    NamedIndented(Range<usize>),
}

pub(super) fn struct_body_starter<E>(i: &mut SynIn<E>) -> Option<StructBodyStarter>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let punctuation = i.run(scan_punctuation)?;
    let starter = match punctuation.kind() {
        PunctuationKind::Semicolon => StructBodyStarter::Bodyless(punctuation.range()),
        PunctuationKind::Open(Delimiter::Brace) => {
            StructBodyStarter::NamedBraced(punctuation.range())
        }
        PunctuationKind::Open(Delimiter::Parenthesis) => {
            StructBodyStarter::Tuple(punctuation.range())
        }
        PunctuationKind::Colon => StructBodyStarter::NamedIndented(punctuation.range()),
        _ => {
            i.rollback(checkpoint);
            return None;
        }
    };
    i.rollback(checkpoint);
    Some(starter)
}

pub(super) fn struct_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_body_starter(i).is_some()
}

pub(super) fn emit_struct_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::StructRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Struct(role));
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

pub(super) fn emit_struct_body_introducer_missing<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = GrammarRole::Declaration(DeclarationRole::Struct(
            crate::session::StructRole::BodyIntroducer,
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
                        crate::session::PunctuationEvidence::Open(Delimiter::Parenthesis),
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

pub(super) fn struct_name_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_error_retry(
        committed,
        crate::session::StructRole::Name,
        ExpectedSyntax::Identifier,
        |i| struct_body_starter_pending(i),
        |i| struct_word_pending(i),
        |_| false,
    )
}

pub(super) fn struct_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_error_retry(
        committed,
        crate::session::StructRole::BodyIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        |_| false,
        |i| struct_body_starter_pending(i),
        |i| struct_word_pending(i) || struct_double_colon_pending(i),
    )
}

pub(super) fn struct_double_colon_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i
        .run(scan_punctuation)
        .is_some_and(|punctuation| punctuation.kind() == PunctuationKind::ColonColon);
    i.rollback(checkpoint);
    pending
}

pub(super) fn struct_error_retry<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::StructRole,
    expected: ExpectedSyntax,
    safe_boundary: impl Fn(&mut SynIn<E>) -> bool,
    retry_after_error: impl Fn(&mut SynIn<E>) -> bool,
    terminal_candidate: impl Fn(&mut SynIn<E>) -> bool,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let recovered = committed.probe(|probe| {
        let start = probe.input().pos();
        let mut end = start;
        loop {
            let i = probe.input();
            let Some(character) = i.input.remainder().chars().next() else {
                return (start < end).then_some((start..end, false));
            };
            if matches!(character, '\r' | '\n' | ';' | ',' | ')' | ']' | '}')
                || safe_boundary(i)
                || terminal_candidate(i)
            {
                return (start < end).then_some((start..end, false));
            }
            i.input.next()?;
            end = i.pos();
            let mut line = i.local.line();
            line.at_line_start = false;
            i.local.set_line(line);
            if retry_after_error(i) {
                return Some((start..end, true));
            }
        }
    })?;
    let (range, retry) = recovered;
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Struct(role));
        let source = ExpectationSources::COMMITTED_RECOVERY_RULE;
        let expectations: Arc<[SyntaxExpectation]> = match role {
            GrammarRole::Declaration(DeclarationRole::Struct(
                crate::session::StructRole::BodyIntroducer,
            )) => Arc::from([
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
                        crate::session::PunctuationEvidence::Open(Delimiter::Brace),
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Open(Delimiter::Parenthesis),
                    ),
                    range: range.clone(),
                    sources: source,
                },
                SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Punctuation(
                        crate::session::PunctuationEvidence::Colon,
                    ),
                    range: range.clone(),
                    sources: source,
                },
            ]),
            _ => Arc::from([SyntaxExpectation {
                role,
                expected,
                range: range.clone(),
                sources: source,
            }]),
        };
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
            expectations,
            0,
        )
    });
    committed.emit_error(record);
    Some(retry)
}

/// A structure declaration shared by root and nested canonical Statements.
///
/// Its parser and direct-CST continuation are wired in later slices; these
/// types preserve the approved surface shape without introducing any future
/// declaration features.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructDeclaration<'source> {
    pub(super) visibility: Visibility,
    pub(super) name: Recovered<WordSpan<'source>>,
    pub(super) derives: Vec<DerivesAttachment<'source>>,
    pub(super) companion: Option<DeclarationCompanion<'source>>,
    pub(super) body: Recovered<StructBody<'source>>,
    pub(super) range: Range<usize>,
}

impl StructDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum StructBody<'source> {
    Bodyless { semicolon: Range<usize> },
    CompanionIntroduced,
    NamedBraced(StructNamedBracedBody<'source>),
    NamedIndented(StructNamedIndentedBody<'source>),
    Tuple(StructTupleBody<'source>),
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructNamedBracedBody<'source> {
    pub(super) open: Range<usize>,
    pub(super) fields: Vec<Recovered<StructNamedField<'source>>>,
    pub(super) trailing_comma: Option<Range<usize>>,
    pub(super) close: Recovered<Range<usize>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructNamedIndentedBody<'source> {
    pub(super) colon: Range<usize>,
    pub(super) base_indent: usize,
    pub(super) block_indent: usize,
    pub(super) fields: Vec<Recovered<StructNamedField<'source>>>,
    pub(super) trailing_comma: Option<Range<usize>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructTupleBody<'source> {
    pub(super) open: Range<usize>,
    pub(super) fields: Vec<Recovered<StructTupleField<'source>>>,
    pub(super) trailing_comma: Option<Range<usize>>,
    pub(super) close: Recovered<Range<usize>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructNamedField<'source> {
    pub(super) name: Recovered<WordSpan<'source>>,
    pub(super) colon: Recovered<Range<usize>>,
    pub(super) type_expr: Recovered<Box<TypeExpression<'source>>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct StructTupleField<'source> {
    pub(super) type_expr: Recovered<Box<TypeExpression<'source>>>,
    pub(super) range: Range<usize>,
}

/// Parses the Struct declaration through the derives-aware promotion core.
pub(crate) fn parse_struct_declaration<'source, E>(
    i: SynIn<'_, 'source, '_, E>,
) -> Option<StructDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_struct_declaration_with_operators(&crate::operator::OperatorTable::empty(), i)
}

pub(crate) fn parse_struct_declaration_with_operators<'source, E>(
    table: &crate::operator::OperatorTable,
    i: SynIn<'_, 'source, '_, E>,
) -> Option<StructDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_struct_declaration_with_derives_and_companion_isolated(table, i)
}

/// Shared promotion core for Struct derives attachments. Keeping header/body
/// ownership here gives the public entry and focused harness one code path.
pub(super) fn parse_struct_declaration_with_derives_isolated<'source, E>(
    i: SynIn<'_, 'source, '_, E>,
) -> Option<StructDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_struct_declaration_with_derives_and_companion_isolated(
        &crate::operator::OperatorTable::empty(),
        i,
    )
}

fn parse_struct_declaration_with_derives_and_companion_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<StructDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let intro = i.run(recognize_struct_statement_intro)?;
    let _ = struct_continuation_trivia(intro.struct_base, &mut i);
    let mut name_incomplete = false;
    let name = if let Some(name) = i.run(scan_word) {
        Recovered::Complete(name)
    } else {
        match struct_name_error_retry_ast(&mut i) {
            Some(true) => Recovered::Complete(
                i.run(scan_word)
                    .expect("a Struct name retry must leave its raw word at the cursor"),
            ),
            Some(false) | None => {
                name_incomplete = true;
                Recovered::Incomplete
            }
        }
    };

    let (mut derives, header_companion_tail) = if matches!(name, Recovered::Complete(_)) {
        recognize_derives_attachment_start(
            DerivesAttachmentOwner::Struct,
            DerivesAttachmentPosition::Header,
            intro.struct_base,
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
    let header_companion_pending = !name_incomplete
        && (header_companion_tail.is_some()
            || recognize_declaration_companion_handoff(intro.struct_base, &mut i).is_some());
    let body = if header_companion_pending {
        if let Some(tail) = header_companion_tail {
            debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Struct);
            debug_assert_eq!(tail.position, DerivesAttachmentPosition::Header);
        }
        companion = Some(parse_struct_declaration_companion_after_handoff(
            table,
            intro.struct_base,
            &mut i,
        ));
        Recovered::Complete(StructBody::CompanionIntroduced)
    } else if !name_incomplete || struct_body_starter_pending(&mut i) {
        let _ = struct_continuation_trivia(intro.struct_base, &mut i);
        parse_struct_body_ast(intro.struct_base, &mut i)
            .map_or(Recovered::Incomplete, Recovered::Complete)
    } else {
        Recovered::Incomplete
    };
    if struct_body_has_actual_trailing_close(&body) {
        let trailing = recognize_derives_attachment_start(
            DerivesAttachmentOwner::Struct,
            DerivesAttachmentPosition::Trailing,
            intro.struct_base,
            &mut i,
        )
        .map(|start| parse_derives_attachments_with_companion_handoff_isolated(start, &mut i));
        let trailing_companion_tail = trailing.as_ref().and_then(|parsed| parsed.tail);
        if let Some(parsed) = trailing {
            derives.extend(parsed.attachments);
        }
        let trailing_companion_pending = trailing_companion_tail.is_some()
            || recognize_declaration_companion_handoff(intro.struct_base, &mut i).is_some();
        if trailing_companion_pending {
            if let Some(tail) = trailing_companion_tail {
                debug_assert_eq!(tail.owner, DerivesAttachmentOwner::Struct);
                debug_assert_eq!(tail.position, DerivesAttachmentPosition::Trailing);
            }
            companion = Some(parse_struct_declaration_companion_after_handoff(
                table,
                intro.struct_base,
                &mut i,
            ));
        }
    }

    let body_end = match &body {
        Recovered::Complete(StructBody::Bodyless { semicolon }) => semicolon.end,
        Recovered::Complete(StructBody::CompanionIntroduced) => {
            companion
                .as_ref()
                .expect("CompanionIntroduced is created only with a Struct companion")
                .range
                .end
        }
        Recovered::Complete(StructBody::NamedBraced(body)) => body.range.end,
        Recovered::Complete(StructBody::NamedIndented(body)) => body.range.end,
        Recovered::Complete(StructBody::Tuple(body)) => body.range.end,
        Recovered::Incomplete => match &name {
            Recovered::Complete(name) => name.range().end,
            Recovered::Incomplete => intro.struct_keyword.range().end,
        },
    };
    let derives_end = derives
        .last()
        .map_or(0, |attachment| attachment.clause.range.end);
    let companion_end = companion
        .as_ref()
        .map_or(0, |companion| companion.range.end);
    Some(StructDeclaration {
        visibility: intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility),
        name,
        derives,
        companion,
        body,
        range: intro.start..body_end.max(derives_end).max(companion_end),
    })
}

fn parse_struct_declaration_companion_after_handoff<'source, E>(
    table: &crate::operator::OperatorTable,
    struct_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> DeclarationCompanion<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_continuation_trivia(struct_base, i)
        .expect("an accepted Struct companion handoff preserves its owner gap");
    parse_declaration_companion_isolated(table, struct_base, i)
        .expect("an accepted Struct companion handoff preserves exact `with`")
}

pub(super) fn struct_body_has_actual_trailing_close(body: &Recovered<StructBody<'_>>) -> bool {
    matches!(
        body,
        Recovered::Complete(StructBody::NamedBraced(StructNamedBracedBody {
            close: Recovered::Complete(_),
            ..
        })) | Recovered::Complete(StructBody::Tuple(StructTupleBody {
            close: Recovered::Complete(_),
            ..
        }))
    )
}

pub(super) fn parse_struct_body_ast<'source, E>(
    struct_base: usize,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<StructBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let mut starter = struct_body_starter(i);
    if starter.is_none() && !struct_word_pending(i) {
        if struct_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
            starter = struct_body_starter(i);
        }
    }
    let starter = starter?;
    let punctuation = i
        .run(scan_punctuation)
        .expect("a selected Struct body starter remains available");
    match starter {
        StructBodyStarter::Bodyless(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::Bodyless { semicolon: range })
        }
        StructBodyStarter::NamedBraced(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::NamedBraced(parse_struct_named_braced_body_ast(
                struct_base,
                range,
                i,
            )))
        }
        StructBodyStarter::Tuple(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::Tuple(parse_struct_tuple_body_ast(
                struct_base,
                range,
                i,
            )))
        }
        StructBodyStarter::NamedIndented(range) => {
            debug_assert_eq!(punctuation.range(), range);
            Some(StructBody::NamedIndented(
                parse_struct_named_indented_body_ast(struct_base, range, i),
            ))
        }
    }
}

pub(super) fn parse_struct_named_indented_body_ast<'source, E>(
    struct_base: usize,
    colon: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> StructNamedIndentedBody<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let Some((opening, block_indent)) = consume_struct_indented_opening(struct_base, i) else {
        return StructNamedIndentedBody {
            colon: colon.clone(),
            base_indent: struct_base,
            block_indent: struct_base,
            fields: vec![Recovered::Incomplete],
            trailing_comma: None,
            range: colon,
        };
    };
    let stops = i
        .local
        .stop_set()
        .unwrap_or_default()
        .without(StopKind::Newline)
        .with(StopKind::Comma);
    i.local.push_stop_set(stops);
    push_struct_indented_layout(block_indent, i);

    let mut fields = Vec::new();
    let mut trailing_comma = None;
    loop {
        if struct_indented_terminal_boundary_pending(block_indent, i) {
            if fields.is_empty() {
                fields.push(Recovered::Incomplete);
            }
            break;
        }
        if let Some(comma) = scan_struct_comma(i) {
            fields.push(Recovered::Incomplete);
            match consume_struct_indented_gap(block_indent, i) {
                StructIndentedGap::Dedent => {
                    trailing_comma = Some(comma);
                    break;
                }
                StructIndentedGap::Trivia(_)
                    if struct_indented_terminal_boundary_pending(block_indent, i) =>
                {
                    trailing_comma = Some(comma);
                    break;
                }
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if scan_struct_semicolon(i).is_some() {
            match consume_struct_indented_gap(block_indent, i) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_) => continue,
            }
        }

        let field = if let Some(field) = parse_struct_named_field_ast(false, i) {
            Recovered::Complete(field)
        } else if scan_struct_field_invalid_run(false, i).is_some() {
            Recovered::Incomplete
        } else {
            fields.push(Recovered::Incomplete);
            break;
        };
        fields.push(field);

        let gap = consume_struct_indented_gap(block_indent, i);
        if matches!(gap, StructIndentedGap::Dedent) {
            break;
        }
        let StructIndentedGap::Trivia(trivia) = gap else {
            unreachable!()
        };
        if struct_trivia_has_newline(&trivia) && i.local.line().line_indent == block_indent {
            continue;
        }
        if let Some(comma) = scan_struct_comma(i) {
            let post = consume_struct_indented_gap(block_indent, i);
            match post {
                StructIndentedGap::Dedent => {
                    trailing_comma = Some(comma);
                    break;
                }
                StructIndentedGap::Trivia(_)
                    if struct_indented_terminal_boundary_pending(block_indent, i) =>
                {
                    trailing_comma = Some(comma);
                    break;
                }
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if scan_struct_semicolon(i).is_some() {
            match consume_struct_indented_gap(block_indent, i) {
                StructIndentedGap::Dedent => break,
                StructIndentedGap::Trivia(_) => continue,
            }
        }
        if struct_indented_terminal_boundary_pending(block_indent, i) {
            break;
        }
        if struct_next_named_field_candidate(i, &trivia) {
            continue;
        }
        break;
    }

    pop_struct_indented_layout(block_indent, i);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    let end = i.pos();
    let _ = opening;
    StructNamedIndentedBody {
        colon: colon.clone(),
        base_indent: struct_base,
        block_indent,
        fields,
        trailing_comma,
        range: colon.start..end,
    }
}

/// Parse the parenthesis-owned tuple field sequence.  It shares the Struct
/// list frame with named braces, but a tuple field is its mandatory type slot
/// directly: there is no field-head authority or named-field TypeApply guard.
pub(super) fn parse_struct_tuple_body_ast<'source, E>(
    struct_base: usize,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> StructTupleBody<'source>
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
    let opening = i.run(scan_trivia).expect("trivia is total");
    let layout = LayoutDelimitedFrame::after_opening_trivia(
        struct_base,
        &opening,
        i.local.line().line_indent,
    );
    push_struct_layout(layout, i);

    let mut fields = Vec::new();
    let mut trailing_comma = None;
    let close = loop {
        if let Some(close) = scan_struct_close_parenthesis(i) {
            break Recovered::Complete(close);
        }
        if struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, i) {
            break Recovered::Incomplete;
        }
        if scan_struct_mismatched_close_for(Delimiter::Parenthesis, i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if i.input.remainder().is_empty() {
            break Recovered::Incomplete;
        }
        if scan_struct_comma(i).is_some() {
            fields.push(Recovered::Incomplete);
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if scan_struct_semicolon(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }

        fields.push(parse_variant_tuple_field_ast(
            VariantFieldDriverSpec::Struct,
            i,
        ));

        if any_ambient_owner_claims(i) {
            break Recovered::Incomplete;
        }

        let trivia = i.run(scan_trivia).expect("trivia is total");
        if let Some(comma) = scan_struct_comma(i) {
            let post = i.run(scan_trivia).expect("trivia is total");
            if let Some(close) = scan_struct_close_parenthesis(i) {
                trailing_comma = Some(comma);
                break Recovered::Complete(close);
            }
            if i.input.remainder().is_empty()
                || struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, i)
            {
                fields.push(Recovered::Incomplete);
                break Recovered::Incomplete;
            }
            let _ = post;
            continue;
        }
        if let Some(close) = scan_struct_close_parenthesis(i) {
            break Recovered::Complete(close);
        }
        if layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
            == LayoutDelimitedBoundary::ImplicitNewline
        {
            continue;
        }
        if struct_outer_owned_mismatched_close_pending_for(Delimiter::Parenthesis, i) {
            break Recovered::Incomplete;
        }
        if scan_struct_mismatched_close_for(Delimiter::Parenthesis, i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if scan_struct_semicolon(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        break Recovered::Incomplete;
    };

    pop_struct_layout(layout, i);
    assert_eq!(i.local.pop_stop_set(), Some(stops));
    assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Parenthesis));
    let end = match &close {
        Recovered::Complete(close) => close.end,
        Recovered::Incomplete => i.pos(),
    };
    StructTupleBody {
        open: open.clone(),
        fields,
        trailing_comma,
        close,
        range: open.start..end,
    }
}

/// Parse the brace-owned named field sequence.  The layout frame is captured
/// once after the opener; unlike type records, this declaration owns its own
/// field and close recovery vocabulary.
pub(super) fn parse_struct_named_braced_body_ast<'source, E>(
    struct_base: usize,
    open: Range<usize>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> StructNamedBracedBody<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = struct_base;
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
        LayoutDelimitedFrame::after_opening_trivia(incoming, &opening, i.local.line().line_indent);
    push_struct_layout(layout, i);

    let mut fields = Vec::new();
    let mut trailing_comma = None;
    let close = loop {
        if let Some(close) = scan_struct_close_brace(i) {
            break Recovered::Complete(close);
        }
        if struct_outer_owned_mismatched_close_pending(i) {
            break Recovered::Incomplete;
        }
        if scan_struct_mismatched_close(i).is_some() {
            // A local mismatched closer belongs to this close slot.  Its
            // following trivia must not manufacture an empty field before
            // the retry reaches this frame's matching close.
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if i.input.remainder().is_empty() {
            break Recovered::Incomplete;
        }
        if let Some(_comma) = scan_struct_comma(i) {
            fields.push(Recovered::Incomplete);
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if scan_struct_semicolon(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        let field = if let Some(field) = parse_struct_named_field_ast(true, i) {
            Recovered::Complete(field)
        } else if scan_struct_field_invalid_run(false, i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            Recovered::Incomplete
        } else {
            break Recovered::Incomplete;
        };
        fields.push(field);

        if matches!(fields.last(), Some(Recovered::Incomplete)) {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            continue;
        }

        if any_ambient_owner_claims(i) {
            break Recovered::Incomplete;
        }
        let trivia = i.run(scan_trivia).expect("trivia is total");
        if let Some(comma) = scan_struct_comma(i) {
            let post = i.run(scan_trivia).expect("trivia is total");
            if let Some(close) = scan_struct_close_brace(i) {
                trailing_comma = Some(comma);
                break Recovered::Complete(close);
            }
            if i.input.remainder().is_empty() || struct_outer_owned_mismatched_close_pending(i) {
                fields.push(Recovered::Incomplete);
                break Recovered::Incomplete;
            }
            let _ = post;
            continue;
        }
        if let Some(close) = scan_struct_close_brace(i) {
            break Recovered::Complete(close);
        }
        if layout.boundary_after_trivia(&trivia, i.local.line().line_indent)
            == LayoutDelimitedBoundary::ImplicitNewline
        {
            if i.input.remainder().is_empty() || struct_outer_owned_mismatched_close_pending(i) {
                fields.push(Recovered::Incomplete);
                break Recovered::Incomplete;
            }
            continue;
        }
        if struct_next_named_field_candidate(i, &trivia) {
            continue;
        }
        if struct_outer_owned_mismatched_close_pending(i) {
            break Recovered::Incomplete;
        }
        if scan_struct_mismatched_close(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
            continue;
        }
        if scan_struct_semicolon(i).is_some() {
            if any_ambient_owner_claims(i) {
                break Recovered::Incomplete;
            }
            let _ = i.run(scan_trivia).expect("trivia is total");
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
    StructNamedBracedBody {
        open: open.clone(),
        fields,
        trailing_comma,
        close,
        range: open.start..end,
    }
}

pub(super) fn parse_struct_named_field_ast<'source, E>(
    ambient_sensitive: bool,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<StructNamedField<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_variant_named_field_ast(VariantFieldDriverSpec::Struct, ambient_sensitive, i)
}

pub(super) fn commit_struct_named_braced_body<'parse, 'source, 'local, E, O>(
    struct_base: usize,
    open: Range<usize>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let incoming = struct_base;
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
            incoming,
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
        if committed.probe(|probe| struct_outer_owned_mismatched_close_pending(probe.input())) {
            emit_struct_missing_close(committed);
            break;
        }
        if let Some((range, actual)) =
            committed.probe(|probe| scan_struct_mismatched_close(probe.input()))
        {
            emit_struct_mismatched_close(committed, range, actual);
            // Keep recovery at the close slot: trivia after a consumed local
            // mismatch precedes the next close retry, not a field slot.
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if committed.probe(|probe| probe.input().input.remainder().is_empty()) {
            emit_struct_missing_close(committed);
            break;
        }
        if committed.probe(|probe| scan_struct_comma_pending(probe.input())) {
            commit_empty_struct_named_field(committed);
            let comma = committed
                .probe(|probe| scan_struct_comma(probe.input()))
                .expect("the empty Struct field slot is followed by its comma");
            committed.token(SyntaxKind::Comma, comma);
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if !commit_struct_named_field(true, committed) {
            if let Some(run) =
                committed.probe(|probe| scan_struct_field_invalid_run(false, probe.input()))
            {
                emit_struct_error(
                    committed,
                    crate::session::StructRole::Field,
                    run.range,
                    ExpectedSyntax::Identifier,
                );
                if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                    emit_struct_missing_close(committed);
                    break;
                }
                let trivia = committed
                    .probe(|probe| probe.input().run(scan_trivia))
                    .expect("trivia is total");
                committed.emit_trivia(&trivia);
                continue;
            } else {
                emit_struct_missing(
                    committed,
                    crate::session::StructRole::Field,
                    ExpectedSyntax::Identifier,
                );
                break;
            }
        }

        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            emit_struct_missing_close(committed);
            break;
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
            if let Some(close) = committed.probe(|probe| scan_struct_close_brace(probe.input())) {
                committed.token(SyntaxKind::RBrace, close);
                break;
            }
            if committed.probe(|probe| {
                probe.input().input.remainder().is_empty()
                    || struct_outer_owned_mismatched_close_pending(probe.input())
            }) {
                emit_struct_missing(
                    committed,
                    crate::session::StructRole::Field,
                    ExpectedSyntax::Identifier,
                );
                emit_struct_missing_close(committed);
                break;
            }
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
            if committed.probe(|probe| {
                probe.input().input.remainder().is_empty()
                    || struct_outer_owned_mismatched_close_pending(probe.input())
            }) {
                emit_struct_missing(
                    committed,
                    crate::session::StructRole::Field,
                    ExpectedSyntax::Identifier,
                );
                emit_struct_missing_close(committed);
                break;
            }
            continue;
        }
        if committed.probe(|probe| struct_next_named_field_candidate(probe.input(), &trivia)) {
            emit_struct_missing(
                committed,
                crate::session::StructRole::FieldSeparator,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            continue;
        }
        if committed.probe(|probe| struct_outer_owned_mismatched_close_pending(probe.input())) {
            emit_struct_missing_close(committed);
            break;
        }
        if let Some((range, actual)) =
            committed.probe(|probe| scan_struct_mismatched_close(probe.input()))
        {
            emit_struct_mismatched_close(committed, range, actual);
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        if let Some(semicolon) = committed.probe(|probe| scan_struct_semicolon(probe.input())) {
            emit_struct_error(
                committed,
                crate::session::StructRole::FieldSeparator,
                semicolon,
                ExpectedSyntax::DelimitedSequenceSeparator,
            );
            if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
                emit_struct_missing_close(committed);
                break;
            }
            let trivia = committed
                .probe(|probe| probe.input().run(scan_trivia))
                .expect("trivia is total");
            committed.emit_trivia(&trivia);
            continue;
        }
        emit_struct_missing_close(committed);
        break;
    }

    committed.probe(|probe| {
        let i = probe.input();
        pop_struct_layout(layout, i);
        assert_eq!(i.local.pop_stop_set(), Some(stops));
        assert_eq!(i.local.pop_delimiter(), Some(Delimiter::Brace));
    });
    let _ = open;
}

pub(super) fn commit_empty_struct_named_field<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    committed.start_node(SyntaxKind::StructField);
    emit_struct_missing(
        committed,
        crate::session::StructRole::Field,
        ExpectedSyntax::Identifier,
    );
    committed.finish_node();
}

pub(super) fn commit_struct_named_field<'parse, 'source, 'local, E, O>(
    ambient_sensitive: bool,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> bool
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_variant_named_field(VariantFieldDriverSpec::Struct, ambient_sensitive, committed)
}
pub(super) fn push_struct_indented_layout<E>(block_indent: usize, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    i.local.push_indentation_baseline(IndentationBaseline {
        column: block_indent,
        kind: IndentationBaselineKind::Block,
    });
}

pub(super) fn pop_struct_indented_layout<E>(block_indent: usize, i: &mut SynIn<E>)
where
    E: ErrorSink<usize>,
{
    assert_eq!(
        i.local.pop_indentation_baseline(),
        Some(IndentationBaseline {
            column: block_indent,
            kind: IndentationBaselineKind::Block,
        })
    );
}

#[derive(Clone, Debug)]
pub(super) enum StructIndentedGap {
    Trivia(TriviaRun),
    Dedent,
}

/// The colon body owns its opening run only when the first field line is
/// strictly deeper than the Struct header. Other trivia remains caller-owned
/// while its mandatory first field slot is recovered.
pub(super) fn consume_struct_indented_opening<E>(
    struct_base: usize,
    i: &mut SynIn<E>,
) -> Option<(TriviaRun, usize)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    let block_indent = i.local.line().line_indent;
    if struct_trivia_has_newline(&trivia) && block_indent > struct_base {
        Some((trivia, block_indent))
    } else {
        i.rollback(checkpoint);
        None
    }
}

/// Consume one inter-field gap without stealing a dedent. A same-column
/// newline is the implicit separator; a deeper line stays ordinary trivia so
/// the mandatory type entry retains continuation authority.
pub(super) fn consume_struct_indented_gap<E>(
    block_indent: usize,
    i: &mut SynIn<E>,
) -> StructIndentedGap
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia).expect("trivia is total");
    if struct_trivia_has_newline(&trivia) && i.local.line().line_indent < block_indent {
        i.rollback(checkpoint);
        StructIndentedGap::Dedent
    } else {
        StructIndentedGap::Trivia(trivia)
    }
}

pub(super) fn commit_struct_indented_gap<'parse, 'source, 'local, E, O>(
    block_indent: usize,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> StructIndentedGap
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let gap = committed.probe(|probe| consume_struct_indented_gap(block_indent, probe.input()));
    if let StructIndentedGap::Trivia(trivia) = &gap {
        committed.emit_trivia(trivia);
    }
    gap
}

pub(super) fn struct_indented_terminal_boundary_pending<E>(
    block_indent: usize,
    i: &mut SynIn<E>,
) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if i.input.remainder().is_empty() || struct_outer_close_pending(i) {
        return true;
    }
    let checkpoint = i.checkpoint();
    let gap = consume_struct_indented_gap(block_indent, i);
    let terminal = matches!(gap, StructIndentedGap::Dedent);
    i.rollback(checkpoint);
    terminal
}

pub(super) fn struct_outer_close_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        let stop = match punctuation.kind() {
            PunctuationKind::Close(Delimiter::Parenthesis) => Some(StopKind::RightParenthesis),
            PunctuationKind::Close(Delimiter::Bracket) => Some(StopKind::RightBracket),
            PunctuationKind::Close(Delimiter::Brace) => Some(StopKind::RightBrace),
            _ => None,
        };
        stop.is_some_and(|stop| i.local.stop_set().is_some_and(|stops| stops.contains(stop)))
    });
    i.rollback(checkpoint);
    pending
}

pub(super) fn scan_struct_mismatched_close<E>(i: &mut SynIn<E>) -> Option<(Range<usize>, Delimiter)>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    scan_struct_mismatched_close_for(Delimiter::Brace, i)
}

pub(super) fn struct_next_named_field_candidate<E>(i: &mut SynIn<E>, leading: &TriviaRun) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if leading.is_empty() || struct_trivia_has_newline(leading) {
        return false;
    }
    let checkpoint = i.checkpoint();
    let candidate = i.run(scan_word).is_some_and(|_| {
        let gap = i.run(scan_trivia).expect("trivia is total");
        !struct_trivia_has_newline(&gap) && scan_struct_colon(i).is_some()
    });
    i.rollback(checkpoint);
    candidate
}

pub(super) fn emit_struct_missing_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_struct_missing_close_for(
        committed,
        ConstructRole::StructNamedFields,
        Delimiter::Brace,
    );
}

pub(super) fn emit_struct_missing_close_for<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    owner: ConstructRole,
    delimiter: Delimiter,
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

pub(super) fn emit_struct_mismatched_close<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    range: Range<usize>,
    actual: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_struct_mismatched_close_for(
        committed,
        ConstructRole::StructNamedFields,
        Delimiter::Brace,
        range,
        actual,
    );
}

pub(super) fn emit_struct_mismatched_close_for<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    owner: ConstructRole,
    delimiter: Delimiter,
    range: Range<usize>,
    actual: Delimiter,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::ClosingDelimiter { owner, delimiter };
        CommittedRecoveryRecord::new(
            i.local,
            RecoverySiteKey {
                role,
                range: range.clone(),
            },
            RecoveryKind::Error,
            Arc::from([crate::session::UnexpectedSyntax::Token {
                range: range.clone(),
                category: crate::session::UnexpectedCategory::Punctuation(
                    crate::session::PunctuationEvidence::Close(actual),
                ),
            }]),
            Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Close(
                    delimiter,
                )),
                range,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        )
    });
    committed.emit_error(record);
}

pub(super) fn emit_struct_error<'parse, 'source, 'local, E, O>(
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: crate::session::StructRole,
    range: Range<usize>,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = GrammarRole::Declaration(DeclarationRole::Struct(role));
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

pub(super) fn struct_name_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_error_retry_ast(
        i,
        |i| struct_body_starter_pending(i),
        |i| struct_word_pending(i),
        |_| false,
    )
}

pub(super) fn struct_body_introducer_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    struct_error_retry_ast(
        i,
        |_| false,
        |i| struct_body_starter_pending(i),
        |i| struct_word_pending(i) || struct_double_colon_pending(i),
    )
}

pub(super) fn struct_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
    safe_boundary: impl Fn(&mut SynIn<'_, 'source, '_, E>) -> bool,
    retry_after_error: impl Fn(&mut SynIn<'_, 'source, '_, E>) -> bool,
    terminal_candidate: impl Fn(&mut SynIn<'_, 'source, '_, E>) -> bool,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        let character = i.input.remainder().chars().next()?;
        if matches!(character, '\r' | '\n' | ';' | ',' | ')' | ']' | '}')
            || safe_boundary(i)
            || terminal_candidate(i)
        {
            return (start < i.pos()).then_some(false);
        }
        i.input.next()?;
        let mut line = i.local.line();
        line.at_line_start = false;
        i.local.set_line(line);
        if retry_after_error(i) {
            return Some(true);
        }
    }
}

/// One maximal Struct continuation run. It may cross a newline only when the
/// next line stays inside the baseline captured by the Struct introduction.
pub(super) fn struct_continuation_trivia<E>(
    struct_base: usize,
    i: &mut SynIn<E>,
) -> Option<TriviaRun>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    mod_trivia(struct_base, i)
}
