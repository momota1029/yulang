use super::*;

/// A standalone Impl declaration shared by root and canonical Statements.
///
/// Gate 1 establishes only the approved AST shape. Recognition and body
/// parsing remain unreachable until their later dedicated gates.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ImplDeclaration<'source> {
    pub(super) visibility: Visibility,
    pub(super) head: Recovered<Box<TypeExpression<'source>>>,
    pub(super) description: Option<ImplDescription<'source>>,
    pub(super) body: Recovered<ImplBody<'source>>,
    pub(super) range: Range<usize>,
}

impl ImplDeclaration<'_> {
    pub(crate) fn range(&self) -> Range<usize> {
        self.range.clone()
    }
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ImplDescription<'source> {
    pub(super) colon: Range<usize>,
    pub(super) value: Recovered<Box<TypeExpression<'source>>>,
    pub(super) range: Range<usize>,
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ImplBody<'source> {
    Bodyless {
        semicolon: Range<usize>,
    },
    Braced {
        block: BracedStatementBlockExpression<'source>,
    },
    Colon {
        colon: Range<usize>,
        body: Recovered<ImplColonBody<'source>>,
    },
}

#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum ImplColonBody<'source> {
    Inline {
        statement: Box<Statement<'source>>,
    },
    Indented {
        block: IndentedStatementBlock<'source>,
    },
}

/// The sink-free prefix reserved for standalone Impl declarations.
///
/// Gate 1 carries this source shape only. Gate 2 supplies recognition, and
/// Gate 8 connects it to shared statement dispatch.
#[allow(dead_code)]
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ImplStatementIntro<'source> {
    pub(super) start: usize,
    pub(super) visibility: Option<VisibilityPrefix<'source>>,
    pub(super) after_visibility: Option<TriviaRun>,
    pub(super) impl_keyword: WordSpan<'source>,
    pub(super) impl_base: usize,
}

/// Recognizes the sink-free prefix reserved for a standalone Impl declaration.
///
/// This remains deliberately separate from `recognize_statement_intro` until
/// the later dispatch gate. An exact `impl` keyword establishes declaration
/// authority without probing its mandatory head or body.
pub(super) fn recognize_impl_statement_intro<'source, E>(
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ImplStatementIntro<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let start = i.pos();
    let first = i.run(scan_word)?;
    let impl_base = i
        .local
        .indentation_baseline()
        .map_or(0, |baseline| baseline.column);
    let (visibility, after_visibility, keyword) = if let Some(visibility) = visibility_prefix(first)
    {
        let Some(trivia) = mod_trivia(impl_base, &mut i).filter(|trivia| !trivia.is_empty()) else {
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
    if keyword.text() != "impl" {
        i.rollback(checkpoint);
        return None;
    }
    Some(ImplStatementIntro {
        start,
        visibility,
        after_visibility,
        impl_keyword: keyword,
        impl_base,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ImplTypeExpressionSlot {
    Head,
    Description,
}

#[allow(dead_code)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ImplTailOwner {
    Standalone,
    TypeAttached,
}

/// The sole owner-specific input to the shared post-keyword Impl grammar.
/// Intro recognition, visibility, and the outer declaration node stay with
/// the caller; this spec selects only layout and outer recovery ownership.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ImplTailOwnerSpec {
    pub(super) owner: ImplTailOwner,
    pub(super) owner_base: usize,
}

impl ImplTailOwnerSpec {
    pub(super) fn grammar_role(self, role: ImplRole) -> GrammarRole {
        match self.owner {
            ImplTailOwner::Standalone => GrammarRole::Declaration(DeclarationRole::Impl(role)),
            ImplTailOwner::TypeAttached => GrammarRole::Declaration(DeclarationRole::Type(
                TypeDeclarationRole::AttachedImpl(role),
            )),
        }
    }
}

pub(super) fn standalone_impl_tail_owner_spec(owner_base: usize) -> ImplTailOwnerSpec {
    ImplTailOwnerSpec {
        owner: ImplTailOwner::Standalone,
        owner_base,
    }
}

/// The isolated owner adapter reserved for a Type-attached Impl tail.
///
/// The baseline remains Type's declaration baseline rather than the column of
/// the later `impl` keyword. Gate 4 supplies the first parsing caller.
#[allow(dead_code)]
pub(super) fn type_attached_impl_tail_owner_spec(type_base: usize) -> ImplTailOwnerSpec {
    ImplTailOwnerSpec {
        owner: ImplTailOwner::TypeAttached,
        owner_base: type_base,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) struct ImplTypeExpressionEpisodeSpec {
    pub(super) stops: StopSet,
    pub(super) scoped_frame: TypeExpressionScopedStopFrame,
    pub(super) policy: TypeExpressionEpisodePolicy,
    pub(super) outer_role: GrammarRole,
}

/// One outer Impl TypeExpression slot owns body punctuation only in its
/// logical episode. Nested TypeExpression episodes retain the raw stop bits
/// while the scoped frame suspends their ownership there.
pub(super) fn impl_type_expression_episode_spec(
    owner_spec: ImplTailOwnerSpec,
    slot: ImplTypeExpressionSlot,
    incoming: StopSet,
    current_episode_depth: usize,
) -> ImplTypeExpressionEpisodeSpec {
    let scoped_stops = StopSet::default()
        .with(StopKind::Colon)
        .with(StopKind::LeftBrace)
        .with(StopKind::Semicolon);
    let stops = incoming
        .with(StopKind::Colon)
        .with(StopKind::LeftBrace)
        .with(StopKind::Semicolon);
    let fresh_primary_locally_owned_stops = match slot {
        ImplTypeExpressionSlot::Head => StopSet::default(),
        ImplTypeExpressionSlot::Description => StopSet::default().with(StopKind::LeftBrace),
    };
    let role = match slot {
        ImplTypeExpressionSlot::Head => ImplRole::Head,
        ImplTypeExpressionSlot::Description => ImplRole::Description,
    };
    ImplTypeExpressionEpisodeSpec {
        stops,
        scoped_frame: TypeExpressionScopedStopFrame {
            stops: scoped_stops,
            visible_episode_depth: current_episode_depth + 1,
        },
        policy: TypeExpressionEpisodePolicy {
            fresh_primary_locally_owned_stops,
            fresh_primary_owns_adjacent_polymorphic_variant_starter: true,
        },
        outer_role: owner_spec.grammar_role(role),
    }
}

pub(super) fn parse_required_impl_tail_type_expression<'source, E>(
    owner_spec: ImplTailOwnerSpec,
    slot: ImplTypeExpressionSlot,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let episode = impl_type_expression_episode_spec(
        owner_spec,
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
                parse_required_type_expression_with_outer_missing_role_and_policy(
                    Some(episode.outer_role),
                    episode.policy,
                    i,
                ),
            )
        }))
        .expect("the mandatory Impl TypeExpression entry is total");
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

pub(super) fn commit_required_impl_tail_type_expression<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    slot: ImplTypeExpressionSlot,
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
        impl_type_expression_episode_spec(
            owner_spec,
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

#[cfg(test)]
pub(super) fn parse_required_impl_type_expression_isolated<'source, E>(
    slot: ImplTypeExpressionSlot,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<Box<TypeExpression<'source>>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    parse_required_impl_tail_type_expression(standalone_impl_tail_owner_spec(0), slot, i)
}

#[cfg(test)]
pub(super) fn commit_required_impl_type_expression_isolated<'parse, 'source, 'local, E, O>(
    slot: ImplTypeExpressionSlot,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    commit_required_impl_tail_type_expression(standalone_impl_tail_owner_spec(0), slot, committed)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ParsedImplTail<'source> {
    pub(super) head: Recovered<Box<TypeExpression<'source>>>,
    pub(super) description: Option<ImplDescription<'source>>,
    pub(super) body: Recovered<ImplBody<'source>>,
}

/// Standalone AST adapter used by root and canonical Statement dispatch.
/// Intro recognition and declaration realization stay here; the post-keyword
/// grammar is shared with the future Type-owned adapter.
pub(crate) fn parse_impl_declaration_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    mut i: SynIn<'_, 'source, '_, E>,
) -> Option<ImplDeclaration<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let declaration = (|| {
        let intro = i.run(recognize_impl_statement_intro)?;
        let visibility = intro
            .visibility
            .map_or(Visibility::Private, |prefix| prefix.visibility);
        let tail = parse_impl_tail_ast(
            table,
            standalone_impl_tail_owner_spec(intro.impl_base),
            &mut i,
        );
        let end = i.pos();
        Some(ImplDeclaration {
            visibility,
            head: tail.head,
            description: tail.description,
            body: tail.body,
            range: intro.start..end,
        })
    })();
    i.errors_rollback(errors_checkpoint);
    declaration
}

pub(super) fn parse_impl_tail_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> ParsedImplTail<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let head = if any_ambient_owner_claims(i) {
        Recovered::Incomplete
    } else {
        let checkpoint = i.checkpoint();
        if mod_trivia(owner_spec.owner_base, i).is_some() {
            parse_required_impl_tail_type_expression(owner_spec, ImplTypeExpressionSlot::Head, i)
        } else {
            i.rollback(checkpoint);
            Recovered::Incomplete
        }
    };
    let (description, body) = parse_impl_after_head_ast(table, owner_spec, i);
    ParsedImplTail {
        head,
        description,
        body,
    }
}

/// Type-owned AST realization after the sink-free post-header judge has cut
/// to its exact `impl` evidence. The shared tail supplies every post-keyword
/// slot; this adapter contributes only the Type form payload and its range.
pub(super) fn parse_type_attached_impl_isolated<'source, E>(
    table: &crate::operator::OperatorTable,
    start: TypeAttachedImplStart<'source>,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> TypeAttachedImpl<'source>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = i.errors_checkpoint();
    let leading = i
        .run(scan_trivia)
        .expect("the accepted Type-attached Impl gap remains at the cursor");
    debug_assert_eq!(leading.range(), start.leading.range());
    let keyword = i
        .run(scan_word)
        .expect("the accepted Type-attached Impl keyword remains at the cursor");
    debug_assert_eq!(keyword.range(), start.keyword.range());
    debug_assert_eq!(keyword.text(), "impl");

    let tail = parse_impl_tail_ast(
        table,
        type_attached_impl_tail_owner_spec(start.type_base),
        i,
    );
    let end = i.pos();
    let attached = TypeAttachedImpl {
        impl_keyword: keyword.range(),
        head: tail.head,
        description: tail.description,
        body: tail.body,
        range: keyword.range().start..end,
    };
    i.errors_rollback(errors_checkpoint);
    attached
}

pub(super) fn parse_impl_after_head_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> (
    Option<ImplDescription<'source>>,
    Recovered<ImplBody<'source>>,
)
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return (None, Recovered::Incomplete);
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(owner_spec.owner_base, i) else {
        i.rollback(checkpoint);
        return (None, Recovered::Incomplete);
    };
    let colon = i.run(scan_punctuation).and_then(|punctuation| {
        (punctuation.kind() == PunctuationKind::Colon).then_some(punctuation.range())
    });
    let Some(colon) = colon else {
        i.rollback(checkpoint);
        return (None, parse_impl_body_ast(table, owner_spec, i));
    };

    let description_trivia_checkpoint = i.checkpoint();
    let description_trivia = i.run(scan_trivia).expect("trivia scan is total");
    if i.input.source()[description_trivia.range()].contains(['\r', '\n']) {
        i.rollback(description_trivia_checkpoint);
        i.rollback(checkpoint);
        return (None, parse_impl_body_ast(table, owner_spec, i));
    }
    let value = parse_required_impl_tail_type_expression(
        owner_spec,
        ImplTypeExpressionSlot::Description,
        i,
    );
    let description = ImplDescription {
        colon: colon.clone(),
        value,
        range: colon.start..i.pos(),
    };
    let body = parse_impl_body_ast(table, owner_spec, i);
    (Some(description), body)
}

pub(super) fn parse_impl_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Recovered<ImplBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if any_ambient_owner_claims(i) {
        return Recovered::Incomplete;
    }
    let checkpoint = i.checkpoint();
    let Some(_) = mod_trivia(owner_spec.owner_base, i) else {
        i.rollback(checkpoint);
        return Recovered::Incomplete;
    };
    let Some(punctuation) = i.run(scan_punctuation) else {
        i.rollback(checkpoint);
        if impl_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
            return parse_impl_body_ast(table, owner_spec, i);
        }
        return Recovered::Incomplete;
    };
    match punctuation.kind() {
        PunctuationKind::Semicolon => Recovered::Complete(ImplBody::Bodyless {
            semicolon: punctuation.range(),
        }),
        PunctuationKind::Open(Delimiter::Brace) => Recovered::Complete(ImplBody::Braced {
            block: parse_braced_statement_block_expression(table, punctuation.range(), i),
        }),
        PunctuationKind::Colon => Recovered::Complete(ImplBody::Colon {
            colon: punctuation.range(),
            body: parse_impl_colon_body_ast(table, owner_spec, i)
                .map_or(Recovered::Incomplete, Recovered::Complete),
        }),
        _ => {
            i.rollback(checkpoint);
            if impl_body_introducer_error_retry_ast(i).is_some_and(|retry| retry) {
                return parse_impl_body_ast(table, owner_spec, i);
            }
            Recovered::Incomplete
        }
    }
}

pub(super) fn parse_impl_colon_body_ast<'source, E>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<ImplColonBody<'source>>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let trivia = i.run(scan_trivia)?;
    if i.input.source()[trivia.range()].contains(['\r', '\n']) {
        if i.local.line().line_indent <= owner_spec.owner_base {
            i.rollback(checkpoint);
            return None;
        }
        let block_indent = i.local.line().line_indent;
        return Some(ImplColonBody::Indented {
            block: parse_indented_impl_tail_body(
                table,
                trivia,
                owner_spec.owner_base,
                block_indent,
                owner_spec.grammar_role(ImplRole::IndentedStatement),
                i,
            ),
        });
    }
    let ambient_scope = i.local.push_inline_canonical_statement_ambient_scope(
        crate::session::InlineStatementOwnerKind::ImplColonBody,
    );
    let statement = i
        .run(from_fn(|i| parse_canonical_statement(table, i)))
        .or_else(|| {
            impl_body_error_retry_ast(table, i)
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
        ImplColonBody::Inline {
            statement: Box::new(statement),
        }
    });
    assert_eq!(i.local.pop_ambient_owner_scope(), Some(ambient_scope));
    body
}

/// Standalone direct-CST adapter. The caller-owned wrapper ends at `ImplKw`;
/// [`commit_impl_tail`] emits only the shared post-keyword continuation.
pub(crate) fn commit_impl_declaration_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    intro: ImplStatementIntro<'source>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    committed.start_node(SyntaxKind::ImplDeclaration);
    if let Some(visibility) = &intro.visibility {
        emit_visibility(committed, visibility);
        if let Some(trivia) = &intro.after_visibility {
            committed.emit_trivia(trivia);
        }
    }
    committed.token(SyntaxKind::ImplKw, intro.impl_keyword.range());
    commit_impl_tail(
        table,
        standalone_impl_tail_owner_spec(intro.impl_base),
        committed,
    );
    let end = committed_position(committed);
    committed.finish_node();
    committed.probe(|probe| {
        probe.input().errors_rollback(errors_checkpoint);
    });
    Recovered::Complete(intro.start..end)
}

pub(super) fn commit_impl_tail<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let head_terminated_incomplete =
        if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
            emit_impl_tail_missing(
                owner_spec,
                committed,
                ImplRole::Head,
                ExpectedSyntax::TypeExpression,
            );
            true
        } else if let Some(trivia) =
            committed.probe(|probe| mod_trivia(owner_spec.owner_base, probe.input()))
        {
            committed.emit_trivia(&trivia);
            matches!(
                commit_required_impl_tail_type_expression(
                    owner_spec,
                    ImplTypeExpressionSlot::Head,
                    committed,
                ),
                Recovered::Incomplete
            )
        } else {
            emit_impl_tail_missing(
                owner_spec,
                committed,
                ImplRole::Head,
                ExpectedSyntax::TypeExpression,
            );
            true
        };

    commit_impl_after_head(table, owner_spec, committed, head_terminated_incomplete);
}

/// Type-owned direct-CST realization for a caller that already opened its
/// `TypeDeclaration` and emitted the shared header. No declaration wrapper is
/// started here: the accepted gap, `ImplKw`, and shared tail remain flat
/// children of that caller-owned node.
pub(super) fn commit_type_attached_impl_isolated<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    start: TypeAttachedImplStart<'source>,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) -> Recovered<Range<usize>>
where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let errors_checkpoint = committed.probe(|probe| probe.input().errors_checkpoint());
    let leading = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("the accepted Type-attached Impl gap remains at the cursor");
    debug_assert_eq!(leading.range(), start.leading.range());
    committed.emit_trivia(&leading);
    let keyword = committed
        .probe(|probe| probe.input().run(scan_word))
        .expect("the accepted Type-attached Impl keyword remains at the cursor");
    debug_assert_eq!(keyword.range(), start.keyword.range());
    debug_assert_eq!(keyword.text(), "impl");
    committed.token(SyntaxKind::ImplKw, keyword.range());
    commit_impl_tail(
        table,
        type_attached_impl_tail_owner_spec(start.type_base),
        committed,
    );
    let range = Recovered::Complete(keyword.range().start..committed_position(committed));
    committed.probe(|probe| probe.input().errors_rollback(errors_checkpoint));
    range
}

pub(super) fn commit_impl_after_head<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    head_terminated_incomplete: bool,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        if !head_terminated_incomplete {
            emit_impl_tail_body_introducer_missing(owner_spec, committed);
        }
        return;
    }
    let description = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let result = mod_trivia(owner_spec.owner_base, i).and_then(|leading| {
            let colon = i.run(scan_punctuation).and_then(|punctuation| {
                (punctuation.kind() == PunctuationKind::Colon).then_some(punctuation.range())
            })?;
            let trailing = i.run(scan_trivia).expect("trivia scan is total");
            (!i.input.source()[trailing.range()].contains(['\r', '\n'])).then_some((leading, colon))
        });
        i.rollback(checkpoint);
        result
    });
    let Some((leading, colon)) = description else {
        commit_impl_body(table, owner_spec, committed, head_terminated_incomplete);
        return;
    };

    let consumed_leading = committed
        .probe(|probe| mod_trivia(owner_spec.owner_base, probe.input()))
        .expect("the shared description probe leaves its leading trivia at the cursor");
    assert_eq!(consumed_leading.range(), leading.range());
    committed.emit_trivia(&consumed_leading);
    committed.start_node(SyntaxKind::ImplDescription);
    let punctuation = committed
        .probe(|probe| probe.input().run(scan_punctuation))
        .expect("the isolated description probe leaves its colon at the cursor");
    assert_eq!(punctuation.range(), colon);
    committed.token(SyntaxKind::Colon, colon);
    let trivia = committed
        .probe(|probe| probe.input().run(scan_trivia))
        .expect("trivia scan is total");
    committed.emit_trivia(&trivia);
    let description = commit_required_impl_tail_type_expression(
        owner_spec,
        ImplTypeExpressionSlot::Description,
        committed,
    );
    committed.finish_node();
    commit_impl_body(
        table,
        owner_spec,
        committed,
        head_terminated_incomplete || matches!(description, Recovered::Incomplete),
    );
}

#[derive(Clone)]
pub(super) enum ImplBodyStarter {
    Bodyless(Range<usize>),
    Braced(Range<usize>),
    Colon(Range<usize>),
}

pub(super) fn commit_impl_body<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    upstream_slot_terminated_incomplete: bool,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    if committed.probe(|probe| any_ambient_owner_claims(probe.input())) {
        if !upstream_slot_terminated_incomplete {
            emit_impl_tail_body_introducer_missing(owner_spec, committed);
        }
        return;
    }
    let starter = committed.probe(|probe| {
        let i = probe.input();
        let checkpoint = i.checkpoint();
        let starter = mod_trivia(owner_spec.owner_base, i).and_then(|trivia| {
            let punctuation = i.run(scan_punctuation)?;
            let starter = match punctuation.kind() {
                PunctuationKind::Semicolon => ImplBodyStarter::Bodyless(punctuation.range()),
                PunctuationKind::Open(Delimiter::Brace) => {
                    ImplBodyStarter::Braced(punctuation.range())
                }
                PunctuationKind::Colon => ImplBodyStarter::Colon(punctuation.range()),
                _ => return None,
            };
            Some((trivia, starter))
        });
        i.rollback(checkpoint);
        starter
    });
    let Some((trivia, starter)) = starter else {
        let trivia = committed.probe(|probe| {
            let i = probe.input();
            let checkpoint = i.checkpoint();
            let trivia = mod_trivia(owner_spec.owner_base, i);
            i.rollback(checkpoint);
            trivia
        });
        let Some(trivia) = trivia else {
            if !upstream_slot_terminated_incomplete {
                emit_impl_tail_body_introducer_missing(owner_spec, committed);
            }
            return;
        };
        let newline = committed
            .probe(|probe| probe.input().input.source()[trivia.range()].contains(['\r', '\n']));
        if newline {
            if !upstream_slot_terminated_incomplete {
                emit_impl_tail_body_introducer_missing(owner_spec, committed);
            }
            return;
        }
        let consumed_trivia = committed
            .probe(|probe| mod_trivia(owner_spec.owner_base, probe.input()))
            .expect("the Impl body-introducer recovery leaves its leading trivia at the cursor");
        assert_eq!(consumed_trivia.range(), trivia.range());
        committed.emit_trivia(&consumed_trivia);
        match impl_body_introducer_error_retry(owner_spec, committed) {
            Some(true) => {
                commit_impl_body(
                    table,
                    owner_spec,
                    committed,
                    upstream_slot_terminated_incomplete,
                );
            }
            Some(false) => {}
            None if !upstream_slot_terminated_incomplete => {
                emit_impl_tail_body_introducer_missing(owner_spec, committed)
            }
            None => {}
        }
        return;
    };
    let consumed_trivia = committed
        .probe(|probe| mod_trivia(owner_spec.owner_base, probe.input()))
        .expect("the accepted Impl body starter leaves its leading trivia at the cursor");
    assert_eq!(consumed_trivia.range(), trivia.range());
    committed.emit_trivia(&consumed_trivia);
    let punctuation = committed
        .probe(|probe| probe.input().run(scan_punctuation))
        .expect("the accepted Impl body starter remains at the cursor");
    match starter {
        ImplBodyStarter::Bodyless(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Semicolon, range);
        }
        ImplBodyStarter::Braced(range) => {
            assert_eq!(punctuation.range(), range);
            commit_braced_statement_block_expression(table, range, committed);
        }
        ImplBodyStarter::Colon(range) => {
            assert_eq!(punctuation.range(), range);
            committed.token(SyntaxKind::Colon, range);
            commit_impl_colon_body(table, owner_spec, committed);
        }
    }
}

pub(super) fn commit_impl_colon_body<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
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
    if newline
        && committed.probe(|probe| probe.input().local.line().line_indent <= owner_spec.owner_base)
    {
        committed.probe(|probe| probe.input().rollback(checkpoint));
        emit_impl_tail_body_missing(owner_spec, committed);
        return;
    }
    if newline {
        let block_indent = committed.probe(|probe| probe.input().local.line().line_indent);
        commit_indented_impl_tail_body(
            table,
            trivia,
            owner_spec.owner_base,
            block_indent,
            owner_spec.grammar_role(ImplRole::IndentedStatement),
            committed,
        );
        return;
    }
    committed.emit_trivia(&trivia);
    let ambient_scope = committed.probe(|probe| {
        probe
            .input()
            .local
            .push_inline_canonical_statement_ambient_scope(
                crate::session::InlineStatementOwnerKind::ImplColonBody,
            )
    });
    let statement_committed = if commit_canonical_statement(table, LeadingTrivia::None, committed) {
        true
    } else {
        match impl_body_error_retry(table, owner_spec, committed) {
            Some(true) => commit_canonical_statement(table, LeadingTrivia::None, committed),
            Some(false) => false,
            None => {
                emit_impl_tail_body_missing(owner_spec, committed);
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

pub(super) fn impl_body_starter_pending<E>(i: &mut SynIn<E>) -> bool
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

pub(super) fn impl_body_boundary_pending<E>(i: &mut SynIn<E>) -> bool
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let checkpoint = i.checkpoint();
    let pending = i.run(scan_punctuation).is_some_and(|punctuation| {
        matches!(
            punctuation.kind(),
            PunctuationKind::Comma
                | PunctuationKind::Close(
                    Delimiter::Parenthesis | Delimiter::Bracket | Delimiter::Brace
                )
                | PunctuationKind::Open(Delimiter::Brace)
                | PunctuationKind::Colon
                | PunctuationKind::Semicolon
        )
    });
    i.rollback(checkpoint);
    pending
}

/// Consumes one malformed body-starter run until an actual Impl starter or a
/// caller-owned boundary.  The AST path consumes the same bytes without
/// emitting; direct CST realizes the one typed error record below.
pub(super) fn impl_body_introducer_error_retry_ast<'source, E>(
    i: &mut SynIn<'_, 'source, '_, E>,
) -> Option<bool>
where
    E: ErrorSink<usize>,
    Unexpected<char>: Into<E::Error>,
    UnexpectedEndOfInput: Into<E::Error>,
{
    let start = i.pos();
    loop {
        if impl_body_starter_pending(i) {
            return (start < i.pos()).then_some(true);
        }
        if impl_body_boundary_pending(i) {
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

pub(super) fn impl_body_error_retry_ast<'source, E>(
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
        if impl_body_boundary_pending(i) {
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

pub(super) fn impl_body_introducer_error_retry<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
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
            if impl_body_starter_pending(i) {
                return (start < i.pos()).then_some((start..i.pos(), true));
            }
            if impl_body_boundary_pending(i) {
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
    })?;
    emit_impl_tail_error(
        owner_spec,
        committed,
        ImplRole::BodyIntroducer,
        ExpectedSyntax::Punctuation(crate::session::PunctuationEvidence::Colon),
        recovered.0,
    );
    Some(recovered.1)
}

pub(super) fn impl_body_error_retry<'parse, 'source, 'local, E, O>(
    table: &crate::operator::OperatorTable,
    owner_spec: ImplTailOwnerSpec,
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
                if impl_body_boundary_pending(i) {
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
    emit_impl_tail_error(
        owner_spec,
        committed,
        ImplRole::Body,
        ExpectedSyntax::Statement,
        recovered.0,
    );
    Some(recovered.1)
}

/// Emits the one outer-body recovery owned by an accepted Impl tail. The AST
/// path represents the same terminal slot as `ImplBody::Incomplete`; direct
/// CST additionally materializes the owner-mapped missing recovery node.
pub(super) fn emit_impl_tail_body_introducer_missing<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = owner_spec.grammar_role(ImplRole::BodyIntroducer);
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

pub(super) fn emit_impl_tail_body_missing<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    emit_impl_tail_missing(
        owner_spec,
        committed,
        ImplRole::Body,
        ExpectedSyntax::Statement,
    );
}

pub(super) fn emit_impl_tail_missing<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    role: ImplRole,
    expected: ExpectedSyntax,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let at = i.pos();
        let role = owner_spec.grammar_role(role);
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

pub(super) fn emit_impl_tail_error<'parse, 'source, 'local, E, O>(
    owner_spec: ImplTailOwnerSpec,
    committed: &mut Committed<'parse, 'source, 'local, E, O>,
    impl_role: ImplRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
) where
    E: ErrorSink<usize>,
    O: CommitOutput<'source>,
{
    let record = committed.probe(|probe| {
        let i = probe.input();
        let role = owner_spec.grammar_role(impl_role);
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
