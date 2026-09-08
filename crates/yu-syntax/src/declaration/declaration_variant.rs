//! Shared direct declaration-variant sequence and payload construction.

use crate::ambient_claim::AmbientClaimContext;
#[cfg(test)]
use crate::ambient_claim::AmbientClaimView;
use reborrow_generic::Reborrow as _;
use std::{cell::Cell, ops::Range, sync::Arc};

use crate::{
    recovery_record::{
        ConstructRole, DeclarationRole, Delimiter, EnumDeclarationRole, ErrorDeclarationRole,
        ExpectationSources, ExpectedSyntax, GrammarRole, PunctuationEvidence, RecoveryKind,
        RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
        VariantDeclarationRole,
    },
    syntax_kind::SyntaxKind,
};

use crate::{
    cst_output::{
        RecoveryDraft,
        emit::{
            emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind,
        },
    },
    cursor::{LexIn, SyntaxIn},
    declaration::fields::{
        DeclarationFieldRoles, FieldList, FieldOuterClose, declaration_fields_normalized,
    },
    handoff::{Either, NormalizedExit, complete, handoff},
    lexical::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, LeadingTrivia, TokenKind},
        lexer::{
            introduced_body_indentation_normalized, scan_exact_pipe, scan_identifier,
            scan_type_payload,
        },
        observation::{
            delimited_baseline, indentation_after_newline, is_active_stop_lex, token_kind,
        },
        position::{advanced_origin, suffix_marker},
        stops::{STOP_WITH, Stops},
        yumark::FenceBoundary,
    },
    type_expr::{
        TypeMlContext, TypeOuterBoundary, required_variant_payload_type_normalized_with_ambient,
    },
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum VariantOwner {
    Enum,
    Error,
}

impl VariantOwner {
    fn role(self, slot: VariantDeclarationRole) -> GrammarRole {
        GrammarRole::Declaration(match self {
            Self::Enum => DeclarationRole::Enum(EnumDeclarationRole::Variant(slot)),
            Self::Error => DeclarationRole::Error(ErrorDeclarationRole::Variant(slot)),
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum VariantSequenceForm {
    Braced,
    ColonIndented,
    EqualsInline,
    EqualsIndented,
}

impl VariantSequenceForm {
    fn introducer(self) -> TokenKind {
        match self {
            Self::Braced => TokenKind::LBrace,
            Self::ColonIndented => TokenKind::Colon,
            Self::EqualsInline | Self::EqualsIndented => TokenKind::Equals,
        }
    }

    fn matching_close(self) -> Option<TokenKind> {
        (self == Self::Braced).then_some(TokenKind::RBrace)
    }

    fn allows_pipe(self) -> bool {
        self != Self::Braced
    }

    fn allows_comma(self) -> bool {
        self != Self::EqualsInline
    }

    fn allows_empty(self) -> bool {
        self == Self::Braced
    }
}

/// Build one already-selected declaration variant body.  The declaration
/// shell owns selection; this owner consumes only the supplied introducer,
/// local separators, variants, payload delimiters, and a matching braced
/// close.
#[allow(clippy::too_many_arguments)]
pub(crate) fn declaration_variant_sequence_normalized(
    mut i: SyntaxIn,
    owner: VariantOwner,
    form: VariantSequenceForm,
    introducer: Item,
    yield_with: bool,
    declaration_baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    debug_assert_eq!(token_kind(&introducer), Some(form.introducer()));
    emit_token_item(&mut i, introducer);

    let sequence_baseline = match form {
        VariantSequenceForm::ColonIndented | VariantSequenceForm::EqualsIndented => {
            let Some(indentation) =
                introduced_body_indentation_normalized(i.rb(), item_origin, fence)
            else {
                let (mut item, origin, line_entry) =
                    variant_item_normalized(i.rb(), item_origin, line_entry, fence);
                if item.payload_view().is_eof() {
                    item.emit_eof_leading(&mut *i.state);
                }
                emit_missing_variant(&mut i, owner, &item, origin);
                return complete(handoff(item), line_entry);
            };
            if indentation <= declaration_baseline {
                let (mut item, origin, line_entry) =
                    variant_item_normalized(i.rb(), item_origin, line_entry, fence);
                if item.payload_view().is_eof() {
                    item.emit_eof_leading(&mut *i.state);
                }
                emit_missing_variant(&mut i, owner, &item, origin);
                return complete(handoff(item), line_entry);
            }
            indentation
        }
        VariantSequenceForm::Braced | VariantSequenceForm::EqualsInline => declaration_baseline,
    };

    let (item, item_origin, line_entry) =
        variant_item_normalized(i.rb(), item_origin, line_entry, fence);
    let sequence_baseline = if form == VariantSequenceForm::Braced {
        delimited_baseline(sequence_baseline, item.leading_view())
    } else {
        sequence_baseline
    };
    drive_variant_sequence(
        i,
        owner,
        form,
        item,
        yield_with,
        sequence_baseline,
        stops,
        item_origin,
        line_entry,
        fence,
        ambient,
    )
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Slot {
    Initial,
    Required,
    AfterVariant,
}

#[allow(clippy::too_many_arguments)]
fn drive_variant_sequence(
    mut i: SyntaxIn,
    owner: VariantOwner,
    form: VariantSequenceForm,
    mut item: Item,
    yield_with: bool,
    sequence_baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> NormalizedExit {
    let mut slot = Slot::Initial;
    let mut accepted_leading_pipe = false;
    let mut implicit_boundary = false;

    loop {
        if item.payload_view().is_boundary() {
            finish_incomplete_sequence(&mut i, owner, form, slot, &item, item_origin);
            return complete(handoff(item), line_entry);
        }

        if let Some(close) = form.matching_close()
            && token_kind(&item) == Some(close)
        {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }

        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
            finish_incomplete_sequence(&mut i, owner, form, slot, &item, item_origin);
            return complete(handoff(item), line_entry);
        }

        if i.token(|lex| Some(sequence_ends(lex, form, &item, sequence_baseline, stops)))
            .unwrap()
        {
            finish_incomplete_sequence(&mut i, owner, form, slot, &item, item_origin);
            return complete(handoff(item), line_entry);
        }

        if yields_with(form, yield_with, &item, sequence_baseline) {
            if slot == Slot::Initial {
                emit_missing_variant(&mut i, owner, &item, item_origin);
            }
            return complete(handoff(item), line_entry);
        }

        if slot == Slot::AfterVariant && is_implicit_separator(form, &item, sequence_baseline) {
            item.emit_all_remaining_leading(&mut *i.state);
            slot = Slot::Required;
            implicit_boundary = true;
        }

        let kind = token_kind(&item);
        let explicit_pipe = kind == Some(TokenKind::Pipe) && form.allows_pipe();
        let explicit_comma = kind == Some(TokenKind::Comma) && form.allows_comma();
        if explicit_pipe || explicit_comma {
            item.emit_all_remaining_leading(&mut *i.state);
            let leading_pipe = explicit_pipe && slot == Slot::Initial && !accepted_leading_pipe;
            if slot == Slot::Required && !implicit_boundary
                || slot == Slot::Initial && !leading_pipe
            {
                emit_missing_variant(&mut i, owner, &item, item_origin);
            }
            emit_token_item(&mut i, item);
            accepted_leading_pipe |= leading_pipe;
            implicit_boundary = false;
            (item, item_origin, line_entry) =
                variant_item_normalized(i.rb(), item_origin, line_entry, fence);
            slot = Slot::Required;
            continue;
        }

        if slot == Slot::AfterVariant {
            missing(
                i.rb(),
                &item,
                item_origin,
                owner.role(VariantDeclarationRole::Separator),
            );
        }

        let parsed = parse_variant(
            i.rb(),
            owner,
            item,
            form,
            yield_with,
            sequence_baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        item = parsed.item;
        item_origin = parsed.item_origin;
        line_entry = parsed.line_entry;
        slot = Slot::AfterVariant;
        implicit_boundary = false;
    }
}

fn finish_incomplete_sequence(
    i: &mut SyntaxIn,
    owner: VariantOwner,
    form: VariantSequenceForm,
    slot: Slot,
    item: &Item,
    origin: usize,
) {
    if slot == Slot::Initial && !form.allows_empty() {
        emit_missing_variant(i, owner, item, origin);
    }
    if form.matching_close().is_some() {
        missing(
            i.rb(),
            item,
            origin,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::EnumBracedVariantBody,
                delimiter: Delimiter::Brace,
            },
        );
    }
}

fn emit_missing_variant(i: &mut SyntaxIn, owner: VariantOwner, item: &Item, origin: usize) {
    i.state.start_node(SyntaxKind::EnumVariant.into());
    missing(
        i.rb(),
        item,
        origin,
        owner.role(VariantDeclarationRole::Item),
    );
    i.state.finish_node();
}

fn sequence_ends(
    i: LexIn,
    form: VariantSequenceForm,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> bool {
    if is_active_stop_lex(i, item, stops) {
        return true;
    }
    if stops & STOP_WITH != 0 && is_exact_with(item) {
        return true;
    }
    if matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    ) {
        return true;
    }
    match form {
        VariantSequenceForm::EqualsInline => indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation <= baseline),
        VariantSequenceForm::ColonIndented | VariantSequenceForm::EqualsIndented => {
            indentation_after_newline(item.leading_view())
                .is_some_and(|indentation| indentation < baseline)
        }
        VariantSequenceForm::Braced => false,
    }
}

fn is_implicit_separator(form: VariantSequenceForm, item: &Item, baseline: usize) -> bool {
    match form {
        VariantSequenceForm::Braced => indentation_after_newline(item.leading_view())
            .is_some_and(|indentation| indentation <= baseline),
        VariantSequenceForm::ColonIndented | VariantSequenceForm::EqualsIndented => {
            indentation_after_newline(item.leading_view()) == Some(baseline)
        }
        VariantSequenceForm::EqualsInline => false,
    }
}

struct ParsedVariant {
    item: Item,
    item_origin: usize,
    line_entry: LineEntry,
}

#[allow(clippy::too_many_arguments)]
fn parse_variant(
    mut i: SyntaxIn,
    owner: VariantOwner,
    mut item: Item,
    form: VariantSequenceForm,
    yield_with: bool,
    sequence_baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> ParsedVariant {
    i.state.start_node(SyntaxKind::EnumVariant.into());
    item.emit_all_remaining_leading(&mut *i.state);
    if is_raw_variant_name(&item) {
        emit_token_item(&mut i, item);
    } else {
        let role = Cell::new(VariantDeclarationRole::Item);
        let (next, origin, line, retry) = emit_recovery_error_run(
            i.rb(),
            |run| {
                let start = item.extent(item_origin).recovery_range().start;
                loop {
                    let kind =
                        token_syntax_kind(token_kind(&item).expect("variant Error is lexical"));
                    let extent = run.emit_item_as(item, item_origin, kind);
                    (item, item_origin, line_entry) = run
                        .lexical(|lex| variant_item_lexical(lex, item_origin, line_entry, fence));
                    let protected = item.payload_view().is_boundary()
                        || item.payload_view().is_eof()
                        || run.lexical(|lex| {
                            is_variant_boundary(
                                lex,
                                form,
                                yield_with,
                                &item,
                                sequence_baseline,
                                stops,
                            )
                        });
                    let retry = !protected && is_raw_variant_name(&item);
                    if protected || retry {
                        if retry {
                            role.set(VariantDeclarationRole::Name);
                        }
                        run.append_unexpected(UnexpectedSyntax::Token {
                            range: start..extent.recovery_range().end,
                            category: UnexpectedCategory::OtherCharacter,
                        });
                        return (item, item_origin, line_entry, retry);
                    }
                }
            },
            |range, unexpected| {
                draft(
                    owner.role(role.get()),
                    RecoveryKind::Error,
                    range,
                    unexpected,
                )
            },
        );
        item = next;
        item_origin = origin;
        line_entry = line;
        if !retry {
            i.state.finish_node();
            return ParsedVariant {
                item,
                item_origin,
                line_entry,
            };
        }
        emit_token_item(&mut i, item);
    }

    (item, item_origin, line_entry) =
        variant_item_normalized(i.rb(), item_origin, line_entry, fence);

    if is_contextual_from(&item) {
        item.emit_all_remaining_leading(&mut *i.state);
        item.emit_remaining(&mut *i.state, SyntaxKind::FromKw);
        (item, item_origin, line_entry) =
            variant_item_normalized(i.rb(), item_origin, line_entry, fence);
        if !item.payload_view().is_boundary()
            && !yields_with(form, yield_with, &item, sequence_baseline)
        {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        let parsed = parse_payload_type(
            i.rb(),
            item,
            owner.role(VariantDeclarationRole::FromType),
            sequence_baseline,
            TypeMlContext::INACTIVE,
            form.allows_pipe(),
            yield_with && form == VariantSequenceForm::EqualsInline,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        i.state.finish_node();
        return parsed;
    }

    if !item.payload_view().is_boundary()
        && !item.payload_view().is_eof()
        && matches!(
            token_kind(&item),
            Some(TokenKind::LBrace | TokenKind::LParen)
        )
        && !is_implicit_separator(form, &item, sequence_baseline)
    {
        let list = if token_kind(&item) == Some(TokenKind::LBrace) {
            FieldList::NamedBrace
        } else {
            FieldList::Tuple
        };
        let fields = declaration_fields_normalized(
            i.rb(),
            DeclarationFieldRoles {
                field: owner.role(VariantDeclarationRole::NamedField),
                field_name: owner.role(VariantDeclarationRole::NamedFieldName),
                field_colon: owner.role(VariantDeclarationRole::NamedFieldColon),
                field_type: owner.role(if list == FieldList::Tuple {
                    VariantDeclarationRole::TupleFieldType
                } else {
                    VariantDeclarationRole::NamedFieldType
                }),
                field_separator: owner.role(VariantDeclarationRole::NamedFieldSeparator),
                close: GrammarRole::ClosingDelimiter {
                    owner: match list {
                        FieldList::NamedBrace => ConstructRole::VariantNamedPayload,
                        FieldList::Tuple => ConstructRole::VariantTuplePayload,
                    },
                    delimiter: match list {
                        FieldList::NamedBrace => Delimiter::Brace,
                        FieldList::Tuple => Delimiter::Parenthesis,
                    },
                },
            },
            item,
            sequence_baseline,
            stops,
            list,
            FieldOuterClose::Borrow,
            true,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        item_origin = fields.item_origin;
        match fields.exit {
            NormalizedExit::Complete(Ok(()), next_entry) => {
                line_entry = next_entry;
                (item, item_origin, line_entry) =
                    variant_item_normalized(i.rb(), item_origin, line_entry, fence);
            }
            NormalizedExit::Complete(Err(Either::Left(next)), next_entry) => {
                item = next;
                line_entry = next_entry;
            }
            NormalizedExit::Complete(Err(Either::Right(end)), next_entry) => {
                item = end.item;
                line_entry = next_entry;
            }
            NormalizedExit::Deferred(..) => {
                unreachable!("normalized declaration fields do not defer")
            }
        }
        i.state.finish_node();
        return ParsedVariant {
            item,
            item_origin,
            line_entry,
        };
    }

    while !yields_with(form, yield_with, &item, sequence_baseline)
        && positional_payload_candidate(form, &item, sequence_baseline)
    {
        item.emit_all_remaining_leading(&mut *i.state);
        let parsed = parse_payload_type(
            i.rb(),
            item,
            owner.role(VariantDeclarationRole::PositionalPayload),
            sequence_baseline,
            TypeMlContext::INACTIVE.enter_non_type_apply(),
            form.allows_pipe(),
            yield_with && form == VariantSequenceForm::EqualsInline,
            item_origin,
            line_entry,
            fence,
            ambient,
        );
        item = parsed.item;
        item_origin = parsed.item_origin;
        line_entry = parsed.line_entry;
    }

    i.state.finish_node();
    ParsedVariant {
        item,
        item_origin,
        line_entry,
    }
}

fn is_contextual_from(item: &Item) -> bool {
    indentation_after_newline(item.leading_view()).is_none()
        && item.payload_view().token_kind() == Some(TokenKind::Identifier)
        && item.payload_view().spelling() == Some("from")
}

fn positional_payload_candidate(form: VariantSequenceForm, item: &Item, baseline: usize) -> bool {
    if item.payload_view().is_boundary()
        || item.payload_view().is_eof()
        || token_kind(item) == Some(TokenKind::Pipe) && form.allows_pipe()
        || matches!(
            token_kind(item),
            Some(TokenKind::Comma | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
        || is_implicit_separator(form, item, baseline)
    {
        return false;
    }
    item.leading_view().has_ordinary_trivia()
        && indentation_after_newline(item.leading_view())
            .is_none_or(|indentation| indentation > baseline)
}

#[allow(clippy::too_many_arguments)]
fn parse_payload_type(
    mut i: SyntaxIn,
    primary: Item,
    missing_role: GrammarRole,
    baseline: usize,
    type_ml: TypeMlContext,
    pipe_boundary: bool,
    with_boundary: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> ParsedVariant {
    let entry = suffix_marker(i.rb());
    let (exit, _) = required_variant_payload_type_normalized_with_ambient(
        i.rb(),
        primary,
        missing_role,
        baseline,
        type_ml,
        (if pipe_boundary {
            TypeOuterBoundary::PIPE
        } else {
            TypeOuterBoundary::NONE
        })
        .with(if with_boundary {
            TypeOuterBoundary::WITH
        } else {
            TypeOuterBoundary::NONE
        }),
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => ParsedVariant {
            item,
            item_origin,
            line_entry,
        },
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => ParsedVariant {
            item: end.item,
            item_origin,
            line_entry,
        },
        NormalizedExit::Complete(Ok(()), line_entry) => {
            let (item, item_origin, line_entry) =
                variant_item_normalized(i, item_origin, line_entry, fence);
            ParsedVariant {
                item,
                item_origin,
                line_entry,
            }
        }
        NormalizedExit::Deferred(..) => unreachable!("normalized TypeExpression does not defer"),
    }
}

fn is_variant_boundary(
    i: LexIn,
    form: VariantSequenceForm,
    yield_with: bool,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> bool {
    sequence_ends(i, form, item, baseline, stops)
        || yields_with(form, yield_with, item, baseline)
        || is_implicit_separator(form, item, baseline)
        || token_kind(item) == Some(TokenKind::Pipe) && form.allows_pipe()
        || token_kind(item) == Some(TokenKind::Comma) && form.allows_comma()
}

fn yields_with(form: VariantSequenceForm, enabled: bool, item: &Item, baseline: usize) -> bool {
    enabled
        && form == VariantSequenceForm::EqualsInline
        && item.leading_view().has_ordinary_trivia()
        && indentation_after_newline(item.leading_view())
            .is_none_or(|indentation| indentation > baseline)
        && is_exact_with(item)
}

fn is_exact_with(item: &Item) -> bool {
    item.payload_view().token_kind() == Some(TokenKind::Identifier)
        && item.payload_view().spelling() == Some("with")
}

fn is_raw_variant_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

fn variant_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.token(|lex| Some(variant_item_lexical(lex, item_origin, line_entry, fence)))
        .unwrap()
}

fn variant_item_lexical(
    mut lex: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let entry_pointer = lex.remainder().as_ptr() as usize;
    let entry_length = lex.remainder().len();
    let CurrentItem {
        item,
        next_line_entry,
    } = current_item(
        lex.rb(),
        item_origin,
        line_entry,
        fence,
        |mut lex, leading, origin, fence, _| {
            if let Some(pipe) = lex.token(scan_exact_pipe) {
                return Some(AcceptedPayload {
                    payload: CurrentPayload::Token(pipe),
                    next_line_entry: LineEntry::InLine,
                });
            }
            if let Some(identifier) = lex.token(scan_identifier) {
                return Some(AcceptedPayload {
                    payload: CurrentPayload::Token(identifier),
                    next_line_entry: LineEntry::InLine,
                });
            }
            scan_type_payload(lex, leading, origin, fence)
        },
    )
    .expect("declaration variant payload scanning is total");
    let consumed = entry_length
        .checked_sub(lex.remainder().len())
        .expect("variant scan keeps a suffix");
    assert_eq!(
        entry_pointer.wrapping_add(consumed),
        lex.remainder().as_ptr() as usize
    );
    (
        item,
        item_origin
            .checked_add(consumed)
            .expect("variant coordinate fits usize"),
        next_line_entry,
    )
}

fn missing(i: SyntaxIn, item: &Item, origin: usize, role: GrammarRole) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || {
            if item.payload_view().is_eof() {
                origin
            } else {
                item.extent(origin).recovery_range().start
            }
        },
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn draft(
    role: GrammarRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        GrammarRole::ClosingDelimiter { delimiter, .. } => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        }
        GrammarRole::Declaration(
            DeclarationRole::Enum(EnumDeclarationRole::Variant(VariantDeclarationRole::Separator))
            | DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::Separator,
            )),
        ) => ExpectedSyntax::DelimitedSequenceSeparator,
        _ => ExpectedSyntax::Identifier,
    };
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        0,
    )
}

#[cfg(test)]
pub(crate) fn declaration_variant_sequence_witness(
    i: SyntaxIn,
    form: VariantSequenceForm,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    declaration_variant_owner_witness(
        i,
        VariantOwner::Enum,
        form,
        false,
        baseline,
        0,
        item_origin,
        line_entry,
        fence,
    )
}

#[cfg(test)]
#[allow(clippy::too_many_arguments)]
pub(crate) fn declaration_variant_owner_witness(
    mut i: SyntaxIn,
    owner: VariantOwner,
    form: VariantSequenceForm,
    yield_with: bool,
    baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    let (introducer, item_origin, line_entry) =
        variant_item_normalized(i.rb(), item_origin, line_entry, fence);
    (token_kind(&introducer) == Some(form.introducer())).then(|| {
        declaration_variant_sequence_normalized(
            i,
            owner,
            form,
            introducer,
            yield_with,
            baseline,
            stops,
            item_origin,
            line_entry,
            fence,
            Some(AmbientClaimView::root_statement(baseline)).into(),
        )
    })
}
