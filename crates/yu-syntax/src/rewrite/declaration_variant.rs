//! Shared direct declaration-variant sequence and payload construction.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::{
    RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    driver::{
        Either, NormalizedExit, advanced_origin, complete, delimited_baseline, handoff,
        indentation_after_newline, is_active_stop, suffix_marker, token_kind,
    },
    emit::{emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{
        introduced_body_indentation_normalized, scan_exact_pipe, scan_identifier, scan_type_payload,
    },
    struct_decl::{FieldList, FieldOuterClose, declaration_fields_normalized},
    type_expr::{TypeOuterBoundary, required_variant_payload_type_normalized},
    yumark::FenceBoundary,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum VariantSequenceForm {
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
pub(super) fn declaration_variant_sequence_normalized(
    mut i: RewriteIn,
    form: VariantSequenceForm,
    introducer: Item,
    declaration_baseline: usize,
    stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    debug_assert_eq!(token_kind(&introducer), Some(form.introducer()));
    emit_token_item(&mut i, introducer);

    let sequence_baseline = match form {
        VariantSequenceForm::ColonIndented | VariantSequenceForm::EqualsIndented => {
            let Some(indentation) =
                introduced_body_indentation_normalized(i.rb(), item_origin, fence)
            else {
                let (item, _, line_entry) =
                    variant_item_normalized(i.rb(), item_origin, line_entry, fence);
                emit_missing_variant(&mut i);
                return complete(handoff(item), line_entry);
            };
            if indentation <= declaration_baseline {
                let (item, _, line_entry) =
                    variant_item_normalized(i.rb(), item_origin, line_entry, fence);
                emit_missing_variant(&mut i);
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
        form,
        item,
        sequence_baseline,
        stops,
        item_origin,
        line_entry,
        fence,
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
    mut i: RewriteIn,
    form: VariantSequenceForm,
    mut item: Item,
    sequence_baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let mut slot = Slot::Initial;
    let mut accepted_leading_pipe = false;
    let mut implicit_boundary = false;

    loop {
        if item.payload_view().is_boundary() {
            finish_incomplete_sequence(&mut i, form, slot);
            return complete(handoff(item), line_entry);
        }

        if let Some(close) = form.matching_close()
            && token_kind(&item) == Some(close)
        {
            item.emit_all_remaining_leading(&mut *i.state);
            emit_token_item(&mut i, item);
            return complete(Ok(()), line_entry);
        }

        if sequence_ends(i.rb(), form, &item, sequence_baseline, stops) {
            finish_incomplete_sequence(&mut i, form, slot);
            return complete(handoff(item), line_entry);
        }

        if item.payload_view().is_eof() {
            item.emit_eof_leading(&mut *i.state);
            finish_incomplete_sequence(&mut i, form, slot);
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
                emit_missing_variant(&mut i);
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
            emit_missing(&mut i, LeadingTrivia::default());
        }

        let parsed = parse_variant(
            i.rb(),
            item,
            form,
            sequence_baseline,
            stops,
            item_origin,
            line_entry,
            fence,
        );
        item = parsed.item;
        item_origin = parsed.item_origin;
        line_entry = parsed.line_entry;
        slot = Slot::AfterVariant;
        implicit_boundary = false;
    }
}

fn finish_incomplete_sequence(i: &mut RewriteIn, form: VariantSequenceForm, slot: Slot) {
    if slot == Slot::Initial && !form.allows_empty() {
        emit_missing_variant(i);
    }
    if form.matching_close().is_some() {
        emit_missing(i, LeadingTrivia::default());
    }
}

fn emit_missing_variant(i: &mut RewriteIn) {
    i.state.start_node(SyntaxKind::EnumVariant.into());
    emit_missing(i, LeadingTrivia::default());
    i.state.finish_node();
}

fn sequence_ends(
    mut i: RewriteIn,
    form: VariantSequenceForm,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> bool {
    if is_active_stop(i.rb(), item, stops) {
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
    mut i: RewriteIn,
    mut item: Item,
    form: VariantSequenceForm,
    sequence_baseline: usize,
    stops: Stops,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> ParsedVariant {
    i.state.start_node(SyntaxKind::EnumVariant.into());
    item.emit_all_remaining_leading(&mut *i.state);
    if is_raw_variant_name(&item) {
        emit_token_item(&mut i, item);
    } else {
        i.state.start_node(SyntaxKind::Error.into());
        loop {
            emit_token_item(&mut i, item);
            (item, item_origin, line_entry) =
                variant_item_normalized(i.rb(), item_origin, line_entry, fence);
            if item.payload_view().is_boundary()
                || item.payload_view().is_eof()
                || is_variant_boundary(i.rb(), form, &item, sequence_baseline, stops)
            {
                i.state.finish_node();
                i.state.finish_node();
                return ParsedVariant {
                    item,
                    item_origin,
                    line_entry,
                };
            }
            if is_raw_variant_name(&item) {
                item.emit_all_remaining_leading(&mut *i.state);
                i.state.finish_node();
                emit_token_item(&mut i, item);
                break;
            }
        }
    }

    (item, item_origin, line_entry) =
        variant_item_normalized(i.rb(), item_origin, line_entry, fence);

    if is_contextual_from(&item) {
        item.emit_all_remaining_leading(&mut *i.state);
        item.emit_remaining(&mut *i.state, SyntaxKind::FromKw);
        (item, item_origin, line_entry) =
            variant_item_normalized(i.rb(), item_origin, line_entry, fence);
        if !item.payload_view().is_boundary() {
            item.emit_all_remaining_leading(&mut *i.state);
        }
        let parsed = parse_payload_type(
            i.rb(),
            item,
            sequence_baseline,
            false,
            form.allows_pipe(),
            item_origin,
            line_entry,
            fence,
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
            item,
            sequence_baseline,
            stops,
            list,
            FieldOuterClose::Borrow,
            true,
            item_origin,
            line_entry,
            fence,
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

    while positional_payload_candidate(form, &item, sequence_baseline) {
        item.emit_all_remaining_leading(&mut *i.state);
        let parsed = parse_payload_type(
            i.rb(),
            item,
            sequence_baseline,
            true,
            form.allows_pipe(),
            item_origin,
            line_entry,
            fence,
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
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    pipe_boundary: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> ParsedVariant {
    let entry = suffix_marker(i.rb());
    let (exit, _) = required_variant_payload_type_normalized(
        i.rb(),
        primary,
        baseline,
        type_ml,
        if pipe_boundary {
            TypeOuterBoundary::PIPE
        } else {
            TypeOuterBoundary::NONE
        },
        item_origin,
        line_entry,
        fence,
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
    i: RewriteIn,
    form: VariantSequenceForm,
    item: &Item,
    baseline: usize,
    stops: Stops,
) -> bool {
    sequence_ends(i, form, item, baseline, stops)
        || is_implicit_separator(form, item, baseline)
        || token_kind(item) == Some(TokenKind::Pipe) && form.allows_pipe()
        || token_kind(item) == Some(TokenKind::Comma) && form.allows_comma()
}

fn is_raw_variant_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

fn variant_item_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item,
        next_line_entry,
    } = i
        .token(|lex| {
            current_item(
                lex,
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
        })
        .expect("declaration variant payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

#[cfg(test)]
pub(super) fn declaration_variant_sequence_witness(
    mut i: RewriteIn,
    form: VariantSequenceForm,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    let (introducer, item_origin, line_entry) =
        variant_item_normalized(i.rb(), item_origin, line_entry, fence);
    (token_kind(&introducer) == Some(form.introducer())).then(|| {
        declaration_variant_sequence_normalized(
            i,
            form,
            introducer,
            baseline,
            0,
            item_origin,
            line_entry,
            fence,
        )
    })
}
