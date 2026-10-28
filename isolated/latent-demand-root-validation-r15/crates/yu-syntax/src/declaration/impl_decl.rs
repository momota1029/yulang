//! Private direct standalone `impl` declaration construction.

use crate::ambient_claim::AmbientClaimContext;
#[cfg(test)]
use crate::ambient_claim::AmbientClaimView;

use crate::syntax_kind::SyntaxKind;

use crate::{
    cursor::{LexIn, SyntaxIn},
    handoff::NormalizedExit,
    lexical::{
        current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
        item::{Item, TokenKind},
        lexer::{
            scan_identifier, scan_statement_payload, scan_type_nud_payload, source_identifier,
        },
        observation::indentation_after_newline,
        stops::Stops,
        trivia::{TriviaObservation, observe_fenced_trivia},
        yumark::FenceBoundary,
    },
    statement::StatementLineHandoff,
};

#[allow(clippy::too_many_arguments)]
#[cfg(test)]
pub(crate) fn impl_declaration_witness(
    mut i: SyntaxIn,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    if !impl_source_selected_normalized(i.rb(), baseline, item_origin, line_entry, fence) {
        return None;
    }
    let (intro, item_origin, line_entry) = impl_item_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        baseline,
        stops,
        true,
        false,
    );
    impl_declaration_selected_normalized(i.rb(), &intro, baseline, item_origin, fence).then(|| {
        impl_declaration_normalized(
            i,
            intro,
            baseline,
            stops,
            line_handoff,
            item_origin,
            line_entry,
            fence,
            Some(AmbientClaimView::root_statement(baseline)).into(),
            Some(crate::sequence::SequenceOwner::RootStatement),
        )
    })
}

#[cfg(test)]
fn impl_source_selected_normalized(
    i: SyntaxIn,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            let source = lex.remainder();
            let TriviaObservation::Visible(observed) =
                observe_fenced_trivia(source, item_origin, line_entry, fence)
            else {
                return Some(false);
            };
            if observed
                .indentation
                .is_some_and(|indentation| indentation <= baseline)
            {
                return Some(false);
            }
            let Some((word, suffix)) = source_identifier(observed.source) else {
                return Some(false);
            };
            if word == "impl" {
                return Some(true);
            }
            if !matches!(word, "my" | "our" | "pub") {
                return Some(false);
            }
            let leading_len = source.len() - observed.source.len();
            Some(prefixed_impl_candidate_normalized(
                suffix,
                item_origin + leading_len + word.len(),
                fence,
                baseline,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

#[cfg(test)]
pub(crate) fn impl_declaration_selected_normalized(
    i: SyntaxIn,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    i.map(
        |lex: LexIn| {
            Some(impl_declaration_selected_lexical(
                lex.remainder(),
                item,
                baseline,
                item_origin,
                fence,
            ))
        },
        |selected| selected,
    )
    .unwrap_or(false)
}

pub(crate) fn impl_declaration_selected_lexical(
    source: &str,
    item: &Item,
    baseline: usize,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> bool {
    if item_word(item) == Some("impl") {
        return true;
    }
    if !matches!(item_word(item), Some("my" | "our" | "pub")) {
        return false;
    }
    prefixed_impl_candidate_normalized(source, item_origin, fence, baseline)
}

fn prefixed_impl_candidate_normalized(
    source: &str,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
    baseline: usize,
) -> bool {
    let TriviaObservation::Visible(observed) =
        observe_fenced_trivia(source, item_origin, LineEntry::InLine, fence)
    else {
        return false;
    };
    observed.present
        && observed
            .indentation
            .is_none_or(|indentation| indentation > baseline)
        && source_identifier(observed.source).is_some_and(|(word, _)| word == "impl")
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn impl_declaration_normalized(
    mut i: SyntaxIn,
    intro: Item,
    baseline: usize,
    stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
    sequence: crate::sequence::SequenceContext,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::ImplDeclaration.into());
    if item_word(&intro) == Some("impl") {
        emit_item_as(&mut i, intro, SyntaxKind::ImplKw);
    } else {
        emit_visibility(&mut i, intro);
        let (mut keyword, next_origin, next_entry) = impl_item_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            true,
            false,
        );
        item_origin = next_origin;
        line_entry = next_entry;
        debug_assert!(impl_gap_allowed(&keyword, baseline));
        debug_assert_eq!(item_word(&keyword), Some("impl"));
        keyword.emit_all_remaining_leading(&mut *i.state);
        emit_item_as(&mut i, keyword, SyntaxKind::ImplKw);
    }

    let exit = super::impl_tail::impl_tail_normalized(
        i.rb(),
        baseline,
        stops,
        line_handoff,
        item_origin,
        line_entry,
        fence,
        ambient,
        sequence,
    );
    i.state.finish_node();
    exit
}

pub(super) fn impl_gap_allowed(item: &Item, baseline: usize) -> bool {
    indentation_after_newline(item.leading_view()).is_none_or(|indentation| indentation > baseline)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn impl_item_normalized(
    mut i: SyntaxIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(scan_impl_item(
            lex,
            item_origin,
            line_entry,
            fence,
            baseline,
            stops,
            raw_identifier,
            type_vocabulary,
        ))
    })
    .expect("Impl Item scan is total")
}

#[allow(clippy::too_many_arguments)]
pub(super) fn scan_impl_item(
    mut i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    baseline: usize,
    stops: Stops,
    raw_identifier: bool,
    type_vocabulary: bool,
) -> (Item, usize, LineEntry) {
    let entry = i.remainder().len();
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
                    if raw_identifier && let Some(identifier) = lex.token(scan_identifier) {
                        return Some(AcceptedPayload {
                            payload: CurrentPayload::Token(identifier),
                            next_line_entry: LineEntry::InLine,
                        });
                    }
                    if type_vocabulary {
                        scan_type_nud_payload(lex, leading, origin, fence)
                    } else {
                        scan_statement_payload(lex, leading, origin, fence, baseline, stops)
                    }
                },
            )
        })
        .expect("Impl declaration payload scanning is total");
    (
        item,
        item_origin + entry - i.remainder().len(),
        next_line_entry,
    )
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}

fn emit_item_as(i: &mut SyntaxIn, item: Item, kind: SyntaxKind) {
    item.emit_remaining(&mut *i.state, kind);
}

fn emit_visibility(i: &mut SyntaxIn, item: Item) {
    let kind = match item.payload_view().spelling() {
        Some("my") => SyntaxKind::MyKw,
        Some("our") => SyntaxKind::OurKw,
        Some("pub") => SyntaxKind::PubKw,
        _ => unreachable!("Impl visibility uses exact declaration words"),
    };
    emit_item_as(i, item, kind);
}
