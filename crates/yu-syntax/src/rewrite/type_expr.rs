//! Standalone source-free direct TypeExpression core.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

mod delimited;
mod forall;
mod record;
mod variants;

use super::{
    RewriteIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    driver::{
        Either, NormalizedExit, TailExit, advanced_origin, complete, handoff, ordinary_exit,
        suffix_marker, token_kind,
    },
    emit::{ErrorRunOutput, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, LeadingView, TokenKind},
    lexer::{
        BalancedBracketSuffix, scan_balanced_bracket_suffix_normalized, scan_exact_pipe,
        scan_type_nud_payload, scan_type_payload,
    },
    yumark::FenceBoundary,
};

use self::{
    delimited::{TypeDelimitedOwner, type_delimited_normalized},
    forall::type_forall_normalized,
    record::{type_record_next_field_normalized, type_record_normalized},
    variants::{type_effect_row_normalized, type_polymorphic_variant_normalized},
};

#[derive(Clone, Copy)]
pub(super) enum TypeApplyBoundary {
    NamedRecord(usize),
    DeclarationNamedFields,
}

/// Contextual boundaries owned by precisely one logical TypeExpression.
///
/// This is deliberately an immediate value rather than a `Stops` bit: a
/// nested TypeExpression receives `NONE`, while a same-episode tail/retry
/// retains the caller's value.
#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub(super) struct TypeOuterBoundary(u8);

impl TypeOuterBoundary {
    pub(super) const NONE: Self = Self(0);
    pub(super) const DERIVES: Self = Self(1 << 0);
    pub(super) const VIA: Self = Self(1 << 1);
    pub(super) const WITH: Self = Self(1 << 2);
    pub(super) const IMPL: Self = Self(1 << 3);
    pub(super) const EQUALS: Self = Self(1 << 4);
    pub(super) const PIPE: Self = Self(1 << 5);
    pub(super) const STRUCT_BODY: Self = Self(1 << 6);
    pub(super) const VARIANT_BODY: Self = Self(1 << 7);

    pub(super) const fn with(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    const fn contains(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

/// Slot-local ownership adjustments for a fresh mandatory Type primary.
///
/// The policy is deliberately not propagated into accepted tails or nested
/// TypeExpression episodes.
#[derive(Clone, Copy, Default, Eq, PartialEq)]
pub(super) struct RequiredTypeFreshPrimaryPolicy {
    pub(super) owns_bare_left_brace: bool,
}

pub(super) fn type_expr(i: RewriteIn) -> Option<TailExit> {
    type_expr_normalized(i, 0, LineEntry::InLine, None).map(ordinary_exit)
}

pub(super) fn type_expr_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<NormalizedExit> {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item: primary,
        next_line_entry,
    } = i.token(|lex| {
        let current = current_item(
            lex,
            item_origin,
            line_entry,
            fence,
            |lex, leading, origin, fence, _| scan_type_nud_payload(lex, leading, origin, fence),
        )?;
        if current.item.payload_view().is_boundary()
            || current.item.payload_view().is_eof()
            || !current.item.leading_view().is_grammar_empty()
            || !is_type_nud(&current.item)
        {
            return None;
        }
        Some(current)
    })?;
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    Some(type_expr_from_nud_normalized(
        i,
        primary,
        0,
        false,
        None,
        false,
        0,
        0,
        TypeOuterBoundary::NONE,
        false,
        item_origin,
        next_line_entry,
        fence,
    ))
}

#[cfg(test)]
pub(super) fn type_expr_with_caller_stops_for_test(
    mut i: RewriteIn,
    caller_stops: Stops,
    outer_closes: u8,
    item_origin: usize,
) -> Option<(NormalizedExit, usize)> {
    let entry = suffix_marker(i.rb());
    let CurrentItem {
        item: primary,
        next_line_entry,
    } = i.token(|lex| {
        let current = current_item(
            lex,
            item_origin,
            LineEntry::InLine,
            None,
            |lex, leading, origin, fence, _| scan_type_nud_payload(lex, leading, origin, fence),
        )?;
        if current.item.payload_view().is_boundary()
            || current.item.payload_view().is_eof()
            || !current.item.leading_view().is_grammar_empty()
            || !is_type_nud(&current.item)
        {
            return None;
        }
        Some(current)
    })?;
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    let continuation_entry = suffix_marker(i.rb());
    let exit = type_expr_from_nud_normalized(
        i.rb(),
        primary,
        0,
        false,
        None,
        false,
        outer_closes,
        caller_stops,
        TypeOuterBoundary::NONE,
        false,
        item_origin,
        next_line_entry,
        None,
    );
    let successor_origin = advanced_origin(item_origin, continuation_entry, i.rb());
    Some((exit, successor_origin))
}

/// Build a mandatory TypeExpression slot already introduced by another owner.
///
/// The initial item is intentionally scanned by the Type vocabulary so this
/// module owns both a malformed type-primary Error and the retry. This entry
/// point has no caller-arrow policy; consumers that make an Arrow active must
/// own that boundary themselves.
pub(super) fn required_type_expr(i: RewriteIn, primary: Item, baseline: usize) -> TailExit {
    ordinary_exit(
        required_type_expr_inner_normalized(
            i,
            primary,
            baseline,
            None,
            false,
            0,
            0,
            TypeOuterBoundary::NONE,
            RequiredTypeFreshPrimaryPolicy::default(),
            false,
            false,
            0,
            LineEntry::InLine,
            None,
        )
        .0,
    )
}

pub(super) fn required_type_expr_with_boundary(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_closes: u8,
) -> TailExit {
    ordinary_exit(
        required_type_expr_inner_normalized(
            i,
            primary,
            baseline,
            apply_boundary,
            true,
            outer_closes,
            0,
            TypeOuterBoundary::NONE,
            RequiredTypeFreshPrimaryPolicy::default(),
            false,
            false,
            0,
            LineEntry::InLine,
            None,
        )
        .0,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn required_type_expr_with_boundary_normalized(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_closes: u8,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    required_type_expr_inner_normalized(
        i,
        primary,
        baseline,
        apply_boundary,
        true,
        outer_closes,
        0,
        TypeOuterBoundary::NONE,
        RequiredTypeFreshPrimaryPolicy::default(),
        false,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
    .0
}

pub(super) fn required_type_expr_with_caller_stops(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    caller_stops: Stops,
) -> TailExit {
    required_type_expr_with_caller_stops_and_completion(i, primary, baseline, caller_stops).0
}

pub(super) fn required_type_expr_with_caller_stops_and_completion(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    caller_stops: Stops,
) -> (TailExit, bool) {
    let (exit, primary_found) = required_type_expr_inner_normalized(
        i,
        primary,
        baseline,
        None,
        false,
        0,
        caller_stops,
        TypeOuterBoundary::NONE,
        RequiredTypeFreshPrimaryPolicy::default(),
        false,
        false,
        0,
        LineEntry::InLine,
        None,
    );
    (ordinary_exit(exit), primary_found)
}

pub(super) fn required_type_expr_with_caller_stops_and_outer_boundary(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> (TailExit, bool) {
    let (exit, primary_found) = required_type_expr_inner_normalized(
        i,
        primary,
        baseline,
        None,
        false,
        0,
        caller_stops,
        outer_boundary,
        RequiredTypeFreshPrimaryPolicy::default(),
        false,
        false,
        0,
        LineEntry::InLine,
        None,
    );
    (ordinary_exit(exit), primary_found)
}

#[allow(clippy::too_many_arguments)]
pub(super) fn required_type_expr_with_caller_stops_and_outer_boundary_normalized(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, bool) {
    required_type_expr_with_caller_stops_and_outer_boundary_and_fresh_primary_policy_normalized(
        i,
        primary,
        baseline,
        caller_stops,
        outer_boundary,
        RequiredTypeFreshPrimaryPolicy::default(),
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn required_type_expr_with_caller_stops_and_outer_boundary_and_fresh_primary_policy_normalized(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    fresh_primary_policy: RequiredTypeFreshPrimaryPolicy,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, bool) {
    required_type_expr_inner_normalized(
        i,
        primary,
        baseline,
        None,
        false,
        0,
        caller_stops,
        outer_boundary,
        fresh_primary_policy,
        false,
        false,
        item_origin,
        line_entry,
        fence,
    )
}

/// Build one declaration-variant payload TypeExpression.  `type_ml` splits
/// positional payload items while the contextual outer boundary remains
/// suspended by every nested TypeExpression episode.
#[allow(clippy::too_many_arguments)]
pub(super) fn required_variant_payload_type_normalized(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    outer_boundary: TypeOuterBoundary,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, bool) {
    required_type_expr_inner_normalized(
        i,
        primary,
        baseline,
        None,
        false,
        0,
        0,
        outer_boundary,
        RequiredTypeFreshPrimaryPolicy::default(),
        type_ml,
        true,
        item_origin,
        line_entry,
        fence,
    )
}

pub(super) fn required_type_expr_normalized(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    required_type_expr_inner_normalized(
        i,
        primary,
        baseline,
        None,
        false,
        0,
        0,
        TypeOuterBoundary::NONE,
        RequiredTypeFreshPrimaryPolicy::default(),
        false,
        false,
        item_origin,
        line_entry,
        fence,
    )
    .0
}

pub(super) fn required_type_expr_with_caller_stops_and_completion_normalized(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    caller_stops: Stops,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, bool) {
    required_type_expr_inner_normalized(
        i,
        primary,
        baseline,
        None,
        false,
        0,
        caller_stops,
        TypeOuterBoundary::NONE,
        RequiredTypeFreshPrimaryPolicy::default(),
        false,
        false,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn required_type_expr_inner_normalized(
    mut i: RewriteIn,
    mut primary: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    fresh_primary_policy: RequiredTypeFreshPrimaryPolicy,
    type_ml: bool,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (NormalizedExit, bool) {
    if primary.payload_view().is_boundary() {
        i.state.start_node(SyntaxKind::TypeExpression.into());
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return (complete(handoff(primary), line_entry), false);
    }
    if is_required_type_boundary(
        &primary,
        baseline,
        caller_stops,
        outer_boundary,
        fresh_primary_policy,
    ) {
        i.state.start_node(SyntaxKind::TypeExpression.into());
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return (complete(handoff(primary), line_entry), false);
    }
    if is_type_nud(&primary) {
        return (
            type_expr_from_nud_normalized(
                i,
                primary,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            ),
            true,
        );
    }

    i.state.start_node(SyntaxKind::Error.into());
    loop {
        emit_token_item(&mut i, primary);
        (primary, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        );
        if primary.payload_view().is_boundary() {
            i.state.finish_node();
            return (complete(handoff(primary), line_entry), false);
        }
        if is_required_type_boundary(
            &primary,
            baseline,
            caller_stops,
            outer_boundary,
            fresh_primary_policy,
        ) {
            i.state.finish_node();
            return (complete(handoff(primary), line_entry), false);
        }
        if is_type_nud(&primary) {
            i.state.finish_node();
            return (
                type_expr_from_nud_normalized(
                    i,
                    primary,
                    baseline,
                    type_ml,
                    apply_boundary,
                    outer_separators,
                    outer_closes,
                    caller_stops,
                    outer_boundary,
                    pipe_lexical,
                    item_origin,
                    line_entry,
                    fence,
                ),
                true,
            );
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn type_expr_from_nud_normalized(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if primary.payload_view().is_boundary() {
        return complete(handoff(primary), line_entry);
    }
    if token_kind(&primary) == Some(TokenKind::LBracket) {
        i.state.start_node(SyntaxKind::TypeExpression.into());
        let exit = type_leading_bracket_row_normalized(
            i.rb(),
            primary,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
        i.state.finish_node();
        return exit;
    }
    type_expr_from_primary_normalized(
        i,
        primary,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

fn type_expr_from_primary(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    ordinary_exit(type_expr_from_primary_normalized(
        i,
        primary,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        false,
        0,
        LineEntry::InLine,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
fn type_expr_from_primary_normalized(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypeExpression.into());
    let exit = type_expr_from_primary_started_normalized(
        i.rb(),
        primary,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    i.state.finish_node();
    exit
}

fn type_expr_from_primary_started(
    i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    ordinary_exit(type_expr_from_primary_started_normalized(
        i,
        primary,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        false,
        0,
        LineEntry::InLine,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
fn type_expr_from_primary_started_normalized(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    match token_kind(&primary) {
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier | TokenKind::Integer) => {
            emit_token_item(&mut i, primary);
            scan_type_tail_normalized(
                i.rb(),
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            )
        }
        Some(TokenKind::LParen) => type_group_normalized(
            i.rb(),
            primary,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        ),
        Some(TokenKind::LBrace) => type_record_normalized(
            i.rb(),
            primary,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        ),
        Some(TokenKind::Forall) => type_forall_normalized(
            i.rb(),
            primary,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        ),
        Some(TokenKind::EffectRowApostrophe) => type_effect_row_normalized(
            i.rb(),
            primary,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        ),
        Some(TokenKind::PolymorphicVariantColon) => type_polymorphic_variant_normalized(
            i.rb(),
            primary,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        ),
        _ => unreachable!("the type NUD scanner accepts only type primaries"),
    }
}

fn type_item_normalized(
    i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    type_item_with_pipe_lexical_normalized(i, item_origin, line_entry, fence, false)
}

fn type_item_with_pipe_lexical_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
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
                    if pipe_lexical && let Some(pipe) = lex.token(scan_exact_pipe) {
                        return Some(AcceptedPayload {
                            payload: CurrentPayload::Token(pipe),
                            next_line_entry: LineEntry::InLine,
                        });
                    }
                    scan_type_payload(lex, leading, origin, fence)
                },
            )
        })
        .expect("type payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

pub(super) fn type_nud_item_normalized(
    i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    type_nud_item_with_pipe_lexical_normalized(i, item_origin, line_entry, fence, false)
}

fn type_nud_item_with_pipe_lexical_normalized(
    mut i: RewriteIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
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
                    if pipe_lexical && let Some(pipe) = lex.token(scan_exact_pipe) {
                        return Some(AcceptedPayload {
                            payload: CurrentPayload::Token(pipe),
                            next_line_entry: LineEntry::InLine,
                        });
                    }
                    scan_type_nud_payload(lex, leading, origin, fence)
                },
            )
        })
        .expect("type NUD payload scanning is total");
    (
        item,
        advanced_origin(item_origin, entry, i),
        next_line_entry,
    )
}

/// Scans one total Type NUD item while a sealed malformed run owns output.
///
/// The coordinate check is the lexical counterpart of `suffix_marker` plus
/// `advanced_origin`; the sealed Error-run capability deliberately cannot
/// expose a general `RewriteIn` to its body.
fn type_nud_item_with_pipe_lexical_normalized_in_error_run(
    run: &mut ErrorRunOutput<'_, '_, '_, '_, '_, '_>,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> (Item, usize, LineEntry) {
    run.lexical(|mut lex| {
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
                if pipe_lexical && let Some(pipe) = lex.token(scan_exact_pipe) {
                    return Some(AcceptedPayload {
                        payload: CurrentPayload::Token(pipe),
                        next_line_entry: LineEntry::InLine,
                    });
                }
                scan_type_nud_payload(lex, leading, origin, fence)
            },
        )
        .expect("type NUD payload scanning is total");
        let suffix_pointer = lex.remainder().as_ptr() as usize;
        let suffix_length = lex.remainder().len();
        let consumed = entry_length
            .checked_sub(suffix_length)
            .expect("a direct Type item scan cannot lengthen its live suffix");
        assert_eq!(
            entry_pointer.wrapping_add(consumed),
            suffix_pointer,
            "a direct Type item scan keeps the input on one source suffix",
        );
        let item_origin = item_origin
            .checked_add(consumed)
            .expect("a direct Type item coordinate must fit usize");
        (item, item_origin, next_line_entry)
    })
}

fn scan_type_tail(
    i: RewriteIn,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    ordinary_exit(scan_type_tail_normalized(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        false,
        0,
        LineEntry::InLine,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
fn scan_type_tail_normalized(
    mut i: RewriteIn,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (item, item_origin, line_entry) = type_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    type_tail_normalized(
        i,
        item,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

fn type_tail(
    i: RewriteIn,
    item: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    ordinary_exit(type_tail_normalized(
        i,
        item,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        false,
        0,
        LineEntry::InLine,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
fn type_tail_normalized(
    mut i: RewriteIn,
    item: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    if item.payload_view().is_boundary() {
        return complete(handoff(item), line_entry);
    }
    if !type_chain_trivia(item.leading_view(), baseline) {
        return complete(handoff(item), line_entry);
    }
    if is_type_caller_boundary(&item, caller_stops) || is_type_outer_boundary(&item, outer_boundary)
    {
        return complete(handoff(item), line_entry);
    }
    if type_ml && !item.leading_view().is_grammar_empty() {
        return complete(handoff(item), line_entry);
    }
    match token_kind(&item) {
        Some(TokenKind::Arrow) => {
            return type_arrow_tail_normalized(
                i.rb(),
                item,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                TypeOuterBoundary::NONE,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        Some(TokenKind::LParen) if item.leading_view().is_grammar_empty() => {
            return type_call_tail_normalized(
                i.rb(),
                item,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        Some(TokenKind::PathSeparator) => {
            return type_path_tail_normalized(
                i.rb(),
                item,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        Some(TokenKind::LBracket) => {
            return type_bracket_arrow_tail_normalized(
                i.rb(),
                item,
                baseline,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        _ => {}
    }
    if match apply_boundary {
        Some(TypeApplyBoundary::NamedRecord(base)) => type_record_next_field_normalized(
            i.rb(),
            &item,
            base,
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        ),
        Some(TypeApplyBoundary::DeclarationNamedFields) => {
            super::struct_decl::named_declaration_fields_next_field_candidate(
                i.rb(),
                &item,
                item_origin,
                line_entry,
                fence,
            )
        }
        None => false,
    } {
        return complete(handoff(item), line_entry);
    }
    if !item.leading_view().is_grammar_empty() && is_type_primary(&item) {
        return type_apply_argument_normalized(
            i,
            item,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    complete(handoff(item), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn type_leading_bracket_row_normalized(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let entry = suffix_marker(i.rb());
    let exit = type_bracket_row_normalized(
        i.rb(),
        open,
        baseline,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    match exit {
        NormalizedExit::Complete(Ok(()), next_line_entry) => line_entry = next_line_entry,
        NormalizedExit::Complete(Err(Either::Right(end)), next_line_entry) => {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(Err(Either::Right(end)), next_line_entry);
        }
        NormalizedExit::Complete(Err(Either::Left(item)), next_line_entry) => {
            return complete(handoff(item), next_line_entry);
        }
        _ => unreachable!("normalized Type owners do not defer"),
    }
    let (mut head, next_origin, next_line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    loop {
        if head.payload_view().is_boundary() {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(head), line_entry);
        }
        if !type_chain_trivia(head.leading_view(), baseline)
            || is_type_caller_boundary(&head, caller_stops)
            || is_type_outer_boundary(&head, outer_boundary)
        {
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(head), line_entry);
        }
        if is_type_primary(&head) {
            head.emit_all_remaining_leading(&mut *i.state);
            return type_expr_from_primary_started_normalized(
                i,
                head,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if token_kind(&head) == Some(TokenKind::LBracket) {
            (head, item_origin, line_entry) = match retry_leading_bracket_row_head_normalized(
                i.rb(),
                head,
                item_origin,
                line_entry,
                fence,
                pipe_lexical,
            ) {
                Ok(next) => next,
                Err(exit) => return exit,
            };
            continue;
        }
        if is_type_rhs_boundary(&head) {
            head.emit_all_remaining_leading(&mut *i.state);
            emit_missing(&mut i, LeadingTrivia::default());
            return complete(handoff(head), line_entry);
        }
        head.emit_all_remaining_leading(&mut *i.state);
        return retry_leading_bracket_row_head_error_normalized(
            i,
            head,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
}

fn retry_leading_bracket_row_head_normalized(
    mut i: RewriteIn,
    head: Item,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    pipe_lexical: bool,
) -> Result<(Item, usize, LineEntry), NormalizedExit> {
    let entry = suffix_marker(i.rb());
    let Some(suffix) = i.token(|lex| {
        scan_balanced_bracket_suffix_normalized(lex, item_origin, LineEntry::InLine, fence)
    }) else {
        return Err(complete(handoff(head), line_entry));
    };
    match suffix {
        BalancedBracketSuffix::Complete(CurrentItem {
            item: suffix,
            next_line_entry,
        }) => {
            item_origin = advanced_origin(item_origin, entry, i.rb());
            i.state.start_node(SyntaxKind::Error.into());
            emit_token_item(&mut i, head);
            emit_token_item(&mut i, suffix);
            i.state.finish_node();
            Ok(type_nud_item_with_pipe_lexical_normalized(
                i,
                item_origin,
                next_line_entry,
                fence,
                pipe_lexical,
            ))
        }
        BalancedBracketSuffix::Boundary { accepted, pending } => {
            i.state.start_node(SyntaxKind::Error.into());
            emit_token_item(&mut i, head);
            if let Some(accepted) = accepted {
                emit_token_item(&mut i, accepted.item);
            }
            i.state.finish_node();
            Err(complete(handoff(pending.item), pending.next_line_entry))
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn retry_leading_bracket_row_head_error_normalized(
    mut i: RewriteIn,
    mut head: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        if head.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(head), line_entry);
        }
        emit_token_item(&mut i, head);
        (head, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        );
        if head.payload_view().is_boundary() {
            i.state.finish_node();
            return complete(handoff(head), line_entry);
        }
        if !type_chain_trivia(head.leading_view(), baseline)
            || is_type_rhs_boundary(&head)
            || is_type_caller_boundary(&head, caller_stops)
            || is_type_outer_boundary(&head, outer_boundary)
        {
            i.state.finish_node();
            return complete(handoff(head), line_entry);
        }
        if is_type_primary(&head) {
            i.state.finish_node();
            head.emit_all_remaining_leading(&mut *i.state);
            return type_expr_from_primary_started_normalized(
                i,
                head,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
        if token_kind(&head) == Some(TokenKind::LBracket) {
            i.state.finish_node();
            return complete(handoff(head), line_entry);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn type_bracket_arrow_tail_normalized(
    mut i: RewriteIn,
    mut open: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    open.emit_all_remaining_leading(&mut *i.state);
    i.state.start_node(SyntaxKind::TypeArrowTail.into());
    let entry = suffix_marker(i.rb());
    let exit = type_bracket_row_normalized(
        i.rb(),
        open,
        baseline,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    let exit = match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => type_bracket_arrow_after_row_normalized(
            i.rb(),
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        ),
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            emit_missing(&mut i, LeadingTrivia::default());
            complete(Err(Either::Right(end)), line_entry)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            complete(handoff(item), line_entry)
        }
        _ => unreachable!("normalized Type owners do not defer"),
    };
    i.state.finish_node();
    exit
}

fn type_bracket_row_normalized(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::BracketRow.into());
    emit_token_item(&mut i, open);
    let exit = type_delimited_normalized(
        i.rb(),
        TokenKind::RBracket,
        baseline,
        TypeDelimitedOwner::BracketRow,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn type_bracket_arrow_after_row_normalized(
    mut i: RewriteIn,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    let (mut arrow, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    if arrow.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(arrow), line_entry);
    }
    if !type_chain_trivia(arrow.leading_view(), baseline)
        || is_type_caller_boundary(&arrow, caller_stops)
        || is_type_outer_boundary(&arrow, outer_boundary)
    {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(arrow), line_entry);
    }
    if token_kind(&arrow) == Some(TokenKind::Arrow) {
        return type_arrow_rhs_normalized(
            i,
            arrow,
            baseline,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            TypeOuterBoundary::NONE,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if is_type_nud(&arrow) {
        arrow.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return type_expr_from_nud_normalized(
            i,
            arrow,
            baseline,
            false,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            TypeOuterBoundary::NONE,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if is_type_rhs_boundary(&arrow) {
        arrow.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
    }
    complete(handoff(arrow), line_entry)
}

#[allow(clippy::too_many_arguments)]
fn type_group_normalized(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state
        .start_node(SyntaxKind::ParenthesizedTypeGroup.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = type_delimited_normalized(
        i.rb(),
        TokenKind::RParen,
        baseline,
        TypeDelimitedOwner::ParenthesizedGroup,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_type_tail_normalized(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        exit,
        item_origin,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_call_tail_normalized(
    mut i: RewriteIn,
    open: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypeCallTail.into());
    emit_token_item(&mut i, open);
    let entry = suffix_marker(i.rb());
    let exit = type_delimited_normalized(
        i.rb(),
        TokenKind::RParen,
        baseline,
        TypeDelimitedOwner::Call,
        outer_closes,
        caller_stops,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_type_tail_normalized(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        exit,
        item_origin,
        fence,
    )
}

fn missing_type_item(mut i: RewriteIn, mut item: Item) -> Item {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_missing(&mut i, LeadingTrivia::default());
    item
}

fn missing_type_close(mut i: RewriteIn, mut item: Item) -> TailExit {
    item.emit_all_remaining_leading(&mut *i.state);
    emit_missing(&mut i, LeadingTrivia::default());
    handoff(item)
}

fn missing_bracket_row_close(mut i: RewriteIn, item: Item, baseline: usize) -> TailExit {
    if is_type_implicit_boundary(baseline, item.leading_view()) {
        emit_missing(&mut i, LeadingTrivia::default());
        return handoff(item);
    }
    missing_type_close(i, item)
}

fn type_arrow_rhs(
    i: RewriteIn,
    arrow: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    ordinary_exit(type_arrow_rhs_normalized(
        i,
        arrow,
        baseline,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        TypeOuterBoundary::NONE,
        false,
        0,
        LineEntry::InLine,
        None,
    ))
}

fn retry_type_rhs(i: RewriteIn, item: Item, baseline: usize, caller_stops: Stops) -> Item {
    retry_type_rhs_normalized(
        i,
        item,
        baseline,
        caller_stops,
        false,
        0,
        LineEntry::InLine,
        None,
    )
    .0
}

fn continue_type_tail(
    i: RewriteIn,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    exit: TailExit,
) -> TailExit {
    ordinary_exit(continue_type_tail_normalized(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        false,
        complete(exit, LineEntry::InLine),
        0,
        None,
    ))
}

#[allow(clippy::too_many_arguments)]
fn type_path_tail_normalized(
    mut i: RewriteIn,
    separator: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypePathTail.into());
    emit_token_item(&mut i, separator);
    let (mut segment, next_origin, next_line_entry) = type_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;

    if segment.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return type_tail_normalized(
            i,
            segment,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if is_type_outer_boundary(&segment, outer_boundary)
        && (segment.leading_view().has_ordinary_newline() || !is_type_path_segment(&segment))
    {
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return type_tail_normalized(
            i,
            segment,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if !type_chain_trivia(segment.leading_view(), baseline) || is_type_path_boundary(&segment) {
        segment.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        i.state.finish_node();
        return type_tail_normalized(
            i,
            segment,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if !is_type_path_segment(&segment) {
        (segment, item_origin, line_entry) = retry_type_path_segment_normalized(
            i.rb(),
            segment,
            baseline,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
        if is_type_caller_boundary(&segment, caller_stops)
            || is_type_outer_boundary(&segment, outer_boundary)
        {
            i.state.finish_node();
            return type_tail_normalized(
                i,
                segment,
                baseline,
                type_ml,
                apply_boundary,
                outer_separators,
                outer_closes,
                caller_stops,
                outer_boundary,
                pipe_lexical,
                item_origin,
                line_entry,
                fence,
            );
        }
    }
    if !is_type_path_segment(&segment) {
        i.state.finish_node();
        return type_tail_normalized(
            i,
            segment,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    emit_token_item(&mut i, segment);
    i.state.finish_node();
    scan_type_tail_normalized(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn retry_type_path_segment_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = type_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        );
        if item.payload_view().is_boundary()
            || is_type_caller_boundary(&item, caller_stops)
            || is_type_path_segment(&item)
            || is_type_outer_boundary(&item, outer_boundary)
            || !type_chain_trivia(item.leading_view(), baseline)
            || is_type_path_boundary(&item)
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn type_apply_argument_normalized(
    mut i: RewriteIn,
    mut argument: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypeApplyArgument.into());
    argument.emit_all_remaining_leading(&mut *i.state);
    let entry = suffix_marker(i.rb());
    let exit = type_expr_from_nud_normalized(
        i.rb(),
        argument,
        baseline,
        true,
        None,
        outer_separators,
        outer_closes,
        caller_stops,
        TypeOuterBoundary::NONE,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    let item_origin = advanced_origin(item_origin, entry, i.rb());
    i.state.finish_node();
    continue_type_tail_normalized(
        i,
        baseline,
        false,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        exit,
        item_origin,
        fence,
    )
}

#[allow(clippy::too_many_arguments)]
fn type_arrow_tail_normalized(
    mut i: RewriteIn,
    arrow: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    i.state.start_node(SyntaxKind::TypeArrowTail.into());
    let exit = type_arrow_rhs_normalized(
        i.rb(),
        arrow,
        baseline,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    );
    i.state.finish_node();
    exit
}

#[allow(clippy::too_many_arguments)]
fn type_arrow_rhs_normalized(
    mut i: RewriteIn,
    arrow: Item,
    baseline: usize,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    emit_token_item(&mut i, arrow);
    let (mut rhs, next_origin, next_line_entry) = type_nud_item_with_pipe_lexical_normalized(
        i.rb(),
        item_origin,
        line_entry,
        fence,
        pipe_lexical,
    );
    item_origin = next_origin;
    line_entry = next_line_entry;
    if rhs.payload_view().is_boundary() {
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(rhs), line_entry);
    }
    if !type_chain_trivia(rhs.leading_view(), baseline)
        || is_type_rhs_boundary(&rhs)
        || is_type_caller_boundary(&rhs, caller_stops)
    {
        rhs.emit_all_remaining_leading(&mut *i.state);
        emit_missing(&mut i, LeadingTrivia::default());
        return complete(handoff(rhs), line_entry);
    }
    if !is_type_nud(&rhs) {
        (rhs, item_origin, line_entry) = retry_type_rhs_normalized(
            i.rb(),
            rhs,
            baseline,
            caller_stops,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        );
    }
    if is_type_caller_boundary(&rhs, caller_stops) || !is_type_nud(&rhs) {
        return complete(handoff(rhs), line_entry);
    }
    type_expr_from_nud_normalized(
        i,
        rhs,
        baseline,
        false,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        pipe_lexical,
        item_origin,
        line_entry,
        fence,
    )
}

fn retry_type_rhs_normalized(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    caller_stops: Stops,
    pipe_lexical: bool,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        if item.payload_view().is_boundary() {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
        emit_token_item(&mut i, item);
        (item, item_origin, line_entry) = type_nud_item_with_pipe_lexical_normalized(
            i.rb(),
            item_origin,
            line_entry,
            fence,
            pipe_lexical,
        );
        if item.payload_view().is_boundary()
            || is_type_nud(&item)
            || !type_chain_trivia(item.leading_view(), baseline)
            || is_type_rhs_boundary(&item)
            || is_type_caller_boundary(&item, caller_stops)
        {
            i.state.finish_node();
            return (item, item_origin, line_entry);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn continue_type_tail_normalized(
    i: RewriteIn,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    pipe_lexical: bool,
    exit: NormalizedExit,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> NormalizedExit {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => scan_type_tail_normalized(
            i,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        ),
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => type_tail_normalized(
            i,
            item,
            baseline,
            type_ml,
            apply_boundary,
            outer_separators,
            outer_closes,
            caller_stops,
            outer_boundary,
            pipe_lexical,
            item_origin,
            line_entry,
            fence,
        ),
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            complete(Err(Either::Right(end)), line_entry)
        }
        _ => unreachable!("normalized Type owners do not defer"),
    }
}

fn is_type_primary(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(
            TokenKind::Identifier
                | TokenKind::SigilIdentifier
                | TokenKind::Integer
                | TokenKind::LParen
                | TokenKind::LBrace
                | TokenKind::Forall
                | TokenKind::EffectRowApostrophe
                | TokenKind::PolymorphicVariantColon
        )
    )
}

pub(super) fn is_type_nud(item: &Item) -> bool {
    is_type_primary(item) || token_kind(item) == Some(TokenKind::LBracket)
}

fn is_type_record_field_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

fn is_type_record_field_start(item: &Item) -> bool {
    is_type_record_field_name(item) || token_kind(item) == Some(TokenKind::Colon)
}

fn is_type_polymorphic_variant_tag_name(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

fn is_forall_binder(item: &Item) -> bool {
    item.payload_view().token_kind() == Some(TokenKind::SigilIdentifier)
        && item
            .payload_view()
            .spelling()
            .is_some_and(|text| text.starts_with('\''))
}

fn is_type_path_segment(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Identifier | TokenKind::SigilIdentifier)
    )
}

fn is_type_path_boundary(item: &Item) -> bool {
    item.payload_view().is_eof()
        || is_type_separator(item)
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Arrow
                    | TokenKind::LParen
                    | TokenKind::RParen
                    | TokenKind::PathSeparator
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
}

fn is_type_rhs_boundary(item: &Item) -> bool {
    item.payload_view().is_eof()
        || is_type_separator(item)
        || matches!(
            token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
}

fn is_required_type_boundary(
    item: &Item,
    baseline: usize,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
    fresh_primary_policy: RequiredTypeFreshPrimaryPolicy,
) -> bool {
    let owns_fresh_left_brace =
        fresh_primary_policy.owns_bare_left_brace && token_kind(item) == Some(TokenKind::LBrace);
    !type_chain_trivia(item.leading_view(), baseline)
        || is_type_rhs_boundary(item)
        || token_kind(item) == Some(TokenKind::Equals)
        || (!owns_fresh_left_brace && is_type_caller_boundary(item, caller_stops))
        || (!owns_fresh_left_brace && is_fresh_type_outer_boundary(item, outer_boundary))
}

fn is_fresh_type_outer_boundary(item: &Item, outer_boundary: TypeOuterBoundary) -> bool {
    if outer_boundary.contains(TypeOuterBoundary::STRUCT_BODY) {
        match token_kind(item) {
            Some(TokenKind::LBrace | TokenKind::Colon | TokenKind::Semicolon) => return true,
            Some(TokenKind::LParen) => return false,
            _ => {}
        }
    }
    if outer_boundary.contains(TypeOuterBoundary::VARIANT_BODY)
        && matches!(
            token_kind(item),
            Some(TokenKind::LBrace | TokenKind::Colon | TokenKind::Semicolon)
        )
    {
        return true;
    }
    is_type_outer_boundary(item, outer_boundary)
}

fn is_type_record_field_boundary(item: &Item) -> bool {
    item.payload_view().is_eof()
        || is_type_separator(item)
        || matches!(
            token_kind(item),
            Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
}

fn is_type_mismatched_close(item: &Item, expected: TokenKind) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
    ) && token_kind(item) != Some(expected)
}

pub(super) fn with_type_outer_close(outer_closes: u8, close: TokenKind) -> u8 {
    outer_closes | type_close_bit(close)
}

pub(super) fn is_type_outer_close(item: &Item, outer_closes: u8) -> bool {
    token_kind(item).is_some_and(|kind| outer_closes & type_close_bit(kind) != 0)
}

fn type_close_bit(kind: TokenKind) -> u8 {
    // A child returns the same pending close for its caller to decide, so
    // spelling membership is enough; a delimiter stack is not needed here.
    match kind {
        TokenKind::RParen => 1,
        TokenKind::RBracket => 2,
        TokenKind::RBrace => 4,
        _ => 0,
    }
}

pub(super) fn is_type_caller_boundary(item: &Item, caller_stops: Stops) -> bool {
    if token_kind(item).is_some_and(|kind| super::operator::active_stop_item(kind, caller_stops)) {
        return true;
    }
    if item.payload_view().token_kind() != Some(TokenKind::Identifier) {
        return false;
    }
    let text = item.payload_view().spelling();
    (caller_stops & super::operator::STOP_WITH != 0 && text == Some("with"))
        || (caller_stops & super::operator::STOP_IN != 0 && text == Some("in"))
        || (caller_stops & super::operator::STOP_ELSIF != 0 && text == Some("elsif"))
        || (caller_stops & super::operator::STOP_ELSE != 0 && text == Some("else"))
}

fn is_type_outer_boundary(item: &Item, outer_boundary: TypeOuterBoundary) -> bool {
    if outer_boundary.contains(TypeOuterBoundary::STRUCT_BODY)
        && matches!(
            token_kind(item),
            Some(TokenKind::LBrace | TokenKind::LParen | TokenKind::Colon | TokenKind::Semicolon)
        )
    {
        return true;
    }
    if outer_boundary.contains(TypeOuterBoundary::VARIANT_BODY)
        && matches!(
            token_kind(item),
            Some(TokenKind::LBrace | TokenKind::Colon | TokenKind::Semicolon)
        )
    {
        return true;
    }
    if token_kind(item) == Some(TokenKind::Pipe) {
        return outer_boundary.contains(TypeOuterBoundary::PIPE);
    }
    if token_kind(item) == Some(TokenKind::Equals) {
        return outer_boundary.contains(TypeOuterBoundary::EQUALS);
    }
    if item.payload_view().token_kind() != Some(TokenKind::Identifier) {
        return false;
    }
    match item.payload_view().spelling() {
        Some("derives") => outer_boundary.contains(TypeOuterBoundary::DERIVES),
        Some("via") => outer_boundary.contains(TypeOuterBoundary::VIA),
        Some("with") => outer_boundary.contains(TypeOuterBoundary::WITH),
        Some("impl") => outer_boundary.contains(TypeOuterBoundary::IMPL),
        _ => false,
    }
}

fn is_type_separator(item: &Item) -> bool {
    matches!(
        token_kind(item),
        Some(TokenKind::Comma | TokenKind::Semicolon)
    )
}

fn type_chain_trivia(leading: LeadingView<'_>, baseline: usize) -> bool {
    indentation_after_newline(leading).is_none_or(|indentation| indentation > baseline)
}

fn is_type_implicit_boundary(baseline: usize, leading: LeadingView<'_>) -> bool {
    indentation_after_newline(leading).is_some_and(|indentation| indentation <= baseline)
}

fn is_type_deeper_newline(baseline: usize, leading: LeadingView<'_>) -> bool {
    indentation_after_newline(leading).is_some_and(|indentation| indentation > baseline)
}

fn is_type_payload_boundary(leading: LeadingView<'_>) -> bool {
    !leading.is_grammar_empty() && indentation_after_newline(leading).is_none()
}

fn type_delimited_baseline(incoming: usize, opening: LeadingView<'_>) -> usize {
    indentation_after_newline(opening)
        .filter(|&indentation| indentation > incoming)
        .unwrap_or(incoming)
}

fn indentation_after_newline(leading: LeadingView<'_>) -> Option<usize> {
    leading.indentation_after_newline()
}
