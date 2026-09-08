//! One direct-CST `DerivesClause`, shared by declaration attachment and
//! companion-item owners.

use super::ambient_claim::AmbientClaimContext;
use crate::session::{
    DeclarationRole, DerivesRole, ExpectationSources, ExpectedSyntax, GrammarRole, RecoveryKind,
    RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
};
use reborrow_generic::Reborrow as _;
use std::{ops::Range, sync::Arc};

use crate::syntax_kind::SyntaxKind;

use super::{
    LexIn, ParserIn, Stops,
    current_item::{AcceptedPayload, CurrentItem, CurrentPayload, LineEntry, current_item},
    driver::{
        Either, NormalizedExit, advanced_origin, indentation_after_newline, is_active_stop_lex,
        suffix_marker, token_kind,
    },
    emit::{emit_recovery_error_run, emit_recovery_missing, emit_token_item, token_syntax_kind},
    item::{Item, LeadingTrivia, TokenKind},
    lexer::{scan_identifier, scan_type_nud_payload},
    output::RecoveryDraft,
    statement::StatementLineHandoff,
    type_expr::{
        TypeOuterBoundary,
        required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient,
    },
    yumark::FenceBoundary,
};

#[allow(clippy::too_many_arguments)]
pub(super) fn derives_clause_normalized(
    mut i: ParserIn,
    keyword: Item,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    role_boundary: TypeOuterBoundary,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (Item, usize, LineEntry) {
    debug_assert!(is_word(&keyword, "derives"));
    i.state.start_node(SyntaxKind::DerivesClause.into());
    emit_contextual_keyword(&mut i, keyword, SyntaxKind::DerivesKw);

    let (mut next, mut item_origin, mut line_entry) = required_role_normalized(
        i.rb(),
        baseline,
        caller_stops,
        line_handoff,
        role_boundary,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    loop {
        if !clause_gap_continues(i.rb(), &next, baseline, caller_stops, line_handoff) {
            i.state.finish_node();
            return (next, item_origin, line_entry);
        }
        if token_kind(&next) == Some(TokenKind::Comma) {
            emit_token_item(&mut i, next);
            (next, item_origin, line_entry) = required_role_normalized(
                i.rb(),
                baseline,
                caller_stops,
                line_handoff,
                role_boundary,
                item_origin,
                line_entry,
                fence,
                ambient,
            );
            continue;
        }
        if is_word(&next, "via") {
            emit_contextual_keyword(&mut i, next, SyntaxKind::ViaKw);
            (next, item_origin, line_entry) = required_via_target_normalized(
                i.rb(),
                baseline,
                caller_stops,
                line_handoff,
                item_origin,
                line_entry,
                fence,
            );
        }
        i.state.finish_node();
        return (next, item_origin, line_entry);
    }
}

#[allow(clippy::too_many_arguments)]
fn required_role_normalized(
    mut i: ParserIn,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    role_boundary: TypeOuterBoundary,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    ambient: AmbientClaimContext<'_>,
) -> (Item, usize, LineEntry) {
    let (primary, item_origin, line_entry) =
        next_clause_item_normalized(i.rb(), item_origin, line_entry, fence, false);
    if primary.payload_view().is_eof()
        || !clause_gap_continues(i.rb(), &primary, baseline, caller_stops, line_handoff)
    {
        i.state.start_node(SyntaxKind::TypeExpression.into());
        emit_derives_missing(i.rb(), &primary, item_origin, DerivesRole::RoleReference);
        i.state.finish_node();
        return (primary, item_origin, line_entry);
    }
    let child_entry = suffix_marker(i.rb());
    let (exit, _) = required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
        i.rb(),
        primary,
        GrammarRole::Declaration(DeclarationRole::Derives(DerivesRole::RoleReference)),
        baseline,
        caller_stops,
        role_boundary,
        item_origin,
        line_entry,
        fence,
        ambient,
    );
    let item_origin = advanced_origin(item_origin, child_entry, i.rb());
    successor_after_type_normalized(i, exit, item_origin, fence)
}

#[allow(clippy::too_many_arguments)]
fn required_via_target_normalized(
    mut i: ParserIn,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
    mut item_origin: usize,
    mut line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    let (mut target, next_origin, next_entry) =
        next_clause_item_normalized(i.rb(), item_origin, line_entry, fence, true);
    item_origin = next_origin;
    line_entry = next_entry;
    if !clause_gap_continues(i.rb(), &target, baseline, caller_stops, line_handoff)
        || via_target_boundary(&target)
    {
        emit_derives_missing(i.rb(), &target, item_origin, DerivesRole::ViaTarget);
        return (target, item_origin, line_entry);
    }
    if raw_identifier(&target) {
        emit_token_item(&mut i, target);
        return next_clause_item_normalized(i, item_origin, line_entry, fence, false);
    }

    let (target, item_origin, line_entry, protected) = emit_recovery_error_run(
        i.rb(),
        |run| {
            let start = target.extent(item_origin).recovery_range().start;
            loop {
                let kind =
                    token_syntax_kind(token_kind(&target).expect("ViaTarget Error is lexical"));
                let extent = run.emit_item_as(target, item_origin, kind);
                (target, item_origin, line_entry) = run.lexical(|lex| {
                    next_clause_item_lexical(lex, item_origin, line_entry, fence, true)
                });
                let protected = via_target_boundary(&target)
                    || !run.lexical(|lex| {
                        clause_gap_continues_lexical(
                            lex,
                            &target,
                            baseline,
                            caller_stops,
                            line_handoff,
                        )
                    });
                if protected || raw_identifier(&target) {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: start..extent.recovery_range().end,
                        category: UnexpectedCategory::OtherCharacter,
                    });
                    return (target, item_origin, line_entry, protected);
                }
            }
        },
        |range, unexpected| {
            derives_recovery_draft(
                DerivesRole::ViaTarget,
                RecoveryKind::Error,
                range,
                unexpected,
            )
        },
    );
    // Protected contextual and outer-owned newline Items win over raw retry.
    if protected {
        return (target, item_origin, line_entry);
    }
    emit_token_item(&mut i, target);
    next_clause_item_normalized(i, item_origin, line_entry, fence, false)
}

/// The raw Identifier slot keeps contextual clause words pending for the
/// clause or Type owner.
fn via_target_boundary(item: &Item) -> bool {
    item.payload_view().is_boundary()
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::Equals
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
        || item.payload_view().is_eof()
        || matches!(item_word(item), Some("derives" | "via" | "with" | "impl"))
}

fn successor_after_type_normalized(
    i: ParserIn,
    exit: NormalizedExit,
    item_origin: usize,
    fence: Option<&FenceBoundary>,
) -> (Item, usize, LineEntry) {
    match exit {
        NormalizedExit::Complete(Ok(()), line_entry) => {
            next_clause_item_normalized(i, item_origin, line_entry, fence, false)
        }
        NormalizedExit::Complete(Err(Either::Left(item)), line_entry) => {
            (item, item_origin, line_entry)
        }
        NormalizedExit::Complete(Err(Either::Right(end)), line_entry) => {
            (end.item, item_origin, line_entry)
        }
        NormalizedExit::Deferred(_, _) => {
            unreachable!("normalized TypeExpression does not defer a declaration owner")
        }
    }
}

fn next_clause_item_normalized(
    mut i: ParserIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    raw_identifier_first: bool,
) -> (Item, usize, LineEntry) {
    i.token(|lex| {
        Some(next_clause_item_lexical(
            lex,
            item_origin,
            line_entry,
            fence,
            raw_identifier_first,
        ))
    })
    .expect("Derives payload scanning is total")
}

fn next_clause_item_lexical(
    mut lex: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    raw_identifier_first: bool,
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
        |mut lex: LexIn, leading, origin, fence, _| {
            if raw_identifier_first && let Some(identifier) = lex.token(scan_identifier) {
                return Some(AcceptedPayload {
                    payload: CurrentPayload::Token(identifier),
                    next_line_entry: LineEntry::InLine,
                });
            }
            scan_type_nud_payload(lex, leading, origin, fence)
        },
    )
    .expect("Derives payload scanning is total");
    let consumed = entry_length
        .checked_sub(lex.remainder().len())
        .expect("a Derives scan cannot lengthen its suffix");
    assert_eq!(
        entry_pointer.wrapping_add(consumed),
        lex.remainder().as_ptr() as usize,
        "a Derives scan keeps one source suffix"
    );
    let item_origin = item_origin
        .checked_add(consumed)
        .expect("Derives coordinate fits usize");
    (item, item_origin, next_line_entry)
}

/// This is the complete direct-C15 gap decision.  It is deliberately local:
/// `StatementLineHandoff` comes from the Type owner and is never recovered
/// from state or attached to an Item.
fn clause_gap_continues(
    mut i: ParserIn,
    item: &Item,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    i.token(|lex| {
        Some(clause_gap_continues_lexical(
            lex,
            item,
            baseline,
            caller_stops,
            line_handoff,
        ))
    })
    .expect("Derives gap observation is total")
}

fn clause_gap_continues_lexical(
    i: LexIn,
    item: &Item,
    baseline: usize,
    caller_stops: Stops,
    line_handoff: StatementLineHandoff,
) -> bool {
    if item.payload_view().is_boundary() {
        return false;
    }
    if is_active_stop_lex(i, item, caller_stops) {
        return false;
    }
    let Some(indentation) = indentation_after_newline(item.leading_view()) else {
        return true;
    };
    matches!(line_handoff, StatementLineHandoff::OrdinaryLayout) && indentation > baseline
}

fn emit_derives_missing(i: ParserIn, item: &Item, item_origin: usize, role: DerivesRole) {
    let at = item.payload_view().pending_boundary().map_or_else(
        || {
            if item.payload_view().is_eof() {
                item_origin
            } else {
                item.extent(item_origin).recovery_range().start
            }
        },
        |boundary| boundary.coordinate(),
    );
    emit_recovery_missing(i, LeadingTrivia::default(), at, |range| {
        derives_recovery_draft(role, RecoveryKind::Missing, range, Arc::from([]))
    });
}

fn derives_recovery_draft(
    role: DerivesRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let expected = match role {
        DerivesRole::RoleReference => ExpectedSyntax::TypeExpression,
        DerivesRole::ViaTarget => ExpectedSyntax::Identifier,
    };
    let role = GrammarRole::Declaration(DeclarationRole::Derives(role));
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

fn emit_contextual_keyword(i: &mut ParserIn, item: Item, kind: SyntaxKind) {
    debug_assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    item.emit_remaining(&mut *i.state, kind);
}

fn raw_identifier(item: &Item) -> bool {
    token_kind(item) == Some(TokenKind::Identifier)
}

pub(super) fn is_word(item: &Item, word: &str) -> bool {
    item.payload_view().token_kind() == Some(TokenKind::Identifier)
        && item.payload_view().spelling() == Some(word)
}

fn item_word(item: &Item) -> Option<&str> {
    (item.payload_view().token_kind() == Some(TokenKind::Identifier))
        .then(|| item.payload_view().spelling())
        .flatten()
}
