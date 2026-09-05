//! Effect-row and polymorphic-variant type primaries.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    RewriteIn, Stops,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_error_item, emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{scan_lbrace, scan_lbracket, scan_trivia, type_nud_item_after_trivia},
};
use super::{
    TypeApplyBoundary, TypeDelimitedOwner, TypeOuterBoundary, continue_type_tail,
    indentation_after_newline, is_type_caller_boundary, is_type_mismatched_close, is_type_nud,
    is_type_outer_close, is_type_payload_boundary, is_type_polymorphic_variant_tag_name,
    type_delimited, type_delimited_baseline, type_expr_from_nud, with_type_outer_close,
};

pub(super) fn type_effect_row(
    mut i: RewriteIn,
    apostrophe: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    i.state.start_node(SyntaxKind::EffectRowType.into());
    emit_token_item(&mut i, apostrophe);
    let open = i
        .token(scan_lbracket)
        .expect("the effect-row compound probe accepted an adjacent bracket");
    emit_token_item(
        &mut i,
        Item {
            leading: LeadingTrivia::default(),
            payload: Payload::Token(open),
        },
    );
    let exit = type_delimited(
        i.rb(),
        TokenKind::RBracket,
        baseline,
        TypeDelimitedOwner::Generic,
        outer_closes,
        caller_stops,
    );
    i.state.finish_node();
    continue_type_tail(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        exit,
    )
}

pub(super) fn type_polymorphic_variant(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    type_ml: bool,
    apply_boundary: Option<TypeApplyBoundary>,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
    outer_boundary: TypeOuterBoundary,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::PolymorphicVariantType.into());
    emit_token_item(&mut i, colon);
    let open = i
        .token(scan_lbrace)
        .expect("the polymorphic-variant compound probe accepted an adjacent brace");
    emit_token_item(
        &mut i,
        Item {
            leading: LeadingTrivia::default(),
            payload: Payload::Token(open),
        },
    );
    let exit = type_polymorphic_variant_tags(
        i.rb(),
        baseline,
        outer_separators,
        with_type_outer_close(outer_closes, TokenKind::RBrace),
        caller_stops,
    );
    i.state.finish_node();
    continue_type_tail(
        i,
        baseline,
        type_ml,
        apply_boundary,
        outer_separators,
        outer_closes,
        caller_stops,
        outer_boundary,
        exit,
    )
}

#[derive(Clone, Copy)]
enum TagPosition {
    Open,
    AfterTag,
    Unfilled,
    Filled,
}

fn type_polymorphic_variant_tags(
    mut i: RewriteIn,
    incoming_baseline: usize,
    outer_separators: bool,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    let mut position = TagPosition::Open;
    loop {
        if let Some(indentation) = indentation_after_newline(&item.leading) {
            if indentation > baseline {
                return type_polymorphic_variant_boundary(i, item, position);
            }
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            if matches!(position, TagPosition::AfterTag) {
                position = TagPosition::Unfilled;
            }
            continue;
        }
        if token_kind(&item) == Some(TokenKind::RBrace) {
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if is_type_caller_boundary(&item, caller_stops)
            && !is_type_polymorphic_variant_tag_name(&item)
        {
            return type_polymorphic_variant_boundary(i, item, position);
        }
        if is_type_mismatched_close(&item, TokenKind::RBrace) {
            if is_type_outer_close(&item, outer_closes) {
                return type_polymorphic_variant_boundary(i, item, position);
            }
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            emit_error_item(&mut i, item);
            let leading = scan_trivia(i.rb());
            item = type_nud_item_after_trivia(i.rb(), leading);
            continue;
        }
        if token_kind(&item) == Some(TokenKind::Comma) {
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            if !matches!(position, TagPosition::AfterTag) {
                emit_missing(&mut i, LeadingTrivia::default());
                position = TagPosition::Filled;
            } else {
                position = TagPosition::Unfilled;
            }
            emit_token_item(&mut i, item);
            let leading = scan_trivia(i.rb());
            item = type_nud_item_after_trivia(i.rb(), leading);
            continue;
        }
        if token_kind(&item) == Some(TokenKind::Semicolon) {
            if outer_separators {
                return type_polymorphic_variant_boundary(i, item, position);
            }
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            emit_error_item(&mut i, item);
            let leading = scan_trivia(i.rb());
            item = type_nud_item_after_trivia(i.rb(), leading);
            continue;
        }
        if matches!(&item.payload, Payload::Eof) {
            return type_polymorphic_variant_boundary(i, item, position);
        }
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        let exit = if is_type_polymorphic_variant_tag_name(&item) {
            type_polymorphic_variant_tag(i.rb(), item, baseline, outer_closes, caller_stops)
        } else if is_type_nud(&item) {
            type_polymorphic_variant_wrong_kind_tag(
                i.rb(),
                item,
                baseline,
                outer_closes,
                caller_stops,
            )
        } else {
            type_polymorphic_variant_malformed_tag(
                i.rb(),
                item,
                baseline,
                outer_closes,
                caller_stops,
            )
        };
        position = TagPosition::AfterTag;
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) if is_type_caller_boundary(&next, caller_stops) => {
                return type_polymorphic_variant_boundary(i, next, position);
            }
            Err(Either::Left(next)) => next,
            Err(Either::Right(end)) => end.item,
        };
    }
}

fn type_polymorphic_variant_boundary(
    mut i: RewriteIn,
    item: Item,
    position: TagPosition,
) -> TailExit {
    if matches!(position, TagPosition::Unfilled) {
        emit_missing(&mut i, LeadingTrivia::default());
    }
    emit_missing(&mut i, LeadingTrivia::default());
    handoff(item)
}

fn type_polymorphic_variant_tag(
    mut i: RewriteIn,
    name: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::PolymorphicVariantTag.into());
    let exit =
        type_polymorphic_variant_tag_after_name(i.rb(), name, baseline, outer_closes, caller_stops);
    i.state.finish_node();
    exit
}

fn type_polymorphic_variant_wrong_kind_tag(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::PolymorphicVariantTag.into());
    let exit = type_polymorphic_variant_tag_after_wrong_kind(
        i.rb(),
        primary,
        baseline,
        outer_closes,
        caller_stops,
    );
    i.state.finish_node();
    exit
}

fn type_polymorphic_variant_tag_after_name(
    mut i: RewriteIn,
    name: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    emit_token_item(&mut i, name);
    let leading = scan_trivia(i.rb());
    let item = type_nud_item_after_trivia(i.rb(), leading);
    type_polymorphic_variant_tag_payloads(i, item, baseline, outer_closes, caller_stops, false)
}

fn type_polymorphic_variant_tag_after_wrong_kind(
    mut i: RewriteIn,
    primary: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::Error.into());
    let exit = type_expr_from_nud(
        i.rb(),
        primary,
        baseline,
        true,
        None,
        true,
        outer_closes,
        caller_stops,
    );
    i.state.finish_node();
    type_polymorphic_variant_tag_payloads_after_head(i, exit, baseline, outer_closes, caller_stops)
}

fn type_polymorphic_variant_malformed_tag(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state.start_node(SyntaxKind::PolymorphicVariantTag.into());
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if !is_type_polymorphic_variant_tag_safe(&item) {
            continue;
        }
        i.state.finish_node();
        let exit = if is_type_polymorphic_variant_tag_boundary(&item) {
            handoff(item)
        } else {
            let leading = std::mem::take(&mut item.leading);
            emit_leading_trivia(&mut i, &leading);
            if is_type_polymorphic_variant_tag_name(&item) {
                type_polymorphic_variant_tag_after_name(
                    i.rb(),
                    item,
                    baseline,
                    outer_closes,
                    caller_stops,
                )
            } else {
                type_polymorphic_variant_tag_after_wrong_kind(
                    i.rb(),
                    item,
                    baseline,
                    outer_closes,
                    caller_stops,
                )
            }
        };
        i.state.finish_node();
        return exit;
    }
}

fn type_polymorphic_variant_tag_payloads_after_head(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    let item = match exit {
        Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
        Err(Either::Left(item)) if is_type_caller_boundary(&item, caller_stops) => {
            return handoff(item);
        }
        Err(Either::Left(item)) => item,
        Err(Either::Right(end)) => return handoff(end.item),
    };
    type_polymorphic_variant_tag_payloads(i, item, baseline, outer_closes, caller_stops, true)
}

fn type_polymorphic_variant_tag_payloads(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
    mut completed_payload: bool,
) -> TailExit {
    loop {
        if completed_payload && is_type_caller_boundary(&item, caller_stops) {
            return handoff(item);
        }
        if is_type_polymorphic_variant_payload_boundary(&item) {
            return handoff(item);
        }
        if is_type_nud(&item) {
            let exit = type_polymorphic_variant_payload(
                i.rb(),
                item,
                baseline,
                outer_closes,
                caller_stops,
            );
            item = match exit {
                Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
                Err(Either::Left(next)) => next,
                Err(Either::Right(end)) => return handoff(end.item),
            };
            completed_payload = true;
            continue;
        }
        if !is_type_payload_boundary(&item.leading) {
            return handoff(item);
        }
        let exit = type_polymorphic_variant_malformed_payload(
            i.rb(),
            item,
            baseline,
            outer_closes,
            caller_stops,
        );
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) if is_type_caller_boundary(&next, caller_stops) => {
                return handoff(next);
            }
            Err(Either::Left(next)) => next,
            Err(Either::Right(end)) => return handoff(end.item),
        };
    }
}

fn type_polymorphic_variant_payload(
    mut i: RewriteIn,
    mut primary: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::PolymorphicVariantPayload.into());
    let boundary = std::mem::take(&mut primary.leading);
    if boundary.0.is_empty() {
        emit_missing(&mut i, LeadingTrivia::default());
    } else {
        emit_leading_trivia(&mut i, &boundary);
    }
    let exit = type_expr_from_nud(
        i.rb(),
        primary,
        baseline,
        true,
        None,
        true,
        outer_closes,
        caller_stops,
    );
    i.state.finish_node();
    exit
}

fn type_polymorphic_variant_malformed_payload(
    mut i: RewriteIn,
    mut item: Item,
    baseline: usize,
    outer_closes: u8,
    caller_stops: Stops,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::PolymorphicVariantPayload.into());
    let boundary = std::mem::take(&mut item.leading);
    emit_leading_trivia(&mut i, &boundary);
    i.state.start_node(SyntaxKind::Error.into());
    loop {
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        emit_token_item(&mut i, item);
        let leading = scan_trivia(i.rb());
        item = type_nud_item_after_trivia(i.rb(), leading);
        if is_type_polymorphic_variant_payload_boundary(&item) {
            i.state.finish_node();
            let exit = handoff(item);
            i.state.finish_node();
            return exit;
        }
        if is_type_caller_boundary(&item, caller_stops) {
            i.state.finish_node();
            let exit = handoff(item);
            i.state.finish_node();
            return exit;
        }
        if !is_type_nud(&item) {
            continue;
        }
        i.state.finish_node();
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        let exit = type_expr_from_nud(
            i.rb(),
            item,
            baseline,
            true,
            None,
            true,
            outer_closes,
            caller_stops,
        );
        i.state.finish_node();
        return exit;
    }
}

fn is_type_polymorphic_variant_payload_boundary(item: &Item) -> bool {
    indentation_after_newline(&item.leading).is_some()
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
        || matches!(&item.payload, Payload::Eof)
}

fn is_type_polymorphic_variant_tag_safe(item: &Item) -> bool {
    is_type_polymorphic_variant_tag_boundary(item) || is_type_nud(item)
}

fn is_type_polymorphic_variant_tag_boundary(item: &Item) -> bool {
    indentation_after_newline(&item.leading).is_some()
        || matches!(
            token_kind(item),
            Some(
                TokenKind::Comma
                    | TokenKind::Semicolon
                    | TokenKind::RParen
                    | TokenKind::RBracket
                    | TokenKind::RBrace
            )
        )
        || matches!(&item.payload, Payload::Eof)
}
