//! Effect-row and polymorphic-variant type primaries.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    RewriteIn,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_error_item, emit_leading_trivia, emit_missing, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{scan_lbrace, scan_lbracket, scan_trivia, type_nud_item_after_trivia},
};
use super::{
    TypeDelimitedOwner, continue_type_tail, indentation_after_newline, is_type_mismatched_close,
    is_type_nud, is_type_outer_close, is_type_payload_boundary,
    is_type_polymorphic_variant_tag_name, type_delimited, type_delimited_baseline,
    type_expr_from_nud, with_type_outer_close,
};

pub(super) fn type_effect_row(
    mut i: RewriteIn,
    apostrophe: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
    outer_separators: bool,
    outer_closes: u8,
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
    );
    i.state.finish_node();
    continue_type_tail(
        i,
        baseline,
        type_ml,
        record_base,
        outer_separators,
        outer_closes,
        exit,
    )
}

pub(super) fn type_polymorphic_variant(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
    outer_separators: bool,
    outer_closes: u8,
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
    );
    i.state.finish_node();
    continue_type_tail(
        i,
        baseline,
        type_ml,
        record_base,
        outer_separators,
        outer_closes,
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
        if !is_type_polymorphic_variant_tag_name(&item) {
            return handoff(item);
        }
        let leading = std::mem::take(&mut item.leading);
        emit_leading_trivia(&mut i, &leading);
        let exit = type_polymorphic_variant_tag(i.rb(), item, baseline, outer_closes);
        position = TagPosition::AfterTag;
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
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
) -> TailExit {
    i.state.start_node(SyntaxKind::PolymorphicVariantTag.into());
    emit_token_item(&mut i, name);
    let leading = scan_trivia(i.rb());
    let mut item = type_nud_item_after_trivia(i.rb(), leading);
    loop {
        if !is_type_payload_boundary(&item.leading) || !is_type_nud(&item) {
            i.state.finish_node();
            return handoff(item);
        }
        let exit = type_polymorphic_variant_payload(i.rb(), item, baseline, outer_closes);
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) => next,
            Err(Either::Right(end)) => {
                i.state.finish_node();
                return handoff(end.item);
            }
        };
    }
}

fn type_polymorphic_variant_payload(
    mut i: RewriteIn,
    mut primary: Item,
    baseline: usize,
    outer_closes: u8,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::PolymorphicVariantPayload.into());
    let boundary = std::mem::take(&mut primary.leading);
    emit_leading_trivia(&mut i, &boundary);
    let exit = type_expr_from_nud(i.rb(), primary, baseline, true, None, true, outer_closes);
    i.state.finish_node();
    exit
}
