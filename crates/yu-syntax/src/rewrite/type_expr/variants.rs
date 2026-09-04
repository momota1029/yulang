//! Effect-row and polymorphic-variant type primaries.

use reborrow_generic::Reborrow as _;

use crate::syntax_kind::SyntaxKind;

use super::super::{
    RewriteIn,
    driver::{Either, TailExit, handoff, token_kind},
    emit::{emit_leading_trivia, emit_token_item},
    item::{Item, LeadingTrivia, Payload, TokenKind},
    lexer::{scan_lbrace, scan_lbracket, scan_trivia, type_nud_item_after_trivia},
};
use super::{
    TypeDelimitedOwner, continue_type_tail, is_type_implicit_boundary, is_type_nud,
    is_type_payload_boundary, is_type_polymorphic_variant_tag_name, type_delimited,
    type_delimited_baseline, type_expr_from_nud,
};

pub(super) fn type_effect_row(
    mut i: RewriteIn,
    apostrophe: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
    outer_separators: bool,
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
    );
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, record_base, outer_separators, exit)
}

pub(super) fn type_polymorphic_variant(
    mut i: RewriteIn,
    colon: Item,
    baseline: usize,
    type_ml: bool,
    record_base: Option<usize>,
    outer_separators: bool,
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
    let exit = type_polymorphic_variant_tags(i.rb(), baseline);
    i.state.finish_node();
    continue_type_tail(i, baseline, type_ml, record_base, outer_separators, exit)
}

fn type_polymorphic_variant_tags(mut i: RewriteIn, incoming_baseline: usize) -> TailExit {
    let opening = scan_trivia(i.rb());
    let baseline = type_delimited_baseline(incoming_baseline, &opening);
    emit_leading_trivia(&mut i, &opening);
    let mut item = type_nud_item_after_trivia(i.rb(), LeadingTrivia::default());
    loop {
        if token_kind(&item) == Some(TokenKind::RBrace) {
            emit_token_item(&mut i, item);
            return Ok(());
        }
        if matches!(&item.payload, Payload::Eof) || !is_type_polymorphic_variant_tag_name(&item) {
            return handoff(item);
        }
        let exit = type_polymorphic_variant_tag(i.rb(), item, baseline);
        item = match type_polymorphic_variant_successor(i.rb(), exit, baseline) {
            Ok(next) => next,
            Err(exit) => return exit,
        };
    }
}

fn type_polymorphic_variant_tag(mut i: RewriteIn, name: Item, baseline: usize) -> TailExit {
    i.state.start_node(SyntaxKind::PolymorphicVariantTag.into());
    emit_token_item(&mut i, name);
    let leading = scan_trivia(i.rb());
    let mut item = type_nud_item_after_trivia(i.rb(), leading);
    loop {
        if !is_type_payload_boundary(&item.leading) || !is_type_nud(&item) {
            i.state.finish_node();
            return handoff(item);
        }
        let exit = type_polymorphic_variant_payload(i.rb(), item, baseline);
        item = match exit {
            Ok(()) => type_nud_item_after_trivia(i.rb(), LeadingTrivia::default()),
            Err(Either::Left(next)) => next,
            Err(Either::Right(end)) => {
                i.state.finish_node();
                return Err(Either::Right(end));
            }
        };
    }
}

fn type_polymorphic_variant_payload(
    mut i: RewriteIn,
    mut primary: Item,
    baseline: usize,
) -> TailExit {
    i.state
        .start_node(SyntaxKind::PolymorphicVariantPayload.into());
    let boundary = std::mem::take(&mut primary.leading);
    emit_leading_trivia(&mut i, &boundary);
    let exit = type_expr_from_nud(i.rb(), primary, baseline, true, None, true);
    i.state.finish_node();
    exit
}

fn type_polymorphic_variant_successor(
    mut i: RewriteIn,
    exit: TailExit,
    baseline: usize,
) -> Result<Item, TailExit> {
    match exit {
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::Comma) => {
            emit_token_item(&mut i, next);
            let leading = scan_trivia(i.rb());
            let mut next = type_nud_item_after_trivia(i.rb(), leading);
            if token_kind(&next) == Some(TokenKind::RBrace)
                || is_type_polymorphic_variant_tag_name(&next)
            {
                let leading = std::mem::take(&mut next.leading);
                emit_leading_trivia(&mut i, &leading);
            }
            if token_kind(&next) == Some(TokenKind::RBrace) {
                emit_token_item(&mut i, next);
                return Err(Ok(()));
            }
            Ok(next)
        }
        Err(Either::Left(next)) if token_kind(&next) == Some(TokenKind::RBrace) => {
            emit_token_item(&mut i, next);
            Err(Ok(()))
        }
        Err(Either::Left(mut next))
            if is_type_polymorphic_variant_tag_name(&next)
                && is_type_implicit_boundary(baseline, &next.leading) =>
        {
            let leading = std::mem::take(&mut next.leading);
            emit_leading_trivia(&mut i, &leading);
            Ok(next)
        }
        exit => Err(exit),
    }
}
