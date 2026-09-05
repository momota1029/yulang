//! One transient, fence-aware lexical current-Item constructor.
//!
//! This module owns only a live lexical transaction and one Item's physical
//! leading parts.  Grammar owners receive its completed Item immediately;
//! neither the line fact nor the fence capability is retained.

use reborrow_generic::short::Rb;

use super::{
    LexIn,
    item::{ForeignSplit, Item, Payload, PendingFragments, PhysicalLeadingTrivia},
    lexer::{FencedBlockComment, scan_block_comment_fenced, scan_trivia_part},
    yumark::{FenceBoundary, FenceLineDecision, judge_fence_line},
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum LineEntry {
    PhysicalStart,
    InLine,
}

pub(super) enum CurrentPayload {
    Token(super::item::Token),
    Operator(super::item::OperatorToken),
}

pub(super) struct AcceptedPayload {
    pub(super) payload: CurrentPayload,
    pub(super) next_line_entry: LineEntry,
}

pub(super) struct CurrentItem {
    pub(super) item: Item,
    pub(super) next_line_entry: LineEntry,
}

/// Constructs exactly one current Item in one lexical transaction.
///
/// `None` is an optional lexical non-match: input and recoverable state roll
/// back with the transaction, while local leading parts and split storage are
/// dropped.  A returned boundary is instead an accepted leading-only Item.
pub(super) fn current_item<P>(
    mut i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    payload: P,
) -> Option<CurrentItem>
where
    P: FnOnce(
        LexIn,
        bool,
        usize,
        Option<&FenceBoundary>,
        &mut Option<Vec<ForeignSplit>>,
    ) -> Option<AcceptedPayload>,
{
    i.token(|lex| scan_current_item(lex, item_origin, line_entry, fence, payload))
}

fn scan_current_item<P>(
    mut i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    payload: P,
) -> Option<CurrentItem>
where
    P: FnOnce(
        LexIn,
        bool,
        usize,
        Option<&FenceBoundary>,
        &mut Option<Vec<ForeignSplit>>,
    ) -> Option<AcceptedPayload>,
{
    let source = i.remainder();
    let mut leading = PhysicalLeadingTrivia::default();
    let mut foreign = None;
    let mut has_ordinary_leading = false;

    if let Some(fence) = fence
        && line_entry == LineEntry::PhysicalStart
        && let Some(boundary) = classify_line(
            i.rb(),
            source,
            item_origin,
            fence,
            &mut leading,
            &mut foreign,
        )
    {
        return Some(boundary_item(leading, foreign, item_origin, boundary));
    }

    loop {
        if let Some(fence) = fence
            && i.remainder().starts_with("/*")
        {
            let part_origin = suffix_coordinate(source, item_origin, i.remainder());
            let comment = i.token(|comment| {
                scan_block_comment_fenced(comment, part_origin, fence, &mut foreign)
            })?;
            match comment {
                FencedBlockComment::Complete(comment) => {
                    has_ordinary_leading = true;
                    leading.push_ordinary(comment);
                    continue;
                }
                FencedBlockComment::Boundary { accepted, pending } => {
                    leading.push_ordinary(accepted);
                    return Some(boundary_item(leading, foreign, item_origin, pending));
                }
            }
        }

        let Some(trivia) = i.token(scan_trivia_part) else {
            break;
        };
        let starts_next_physical_line = trivia.has_line_feed();
        has_ordinary_leading = true;
        leading.push_ordinary(trivia);
        if starts_next_physical_line {
            if let Some(fence) = fence
                && let Some(boundary) = classify_line(
                    i.rb(),
                    source,
                    item_origin,
                    fence,
                    &mut leading,
                    &mut foreign,
                )
            {
                return Some(boundary_item(leading, foreign, item_origin, boundary));
            }
        }
    }

    if let Some(fence) = fence
        && i.remainder().is_empty()
    {
        let coordinate = suffix_coordinate(source, item_origin, i.remainder());
        let FenceLineDecision::Boundary(boundary) =
            judge_fence_line(i.remainder(), coordinate, fence)
        else {
            unreachable!("physical EOF is always a fence boundary");
        };
        return Some(boundary_item(leading, foreign, item_origin, boundary));
    }

    let payload_origin = suffix_coordinate(source, item_origin, i.remainder());
    let AcceptedPayload {
        payload,
        next_line_entry,
    } = payload(i, has_ordinary_leading, payload_origin, fence, &mut foreign)?;
    let payload = match payload {
        CurrentPayload::Token(token) => Payload::Token(token),
        CurrentPayload::Operator(operator) => Payload::Operator(operator),
    };
    let item = match fence {
        None => Item::plain(leading.into_ordinary(), payload),
        Some(_) => Item::finish(leading, payload, foreign, item_origin)
            .expect("one current Item owns ordered in-range foreign splits"),
    };
    Some(CurrentItem {
        item,
        next_line_entry,
    })
}

fn boundary_item(
    leading: PhysicalLeadingTrivia,
    foreign: Option<Vec<ForeignSplit>>,
    item_origin: usize,
    boundary: super::item::PendingBoundary,
) -> CurrentItem {
    let next_line_entry = if matches!(boundary.kind(), super::item::Boundary::EofAfterTrivia) {
        LineEntry::InLine
    } else {
        LineEntry::PhysicalStart
    };
    CurrentItem {
        item: Item::finish(leading, Payload::Boundary(boundary), foreign, item_origin)
            .expect("a pending boundary retains only accepted current-Item parts"),
        next_line_entry,
    }
}

fn classify_line(
    mut i: LexIn,
    source: &str,
    item_origin: usize,
    fence: &FenceBoundary,
    leading: &mut PhysicalLeadingTrivia,
    foreign: &mut Option<Vec<ForeignSplit>>,
) -> Option<super::item::PendingBoundary> {
    let coordinate = suffix_coordinate(source, item_origin, i.remainder());
    match judge_fence_line(i.remainder(), coordinate, fence) {
        FenceLineDecision::Boundary(boundary) => Some(boundary),
        FenceLineDecision::Body { prefix: None, .. } => None,
        FenceLineDecision::Body {
            prefix: Some(prefix),
            content,
        } => {
            let length = content
                .checked_sub(coordinate)
                .expect("accepted prefix stays on its physical line");
            let (_, text) = i.rb().with_str(|prefix| consume_bytes(prefix, length));
            PendingFragments::record(
                foreign,
                ForeignSplit::quote_prefix(prefix.facts.extent.start, length),
            )
            .expect("a judged quote prefix is one ordered in-range split");
            leading.push_quote_prefix(text.into());
            None
        }
    }
}

fn consume_bytes(mut i: LexIn, length: usize) -> Option<()> {
    let mut consumed = 0usize;
    while consumed < length {
        consumed = consumed.checked_add(i.next()?.len_utf8())?;
    }
    (consumed == length).then_some(())
}

fn suffix_coordinate(source: &str, item_origin: usize, suffix: &str) -> usize {
    let consumed = source
        .len()
        .checked_sub(suffix.len())
        .expect("a current Item cannot extend its entry suffix");
    assert_eq!(source.as_ptr().wrapping_add(consumed), suffix.as_ptr());
    item_origin
        .checked_add(consumed)
        .expect("a current-Item source coordinate must fit usize")
}

#[cfg(test)]
pub(super) fn scan_identifier_item_witness(
    i: LexIn,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> Option<CurrentItem> {
    current_item(i, item_origin, line_entry, fence, |mut i, _, _, _, _| {
        let token = i.token(super::lexer::scan_identifier)?;
        Some(AcceptedPayload {
            payload: CurrentPayload::Token(token),
            next_line_entry: LineEntry::InLine,
        })
    })
}
