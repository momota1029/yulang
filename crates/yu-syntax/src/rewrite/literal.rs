//! Isolated literal Item construction before expression or Pattern dispatch.

use reborrow_generic::Reborrow as _;

use super::{
    LexIn,
    item::{ForeignSplit, Item, LeadingTrivia, Payload, PendingFragments, Token, TokenKind},
    yumark::{FenceBoundary, FenceLineDecision, judge_fence_line},
};

#[derive(Debug, Eq, PartialEq)]
pub(super) enum LiteralPiece {
    Complete(Item),
    Boundary {
        accepted: Option<Item>,
        pending: Item,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum StringMode {
    Normal,
    Heredoc { quotes: usize },
}

/// Accepts only a complete literal opener candidate. Two adjacent quotes are
/// the opener and terminator of one normal string; three or more form one
/// heredoc opener.
pub(super) fn scan_string_opener_witness(mut i: LexIn) -> Option<(Item, StringMode)> {
    let run = quote_run(i.remainder());
    let (width, mode) = match run {
        0 => return None,
        1 | 2 => (1, StringMode::Normal),
        quotes => (quotes, StringMode::Heredoc { quotes }),
    };
    let (_, text) = i.rb().with_str(|opener| consume_exact_bytes(opener, width));
    Some((literal_token(text), mode))
}

/// Accepts the mode's terminator without partially consuming a heredoc quote
/// run of a different width.
pub(super) fn scan_string_close_witness(mut i: LexIn, mode: StringMode) -> Option<Item> {
    let run = quote_run(i.remainder());
    let width = match mode {
        StringMode::Normal => (run != 0).then_some(1)?,
        StringMode::Heredoc { quotes } => (run == quotes).then_some(quotes)?,
    };
    let (_, text) = i.rb().with_str(|close| consume_exact_bytes(close, width));
    Some(literal_token(text))
}

/// Scans one maximal nonempty StringText Item, or returns the first fence/EOF
/// boundary together with the text Item completed before it. The caller has
/// already ruled out a structural starter at the entry cursor.
pub(super) fn scan_string_text_witness(
    mut i: LexIn,
    part_origin: usize,
    fence: &FenceBoundary,
    mode: StringMode,
) -> LiteralPiece {
    let part = i.remainder();
    let mut foreign = None;
    let (pending, text) = i.rb().with_str(|mut text| {
        loop {
            let remainder = text.remainder();
            if remainder.is_empty() {
                let coordinate = checked_suffix_coordinate(part, part_origin, remainder);
                break literal_line_transition(text, coordinate, fence, &mut foreign);
            }

            if remainder.starts_with('"') {
                let run = quote_run(remainder);
                let is_close = match mode {
                    StringMode::Normal => true,
                    StringMode::Heredoc { quotes } => run == quotes,
                };
                if is_close {
                    break None;
                }
                consume_exact_bytes(text.rb(), run);
                continue;
            }
            if remainder.starts_with(['\\', '%']) {
                break None;
            }

            let character = text
                .next()
                .expect("the literal text cursor is known nonempty");
            let transitioned = match character {
                '\n' => true,
                '\r' if text.remainder().starts_with('\n') => {
                    assert_eq!(text.next(), Some('\n'));
                    true
                }
                _ => false,
            };
            if transitioned {
                let coordinate = checked_suffix_coordinate(part, part_origin, text.remainder());
                if let Some(pending) =
                    literal_line_transition(text.rb(), coordinate, fence, &mut foreign)
                {
                    break Some(pending);
                }
            }
        }
    });

    assert!(
        pending.is_some() || !text.is_empty(),
        "a text witness is entered only after ruling out a structural starter"
    );
    let accepted = (!text.is_empty()).then(|| literal_text_item(text, part_origin, foreign));
    match pending {
        Some(pending) => LiteralPiece::Boundary { accepted, pending },
        None => LiteralPiece::Complete(
            accepted.expect("a structural stop follows a nonempty literal text Item"),
        ),
    }
}

/// The sole literal physical-line transition: classify without advancing,
/// then consume and record only an accepted body prefix.
fn literal_line_transition(
    mut i: LexIn,
    coordinate: usize,
    fence: &FenceBoundary,
    foreign: &mut Option<Vec<ForeignSplit>>,
) -> Option<Item> {
    match judge_fence_line(i.remainder(), coordinate, fence) {
        FenceLineDecision::Boundary(pending) => Some(Item::plain(
            LeadingTrivia::default(),
            Payload::Boundary(pending),
        )),
        FenceLineDecision::Body { prefix: None, .. } => None,
        FenceLineDecision::Body {
            prefix: Some(prefix),
            content,
        } => {
            let prefix_length = prefix
                .facts
                .extent
                .end
                .checked_sub(prefix.facts.extent.start)
                .expect("accepted prefix extent must be ordered");
            assert_eq!(prefix.facts.extent.start, coordinate);
            assert_eq!(prefix.facts.extent.end, content);
            PendingFragments::record(
                foreign,
                ForeignSplit::quote_prefix(prefix.facts.extent.start, prefix_length),
            )
            .expect("accepted prefixes stay ordered within one literal Item");
            consume_exact_bytes(i.rb(), prefix_length);
            None
        }
    }
}

fn literal_text_item(text: &str, part_origin: usize, foreign: Option<Vec<ForeignSplit>>) -> Item {
    let fragments = PendingFragments::finish(foreign, part_origin, text.len())
        .expect("literal fragment coordinates derive from one live suffix");
    let mut item = literal_token(text);
    if let Some(fragments) = fragments {
        item.with_fragments(fragments)
            .expect("one literal carrier covers its complete token payload");
    }
    item
}

fn literal_token(text: &str) -> Item {
    Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: text.into(),
        }),
    )
}

fn quote_run(source: &str) -> usize {
    source.bytes().take_while(|byte| *byte == b'"').count()
}

fn consume_exact_bytes(mut i: LexIn, length: usize) {
    let mut consumed = 0usize;
    while consumed < length {
        consumed = consumed
            .checked_add(
                i.next()
                    .expect("accepted literal source must remain live")
                    .len_utf8(),
            )
            .expect("accepted literal length must fit usize");
    }
    assert_eq!(consumed, length, "accepted source ends at a UTF-8 boundary");
}

fn checked_suffix_coordinate(part: &str, part_origin: usize, suffix: &str) -> usize {
    let consumed = part
        .len()
        .checked_sub(suffix.len())
        .expect("live literal suffix cannot exceed its entry suffix");
    assert_eq!(
        part.as_ptr().wrapping_add(consumed),
        suffix.as_ptr(),
        "live literal input remains a suffix of its entry input"
    );
    part_origin
        .checked_add(consumed)
        .expect("physical literal coordinate must fit usize")
}
