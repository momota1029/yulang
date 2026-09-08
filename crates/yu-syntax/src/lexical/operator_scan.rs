//! Raw successor evidence and lexical dynamic-operator selection.

use unicode_ident::{is_xid_continue, is_xid_start};

use crate::operator_table::{OperatorFixities, OperatorFixity, OperatorKindSet, OperatorTable};

use crate::cursor::LexIn;
use crate::lexical::{
    current_item::LineEntry,
    item::{OperatorToken, OperatorUse},
    stops::{Stops, active_stop},
    trivia::{TriviaObservation, observe_fenced_trivia},
    yumark::FenceBoundary,
};

#[cfg(test)]
pub(crate) fn scan_operator(
    i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    baseline: usize,
    stops: Stops,
) -> Option<OperatorToken> {
    scan_operator_fenced(i, site, has_leading_trivia, baseline, stops, 0, None)
}

/// Selects one dynamic operator using only the visible suffix of its current
/// cell. The caller passes the immediate payload coordinate; nothing is
/// retained after this source-only lexical probe returns.
pub(crate) fn scan_operator_fenced(
    mut i: LexIn,
    site: OperatorSite,
    has_leading_trivia: bool,
    baseline: usize,
    stops: Stops,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<OperatorToken> {
    let table = i.recovery().operators();
    let source = i.remainder();
    let (use_, end) = table.longest_source_match_then(source, |last, entry, end| {
        operator_boundary(last, &source[end..])?;
        let kinds = entry.fixities().kinds();
        let observation = observe_fenced_trivia(
            &source[end..],
            payload_origin.checked_add(end)?,
            LineEntry::InLine,
            fence,
        );
        let (post_whitespace, value_start) = match observation {
            TriviaObservation::Boundary => (true, false),
            TriviaObservation::Visible(visible) => {
                if is_call_or_path_sensitive(kinds)
                    && !visible.present
                    && matches!(visible.source.chars().next(), Some('(' | ':'))
                {
                    return None;
                }
                let post_whitespace = visible.present
                    || visible.source.is_empty()
                    || active_stop(visible.source, stops);
                let value_start =
                    raw_value_start(table, visible.indentation, visible.source, baseline);
                (post_whitespace, value_start)
            }
        };
        let with_value = judge_operator(site, kinds, has_leading_trivia, post_whitespace, true);
        let without_value = judge_operator(site, kinds, has_leading_trivia, post_whitespace, false);
        let fixity = if is_call_or_path_sensitive(kinds) && post_whitespace && value_start {
            Some(OperatorFixity::Prefix)
        } else if with_value != without_value {
            if value_start {
                with_value
            } else {
                without_value
            }
        } else {
            with_value
        }?;
        selected_operator_use(entry.fixities(), fixity)
    })?;
    let character_count = source[..end].chars().count();
    let (accepted, text) = i.with_str(|mut operator| {
        for _ in 0..character_count {
            operator.next()?;
        }
        Some(())
    });
    accepted?;
    Some(OperatorToken {
        text: text.into(),
        use_,
    })
}

/// Fence-aware counterpart of [`scan_dangling_operator`]. A fence boundary
/// is a local EOF fact for this one spelling; the pending boundary Item stays
/// for the next current-Item acquisition.
pub(crate) fn scan_dangling_operator_fenced(
    mut i: LexIn,
    site: OperatorSite,
    baseline: usize,
    stops: Stops,
    payload_origin: usize,
    fence: Option<&FenceBoundary>,
) -> Option<OperatorToken> {
    let table = i.recovery().operators();
    let source = i.remainder();
    let (use_, end) = table.longest_source_match_then(source, |last, entry, end| {
        operator_boundary(last, &source[end..])?;
        let fixities = entry.fixities();
        let fixity = match site {
            OperatorSite::Nud if fixities.prefix().is_some() && !fixities.is_nullfix() => {
                OperatorFixity::Prefix
            }
            OperatorSite::Led if fixities.infix().is_some() && fixities.suffix().is_none() => {
                OperatorFixity::Infix
            }
            _ => return None,
        };
        dangling_follower_fenced(
            &source[end..],
            payload_origin.checked_add(end)?,
            baseline,
            stops,
            fence,
        )?;
        selected_operator_use(fixities, fixity)
    })?;
    let character_count = source[..end].chars().count();
    let (accepted, text) = i.with_str(|mut operator| {
        for _ in 0..character_count {
            operator.next()?;
        }
        Some(())
    });
    accepted?;
    Some(OperatorToken {
        text: text.into(),
        use_,
    })
}

/// A dangling role may be followed by a local boundary, EOF, or one invalid
/// region.  Structural starters stay for their future direct owners, and a
/// shallow newline stays with the outer statement owner.
fn dangling_follower_fenced(
    source: &str,
    source_origin: usize,
    baseline: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> Option<()> {
    match observe_fenced_trivia(source, source_origin, LineEntry::InLine, fence) {
        TriviaObservation::Boundary => Some(()),
        TriviaObservation::Visible(visible) => {
            if visible
                .indentation
                .is_some_and(|indentation| indentation <= baseline)
            {
                return None;
            }
            if visible.source.is_empty() || active_stop(visible.source, stops) {
                return Some(());
            }
            (!matches!(
                visible.source.chars().next(),
                Some(':' | '=' | ',' | ';' | ')' | ']' | '}' | '{')
            ))
            .then_some(())
        }
    }
}

fn operator_boundary(last: char, following: &str) -> Option<()> {
    (!is_xid_continue(last)
        || following
            .chars()
            .next()
            .is_none_or(|character| !is_xid_continue(character)))
    .then_some(())
}

fn raw_value_start(
    table: &OperatorTable,
    indentation: Option<usize>,
    source: &str,
    baseline: usize,
) -> bool {
    if indentation.is_some_and(|indentation| indentation <= baseline) {
        return false;
    }

    match source.chars().next() {
        Some('"' | '(' | '[' | '{' | '$' | '\\' | '%' | '_' | '\'') => true,
        Some(character)
            if is_xid_start(character) || character.is_ascii_digit() || character == '.' =>
        {
            true
        }
        _ => table.value_start_source_len(source).is_some(),
    }
}

fn selected_operator_use(
    fixities: &OperatorFixities,
    fixity: OperatorFixity,
) -> Option<OperatorUse> {
    match fixity {
        OperatorFixity::Prefix => Some(OperatorUse::Prefix(
            fixities.prefix()?.right_binding_power().clone(),
        )),
        OperatorFixity::Infix => {
            let infix = fixities.infix()?;
            Some(OperatorUse::Infix {
                left: infix.left_binding_power().clone(),
                right: infix.right_binding_power().clone(),
            })
        }
        OperatorFixity::Suffix => Some(OperatorUse::Suffix(
            fixities.suffix()?.left_binding_power().clone(),
        )),
        OperatorFixity::Nullfix => fixities.is_nullfix().then_some(OperatorUse::Nullfix),
    }
}

/// Which side of a Pratt operand is requesting an operator.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum OperatorSite {
    Nud,
    Led,
}

pub(crate) fn is_call_or_path_sensitive(kinds: OperatorKindSet) -> bool {
    kinds.contains(OperatorKindSet::PREFIX | OperatorKindSet::NULLFIX)
        && !kinds.contains(OperatorKindSet::INFIX)
        && !kinds.contains(OperatorKindSet::SUFFIX)
}

pub(crate) fn judge_operator(
    site: OperatorSite,
    kinds: OperatorKindSet,
    pre_whitespace: bool,
    post_whitespace: bool,
    probe_value_start: bool,
) -> Option<OperatorFixity> {
    match site {
        OperatorSite::Nud => judge_nud(
            kind_bits(kinds),
            pre_whitespace,
            post_whitespace,
            probe_value_start,
        ),
        OperatorSite::Led => judge_led(
            kind_bits(kinds),
            pre_whitespace,
            post_whitespace,
            probe_value_start,
        ),
    }
}

const PREFIX: u8 = 1 << 0;
const INFIX: u8 = 1 << 1;
const SUFFIX: u8 = 1 << 2;
const NULLFIX: u8 = 1 << 3;

fn kind_bits(kinds: OperatorKindSet) -> u8 {
    let mut bits = 0;
    for (kind, bit) in [
        (OperatorKindSet::PREFIX, PREFIX),
        (OperatorKindSet::INFIX, INFIX),
        (OperatorKindSet::SUFFIX, SUFFIX),
        (OperatorKindSet::NULLFIX, NULLFIX),
    ] {
        if kinds.contains(kind) {
            bits |= bit;
        }
    }
    bits
}

fn judge_nud(
    mut kinds: u8,
    pre_whitespace: bool,
    post_whitespace: bool,
    probe_value_start: bool,
) -> Option<OperatorFixity> {
    kinds &= !(INFIX | SUFFIX);
    if !probe_value_start {
        kinds &= !PREFIX;
    }
    judge_table(kinds, pre_whitespace, post_whitespace)
}

fn judge_led(
    mut kinds: u8,
    pre_whitespace: bool,
    post_whitespace: bool,
    probe_value_start: bool,
) -> Option<OperatorFixity> {
    if !probe_value_start {
        kinds &= !(PREFIX | INFIX);
    }
    let mut multiline_argument_kinds = kinds;
    if post_whitespace {
        multiline_argument_kinds &= !PREFIX;
    }
    judge_table(multiline_argument_kinds, pre_whitespace, post_whitespace)
        .or_else(|| judge_table(kinds, pre_whitespace, post_whitespace))
}

fn judge_table(kinds: u8, pre_whitespace: bool, post_whitespace: bool) -> Option<OperatorFixity> {
    use OperatorFixity::{Infix, Nullfix, Prefix, Suffix};

    const P: Option<OperatorFixity> = Some(Prefix);
    const I: Option<OperatorFixity> = Some(Infix);
    const S: Option<OperatorFixity> = Some(Suffix);
    const N: Option<OperatorFixity> = Some(Nullfix);
    const X: Option<OperatorFixity> = None;
    const TABLE: [[Option<OperatorFixity>; 4]; 16] = [
        [X, X, X, X],
        [P, P, P, P],
        [I, I, I, I],
        [I, I, P, I],
        [S, S, S, S],
        [X, S, P, X],
        [I, S, I, I],
        [I, S, P, I],
        [N, N, N, N],
        [P, N, P, N],
        [I, I, I, N],
        [I, I, P, N],
        [N, S, N, N],
        [N, S, P, N],
        [I, S, I, N],
        [I, S, P, N],
    ];
    let whitespace = ((pre_whitespace as usize) << 1) | post_whitespace as usize;
    TABLE[kinds as usize][whitespace]
}
