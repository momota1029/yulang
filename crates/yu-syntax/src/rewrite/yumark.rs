//! Inert Yumark fence selection and physical-line boundary facts.

use std::ops::Range;

use super::item::{BorrowedTarget, Boundary, PendingBoundary, StopKind};

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FenceOpener {
    pub(super) line: usize,
    pub(super) marker: Range<usize>,
    pub(super) marker_width: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum FencePrefixPolicy {
    None,
    ActivePrefixQuote { depth: usize, base: usize },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FenceBoundary {
    pub(super) opener: FenceOpener,
    pub(super) prefix_policy: FencePrefixPolicy,
    pub(super) close_column: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct QuotePrefixFacts {
    pub(super) indentation: Range<usize>,
    pub(super) marker: Range<usize>,
    pub(super) extent: Range<usize>,
    pub(super) depth: usize,
    pub(super) marker_len: usize,
    pub(super) marker_end: usize,
    pub(super) explicit: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct FenceCloseFacts {
    pub(super) line: usize,
    pub(super) inspected: Range<usize>,
    pub(super) prefix: Option<QuotePrefixFacts>,
    pub(super) indentation: Range<usize>,
    pub(super) indentation_column: usize,
    pub(super) marker: Range<usize>,
    pub(super) marker_width: usize,
    pub(super) horizontal_suffix: Range<usize>,
    pub(super) newline: Option<Range<usize>>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum QuoteTransitionKind {
    Reduced,
    Greater,
    NonPrefix,
    Explicit,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct YumarkFenceTransition {
    pub(super) line: usize,
    pub(super) expected_depth: usize,
    pub(super) expected_base: usize,
    pub(super) indentation: Range<usize>,
    pub(super) observed: Option<QuotePrefixFacts>,
    pub(super) kind: QuoteTransitionKind,
    pub(super) inspected: Range<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct AcceptedQuotePrefix {
    pub(super) facts: QuotePrefixFacts,
    pub(super) content: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum FenceLineDecision {
    Boundary(PendingBoundary),
    Body {
        prefix: Option<AcceptedQuotePrefix>,
        content: usize,
    },
}

/// Selects only an exact first ASCII-horizontal-delimited `yulang` atom.
pub(super) fn is_yulang_fence_info(info: &str) -> bool {
    if info.bytes().any(|byte| matches!(byte, b'\r' | b'\n')) {
        return false;
    }
    let info = info.trim_start_matches([' ', '\t']);
    let atom_end = info
        .bytes()
        .position(|byte| matches!(byte, b' ' | b'\t'))
        .unwrap_or(info.len());
    &info[..atom_end] == "yulang"
}

/// Judges one physical line without advancing or retaining the caller's input.
pub(super) fn judge_fence_line(
    source: &str,
    line: usize,
    boundary: &FenceBoundary,
) -> FenceLineDecision {
    if source.is_empty() {
        return FenceLineDecision::Boundary(PendingBoundary::new(
            line..line,
            Boundary::EofAfterTrivia,
        ));
    }

    let physical = PhysicalLine::new(source, line);
    match boundary.prefix_policy {
        FencePrefixPolicy::None => strict_close(&physical, 0, None, boundary)
            .map(borrowed_close)
            .unwrap_or(FenceLineDecision::Body {
                prefix: None,
                content: line,
            }),
        FencePrefixPolicy::ActivePrefixQuote { depth, base } => {
            let indentation = horizontal_len(physical.content);
            let after_indent = &physical.content[indentation..];
            let observed = quote_marker_facts(after_indent, line, indentation, base);
            if let Some(facts) = observed.as_ref()
                && !facts.explicit
                && facts.depth == depth
            {
                let prefix_len = indentation + facts.marker_len;
                if let Some(close) =
                    strict_close(&physical, prefix_len, Some(facts.clone()), boundary)
                {
                    return borrowed_close(close);
                }
                return FenceLineDecision::Body {
                    content: line + prefix_len,
                    prefix: Some(AcceptedQuotePrefix {
                        facts: facts.clone(),
                        content: line + prefix_len,
                    }),
                };
            }

            let kind = match observed.as_ref() {
                Some(facts) if facts.explicit => QuoteTransitionKind::Explicit,
                Some(facts) if facts.depth < depth => QuoteTransitionKind::Reduced,
                Some(_) => QuoteTransitionKind::Greater,
                None => QuoteTransitionKind::NonPrefix,
            };
            let transition = YumarkFenceTransition {
                line,
                expected_depth: depth,
                expected_base: base,
                indentation: line..line + indentation,
                observed,
                kind,
                inspected: line..line + physical.extent,
            };
            FenceLineDecision::Boundary(PendingBoundary::new(
                transition.inspected.clone(),
                Boundary::Stop(StopKind::YumarkFence(Box::new(transition))),
            ))
        }
    }
}

fn borrowed_close(facts: FenceCloseFacts) -> FenceLineDecision {
    FenceLineDecision::Boundary(PendingBoundary::new(
        facts.inspected.clone(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(Box::new(facts))),
    ))
}

fn strict_close(
    physical: &PhysicalLine<'_>,
    prefix_len: usize,
    prefix: Option<QuotePrefixFacts>,
    boundary: &FenceBoundary,
) -> Option<FenceCloseFacts> {
    let logical = physical.content.get(prefix_len..)?;
    let indentation = horizontal_len(logical);
    if indentation != boundary.close_column {
        return None;
    }
    let marker_start = prefix_len + indentation;
    let marker_end = marker_start.checked_add(boundary.opener.marker_width)?;
    let marker = physical.content.get(marker_start..marker_end)?;
    if boundary.opener.marker_width < 3 || !marker.bytes().all(|byte| byte == b'`') {
        return None;
    }
    let suffix = physical.content.get(marker_end..)?;
    if !suffix.bytes().all(|byte| matches!(byte, b' ' | b'\t')) {
        return None;
    }

    let absolute = |range: Range<usize>| line_range(physical.offset, range);
    Some(FenceCloseFacts {
        line: physical.offset,
        inspected: physical.offset..physical.offset + physical.extent,
        prefix,
        indentation: absolute(prefix_len..marker_start),
        indentation_column: indentation,
        marker: absolute(marker_start..marker_end),
        marker_width: boundary.opener.marker_width,
        horizontal_suffix: absolute(marker_end..physical.content.len()),
        newline: physical.newline.clone().map(|range| absolute(range)),
    })
}

fn quote_marker_facts(
    source: &str,
    line: usize,
    indentation: usize,
    base: usize,
) -> Option<QuotePrefixFacts> {
    let contiguous = source.bytes().take_while(|byte| *byte == b'>').count();
    if contiguous == 0 {
        return None;
    }
    let explicit = contiguous >= 3
        && indentation == base
        && source[contiguous..]
            .bytes()
            .all(|byte| matches!(byte, b' ' | b'\t'));
    let (depth, marker_len, marker_end) = if explicit {
        (contiguous, contiguous, contiguous)
    } else {
        prefix_quote_marker(source)
    };
    let marker_start = line + indentation;
    Some(QuotePrefixFacts {
        indentation: line..marker_start,
        marker: marker_start..marker_start + marker_end,
        extent: line..marker_start + marker_len,
        depth,
        marker_len,
        marker_end,
        explicit,
    })
}

fn prefix_quote_marker(source: &str) -> (usize, usize, usize) {
    let bytes = source.as_bytes();
    let mut index = 0;
    let mut marker_end = 0;
    let mut depth = 0;
    while bytes.get(index) == Some(&b'>') {
        index += 1;
        depth += 1;
        marker_end = index;
        while matches!(bytes.get(index), Some(b' ' | b'\t')) {
            index += 1;
        }
    }
    (depth, index.max(marker_end), marker_end)
}

fn horizontal_len(source: &str) -> usize {
    source
        .bytes()
        .take_while(|byte| matches!(byte, b' ' | b'\t'))
        .count()
}

fn line_range(offset: usize, range: Range<usize>) -> Range<usize> {
    offset + range.start..offset + range.end
}

struct PhysicalLine<'source> {
    content: &'source str,
    offset: usize,
    extent: usize,
    newline: Option<Range<usize>>,
}

impl<'source> PhysicalLine<'source> {
    fn new(source: &'source str, offset: usize) -> Self {
        if let Some(lf) = source.find('\n') {
            let content_end = lf.saturating_sub(usize::from(source[..lf].ends_with('\r')));
            Self {
                content: &source[..content_end],
                offset,
                extent: lf + 1,
                newline: Some(content_end..lf + 1),
            }
        } else {
            Self {
                content: source,
                offset,
                extent: source.len(),
                newline: None,
            }
        }
    }
}
