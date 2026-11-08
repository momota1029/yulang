//! Read-only cursor lookup over a lossless CST.

use crate::{ExpectedSyntax, GrammarSlot, GrammarSlotRole, SyntaxKind, SyntaxNode, SyntaxToken};
use std::ops::Range;

/// A mapped slot at a cursor position. Empty interpolation bodies have a
/// slot even though the parser represents them as an empty node, not Missing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CursorSlot {
    pub slot: GrammarSlot,
    pub expected: ExpectedSyntax,
    pub range: Range<usize>,
}

/// A single incomplete sigil represented by an existing Error token.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Sigil {
    Apostrophe,
    Dollar,
    Ampersand,
}

/// Context established by the CST, without guessing the sigil's meaning.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SigilContext {
    BindingPattern,
    TypeRightHandSide,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PartialSigil {
    pub sigil: Sigil,
    pub context: SigilContext,
    pub range: Range<usize>,
}

/// The syntax surrounding a byte position in one CST snapshot.
#[derive(Clone, Debug)]
pub struct CursorContext {
    pub node: SyntaxNode,
    pub left: Option<SyntaxToken>,
    pub right: Option<SyntaxToken>,
    /// All mapped matching recovery slots in diagnostic CST preorder, followed
    /// by matching empty interpolation body slots in CST preorder. Duplicate
    /// occurrences are retained, including slots at the same byte position.
    pub slots: Vec<CursorSlot>,
    /// Deepest mapped diagnostic slot, retained for compatibility.
    pub slot: Option<GrammarSlot>,
    pub expected: Option<ExpectedSyntax>,
    pub partial_sigil: Option<PartialSigil>,
}

/// Find context in a root CST at a UTF-8 byte boundary, or return `None` for
/// an offset past the source or inside a UTF-8 code point. Nonempty node and
/// slot ranges are half-open; empty ranges match their exact position. At EOF
/// the root is the fallback. Tokens include trivia: inside a token it is both
/// left and right; at a boundary the adjacent tokens are independent.
/// A partial sigil is an Error token that is the last non-trivia token ending
/// at or before the cursor. Bare `$` and `&` have unknown context. This walks
/// the entire tree iteratively; it is not an incremental index. If structural
/// projection fails, its diagnostic-derived slots are absent.
pub fn cursor_context(root: &SyntaxNode, offset: usize) -> Option<CursorContext> {
    let text = root.text().to_string();
    if offset > text.len() || !text.is_char_boundary(offset) {
        return None;
    }
    let mut node = root.clone();
    let mut depth = 0usize;
    let mut empty_bodies = Vec::new();
    let mut stack = vec![(root.clone(), 0usize)];
    while let Some((current, d)) = stack.pop() {
        let range = current.text_range();
        let start = usize::from(range.start());
        let end = usize::from(range.end());
        if (start == end && start == offset) || (start <= offset && offset < end) {
            if d > depth {
                node = current.clone();
                depth = d;
            }
            if current.kind() == SyntaxKind::StringInterpolationBody
                && start == end
                && current.parent().is_some_and(|parent| {
                    parent.children().any(|n| n.kind() == SyntaxKind::Missing)
                })
            {
                empty_bodies.push(CursorSlot {
                    slot: GrammarSlot::new(
                        SyntaxKind::StringInterpolationBody,
                        GrammarSlotRole::ExpressionBody,
                    ),
                    expected: ExpectedSyntax::Statement,
                    range: start..end,
                });
            }
        }
        if start <= offset && offset <= end {
            stack.extend(
                current
                    .children()
                    .collect::<Vec<_>>()
                    .into_iter()
                    .rev()
                    .map(|child| (child, d + 1)),
            );
        }
    }
    let mut left = None;
    let mut right = None;
    let mut last_significant = None;
    for element in root.descendants_with_tokens() {
        let Some(token) = element.into_token() else {
            continue;
        };
        let range = token.text_range();
        let start = usize::from(range.start());
        let end = usize::from(range.end());
        if start < offset && offset <= end {
            left = Some(token.clone());
        }
        if right.is_none() && start <= offset && offset < end {
            right = Some(token.clone());
        }
        if end <= offset
            && !matches!(
                token.kind(),
                SyntaxKind::Whitespace
                    | SyntaxKind::Newline
                    | SyntaxKind::LineComment
                    | SyntaxKind::BlockComment
            )
        {
            last_significant = Some(token);
        } else if start < offset
            && offset < end
            && !matches!(
                token.kind(),
                SyntaxKind::Whitespace
                    | SyntaxKind::Newline
                    | SyntaxKind::LineComment
                    | SyntaxKind::BlockComment
            )
        {
            last_significant = None;
        }
    }
    let partial_sigil = last_significant.and_then(|token| {
        if token.kind() != SyntaxKind::Error {
            return None;
        }
        let sigil = match token.text() {
            "'" => Sigil::Apostrophe,
            "$" => Sigil::Dollar,
            "&" => Sigil::Ampersand,
            _ => return None,
        };
        let start = usize::from(token.text_range().start());
        let end = usize::from(token.text_range().end());
        let mut context = SigilContext::Unknown;
        for ancestor in token.parent_ancestors() {
            if ancestor.kind() == SyntaxKind::BindingHeader {
                context = SigilContext::BindingPattern;
                break;
            }
            if ancestor.kind() == SyntaxKind::TypeDeclaration {
                if ancestor.children_with_tokens().any(|child| {
                    child.kind() == SyntaxKind::Equals
                        && usize::from(child.text_range().end()) <= start
                }) {
                    context = SigilContext::TypeRightHandSide;
                }
                break;
            }
        }
        Some(PartialSigil {
            sigil,
            context,
            range: start..end,
        })
    });
    let mut slots = Vec::new();
    let mut slot = None;
    let mut expected = None;
    let mut slot_depth = 0;
    if let Ok(occurrences) = crate::structural_diagnostic::try_collect(root) {
        for occurrence in occurrences {
            let range = occurrence.range();
            let matches = if range.is_empty() {
                range.start == offset
            } else {
                range.contains(&offset)
            };
            if matches {
                if let (Some(mapped), Some(value)) = (
                    occurrence.identity().slot(),
                    occurrence.expectations().and_then(|v| v.first()).copied(),
                ) {
                    slots.push(CursorSlot {
                        slot: mapped,
                        expected: value,
                        range: range.clone(),
                    });
                    if occurrence.path().len() >= slot_depth {
                        slot_depth = occurrence.path().len();
                        slot = Some(mapped);
                        expected = Some(value);
                    }
                }
            }
        }
    }
    slots.extend(empty_bodies);
    Some(CursorContext {
        node,
        left,
        right,
        slots,
        slot,
        expected,
        partial_sigil,
    })
}
