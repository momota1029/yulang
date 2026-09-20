//! Focused witnesses for the shadow CST-derived structural diagnostic walk.
//!
//! These drive `crate::structural_diagnostic` directly. They cover the
//! representative subset required by the active gate: a precise cataloged
//! `Missing`, precise raw `Error` groups in each mapped slot, a structured
//! `Invalid`, a byte-range-sensitive witness, and a deliberately uncataloged
//! generic fallback. They do not attempt catalog coverage.

use crate::{
    ExpectedSyntax, GrammarSlot, GrammarSlotRole, SyntaxKind, SyntaxNode,
    structural_diagnostic::{StructuralDiagnostic, StructuralKind},
    tests::support::{run, run_pattern, run_statement},
};

fn slot(owner: SyntaxKind, role: GrammarSlotRole) -> GrammarSlot {
    GrammarSlot::new(owner, role)
}

fn walk(source: &str) -> Vec<StructuralDiagnostic> {
    let (green, _) = run(source);
    assert_eq!(green.to_string(), source);
    crate::structural_diagnostic::collect(&SyntaxNode::new_root(green))
}

#[test]
fn precise_missing_slots_follow_the_ordered_delimited_children() {
    for (source, parent, anchor, role, expected) in [
        (
            "(,a)",
            SyntaxKind::ParenthesizedExpression,
            1,
            slot(SyntaxKind::ParenthesizedExpression, GrammarSlotRole::Item),
            ExpectedSyntax::Expression,
        ),
        (
            "(1x)",
            SyntaxKind::ParenthesizedExpression,
            2,
            slot(
                SyntaxKind::ParenthesizedExpression,
                GrammarSlotRole::Separator,
            ),
            ExpectedSyntax::DelimitedSequenceSeparator,
        ),
        (
            "(a",
            SyntaxKind::ParenthesizedExpression,
            2,
            slot(SyntaxKind::ParenthesizedExpression, GrammarSlotRole::Close),
            ExpectedSyntax::ClosingParenthesis,
        ),
        (
            "f(,a)",
            SyntaxKind::CallTail,
            2,
            slot(SyntaxKind::CallTail, GrammarSlotRole::Item),
            ExpectedSyntax::Expression,
        ),
        (
            "x[,a]",
            SyntaxKind::IndexTail,
            2,
            slot(SyntaxKind::IndexTail, GrammarSlotRole::Item),
            ExpectedSyntax::Expression,
        ),
    ] {
        let occurrences = walk(source);
        let missing = occurrences
            .iter()
            .find(|occurrence| {
                occurrence.kind() == StructuralKind::Missing && occurrence.range().start == anchor
            })
            .unwrap_or_else(|| panic!("{source:?}: {occurrences:?}"));
        assert_eq!(missing.parent(), parent, "{source:?}");
        assert_eq!(missing.identity().slot(), Some(role), "{source:?}");
        assert_eq!(
            missing.expectations(),
            Some([expected].as_slice()),
            "{source:?}"
        );
        assert_eq!(missing.primary_expectation(), Some(0), "{source:?}");
    }
}

#[test]
fn precise_raw_error_groups_follow_their_immediate_slot() {
    for (source, parent, range, role, expected) in [
        (
            "(@)",
            SyntaxKind::ParenthesizedExpression,
            1..2,
            slot(SyntaxKind::ParenthesizedExpression, GrammarSlotRole::Item),
            ExpectedSyntax::Expression,
        ),
        (
            "f(@)",
            SyntaxKind::CallTail,
            2..3,
            slot(SyntaxKind::CallTail, GrammarSlotRole::Item),
            ExpectedSyntax::Expression,
        ),
        (
            "x[@]",
            SyntaxKind::IndexTail,
            2..3,
            slot(SyntaxKind::IndexTail, GrammarSlotRole::Item),
            ExpectedSyntax::Expression,
        ),
        (
            "(a @ b)",
            SyntaxKind::ExpressionDelimitedSeparator,
            3..4,
            slot(
                SyntaxKind::ParenthesizedExpression,
                GrammarSlotRole::Separator,
            ),
            ExpectedSyntax::DelimitedSequenceSeparator,
        ),
        (
            "f(a @ b)",
            SyntaxKind::ExpressionDelimitedSeparator,
            4..5,
            slot(SyntaxKind::CallTail, GrammarSlotRole::Separator),
            ExpectedSyntax::DelimitedSequenceSeparator,
        ),
        (
            "(])",
            SyntaxKind::ExpressionDelimitedForeignClose,
            1..2,
            slot(SyntaxKind::ParenthesizedExpression, GrammarSlotRole::Close),
            ExpectedSyntax::ClosingParenthesis,
        ),
        (
            "f(])",
            SyntaxKind::ExpressionDelimitedForeignClose,
            2..3,
            slot(SyntaxKind::CallTail, GrammarSlotRole::Close),
            ExpectedSyntax::ClosingParenthesis,
        ),
    ] {
        let occurrences = walk(source);
        let group = occurrences
            .iter()
            .find(|occurrence| occurrence.kind() == StructuralKind::ErrorGroup)
            .unwrap_or_else(|| panic!("{source:?}: {occurrences:?}"));
        assert_eq!(group.parent(), parent, "{source:?}");
        assert_eq!(group.range(), &range, "{source:?}");
        assert_eq!(group.identity().slot(), Some(role), "{source:?}");
        assert_eq!(
            group.expectations(),
            Some([expected].as_slice()),
            "{source:?}"
        );
    }
}

#[test]
fn a_maximal_raw_error_run_is_one_grouped_occurrence() {
    let occurrences = walk("(@@a)");
    let groups = occurrences
        .iter()
        .filter(|occurrence| occurrence.kind() == StructuralKind::ErrorGroup)
        .collect::<Vec<_>>();
    assert_eq!(groups.len(), 1, "{occurrences:?}");
    assert_eq!(groups[0].range(), &(1..3));
    assert_eq!(groups[0].parent(), SyntaxKind::ParenthesizedExpression);
    assert_eq!(
        groups[0].identity().slot(),
        Some(slot(
            SyntaxKind::ParenthesizedExpression,
            GrammarSlotRole::Item
        ))
    );
}

#[test]
fn a_retry_continuation_keeps_one_grouped_raw_occurrence() {
    let occurrences = walk("f(@a)");
    let groups = occurrences
        .iter()
        .filter(|occurrence| occurrence.kind() == StructuralKind::ErrorGroup)
        .collect::<Vec<_>>();
    assert_eq!(groups.len(), 1, "{occurrences:?}");
    assert_eq!(groups[0].range(), &(2..3));
    assert_eq!(groups[0].parent(), SyntaxKind::CallTail);
    assert_eq!(
        groups[0].identity().slot(),
        Some(slot(SyntaxKind::CallTail, GrammarSlotRole::Item))
    );
}

#[test]
fn structured_invalid_is_its_own_kind_and_precedes_its_children() {
    let (green, _) = run_pattern("{1, b}");
    assert_eq!(green.to_string(), "{1, b}");
    let root = SyntaxNode::new_root(green);
    let invalid = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Invalid)
        .expect("a wrong-kind record item is structured");
    let range = usize::from(invalid.text_range().start())..usize::from(invalid.text_range().end());

    let occurrences = crate::structural_diagnostic::collect(&root);
    let outer = occurrences
        .iter()
        .find(|occurrence| occurrence.kind() == StructuralKind::Invalid)
        .expect("the structured Invalid occurrence");
    assert_eq!(outer.range(), &range);
    assert_eq!(outer.parent(), SyntaxKind::RecordPattern);
    assert!(
        outer.identity().slot().is_none(),
        "structured Invalid has no mapped precise row"
    );

    // Preorder: the enclosing Invalid precedes every occurrence nested inside
    // it, even though a nested occurrence may share its offset.
    for nested in occurrences.iter().filter(|occurrence| {
        occurrence.range().start >= range.start
            && occurrence.range().end <= range.end
            && occurrence.ordinal() != outer.ordinal()
    }) {
        assert!(
            nested.ordinal() > outer.ordinal(),
            "{nested:?} must follow {outer:?}"
        );
    }
    assert!(
        occurrences
            .windows(2)
            .all(|pair| pair[0].ordinal() < pair[1].ordinal()),
        "ordinals are strictly increasing in emission order"
    );
}

#[test]
fn an_uncataloged_occurrence_uses_the_deterministic_generic_fallback() {
    let (green, _) = run_statement("my x =");
    assert_eq!(green.to_string(), "my x =");
    let root = SyntaxNode::new_root(green);
    let occurrences = crate::structural_diagnostic::collect(&root);
    let missing = occurrences
        .iter()
        .find(|occurrence| occurrence.kind() == StructuralKind::Missing)
        .unwrap_or_else(|| panic!("{occurrences:?}"));
    assert_eq!(missing.range(), &(6..6));
    assert_eq!(missing.parent(), SyntaxKind::BindingBody);
    assert_eq!(missing.path().last(), Some(&SyntaxKind::BindingBody));
    assert!(
        missing.identity().slot().is_none(),
        "an unmapped slot keeps only the generic CST facts"
    );
    // Determinism: an independent walk reports the identical sequence.
    assert_eq!(crate::structural_diagnostic::collect(&root), occurrences);
}

#[test]
fn trivia_between_a_missing_and_its_ordered_sibling_keeps_the_slot() {
    // Trivia is not an ordered child phase. These are the trivia-interleaved
    // forms of the same mapped row, and the role still matches the slot the
    // owner emitted for the structural sibling that follows the `Missing`.
    for (source, parent, anchor, role) in [
        (
            "( ,a)",
            SyntaxKind::ParenthesizedExpression,
            1,
            slot(SyntaxKind::ParenthesizedExpression, GrammarSlotRole::Item),
        ),
        (
            "(1 x)",
            SyntaxKind::ParenthesizedExpression,
            2,
            slot(
                SyntaxKind::ParenthesizedExpression,
                GrammarSlotRole::Separator,
            ),
        ),
        (
            "f( ,a)",
            SyntaxKind::CallTail,
            2,
            slot(SyntaxKind::CallTail, GrammarSlotRole::Item),
        ),
        (
            "x[ ,a]",
            SyntaxKind::IndexTail,
            2,
            slot(SyntaxKind::IndexTail, GrammarSlotRole::Item),
        ),
    ] {
        let occurrences = walk(source);
        let missing = occurrences
            .iter()
            .find(|occurrence| {
                occurrence.kind() == StructuralKind::Missing && occurrence.range().start == anchor
            })
            .unwrap_or_else(|| panic!("{source:?}: {occurrences:?}"));
        assert_eq!(missing.parent(), parent, "{source:?}");
        assert_eq!(missing.identity().slot(), Some(role), "{source:?}");
    }
}

#[test]
fn utf8_and_crlf_ranges_stay_byte_accurate() {
    for (source, length) in [("(@β)", 5), ("(@β\r\n)", 7)] {
        assert_eq!(source.len(), length, "{source:?}");
        let occurrences = walk(source);
        let group = occurrences
            .iter()
            .find(|occurrence| occurrence.kind() == StructuralKind::ErrorGroup)
            .unwrap_or_else(|| panic!("{source:?}: {occurrences:?}"));
        assert_eq!(group.range(), &(1..2), "{source:?}");
        assert_eq!(
            group.identity().slot(),
            Some(slot(
                SyntaxKind::ParenthesizedExpression,
                GrammarSlotRole::Item
            )),
            "{source:?}"
        );
    }
}
