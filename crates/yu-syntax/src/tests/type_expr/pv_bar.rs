use super::*;

use crate::{SourceText, SyntaxEnvironment, parse_file, scan_header};
use std::sync::Arc;

fn parse(source: &str) -> SyntaxNode {
    let source: Arc<SourceText> = Arc::from(source);
    let parsed = parse_file(
        Arc::clone(&source),
        Arc::new(scan_header(Arc::clone(&source))),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(root.text(), source.as_ref());
    root
}

fn assert_clean(source: &str) {
    let full = format!("my f(x: {source}) = 0");
    let root = parse(&full);
    assert_eq!(root.text().to_string(), full);
    assert!(
        !root.descendants_with_tokens().any(|element| matches!(
            element.kind(),
            SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
        )),
        "{source:?}\n{root:#?}"
    );
}

#[test]
fn polymorphic_variant_bar_forms_reuse_tag_and_payload_nodes() {
    for source in [
        ":ready | :some int",
        ":ready | :some int | :pair (int, str)",
        ":some int | :ready",
        ":pair (int, str) | :ready | :done",
    ] {
        assert_clean(source);
        let full = format!("my f(x: {source}) = 0");
        let root = parse(&full);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("variant type");
        assert_eq!(variant.text(), source);
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            source.matches(':').count()
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
                .count(),
            usize::from(source.contains(":some int")) + usize::from(source.contains(":pair"))
        );
    }
}

#[test]
fn polymorphic_variant_bar_form_parses_in_annotation_and_round_trips() {
    let source = "my g(x: :ready | :some int) = 0";
    let root = parse(source);
    assert_eq!(root.text(), source);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
    );
}

#[test]
fn polymorphic_variant_bar_rejects_non_tags_and_general_union_stays_rejected() {
    for source in [":ready | int", "int | str"] {
        let full = format!("my f(x: {source}) = 0");
        let root = parse(&full);
        assert_eq!(root.text().to_string(), full);
        assert!(
            root.descendants_with_tokens().any(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
                )
            }),
            "{source:?}\n{root:#?}"
        );
    }
}

#[test]
fn lone_polymorphic_variant_tag_remains_rejected() {
    let source = "my f(x: :ready) = 0";
    let root = parse(source);
    assert_eq!(root.text(), source);
    assert!(root.descendants_with_tokens().any(|node| {
        matches!(
            node.kind(),
            SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
        )
    }));
}
