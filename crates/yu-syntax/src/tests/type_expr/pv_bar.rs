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

#[test]
fn bar_variant_colon_uses_head_or_leading_trivia_and_adjacent_identifier() {
    use crate::lexical::current_item::current_item;
    use crate::lexical::lexer::{scan_type_nud_payload, scan_type_payload};

    let operators = OperatorTable::empty();
    for (source, head, expected) in [
        (":a | :b", true, TokenKind::PolymorphicVariantColon),
        (":b", true, TokenKind::PolymorphicVariantColon), // after `(` or `|`
        (" :a | :b", false, TokenKind::PolymorphicVariantColon),
        (":y", false, TokenKind::Colon), // attached to `x`
        (": y", true, TokenKind::Colon),
        (":{", false, TokenKind::PolymorphicVariantColon),
    ] {
        let mut input = source;
        let item = current_item(
            chasa_recover::In::new(
                &mut input,
                &mut crate::cursor::LexRecover::new_for_test(&operators),
                (),
            ),
            0,
            LineEntry::InLine,
            None,
            |lex, leading, origin, fence, _| {
                if head {
                    scan_type_nud_payload(lex, leading, origin, fence)
                } else {
                    scan_type_payload(lex, leading, origin, fence)
                }
            },
        )
        .expect("type item")
        .item;
        assert_eq!(
            item.payload_view().token_kind(),
            Some(expected),
            "{source:?}"
        );
    }
    assert_clean("(:a | :b)");
    assert_clean(":a |:b");
    assert_clean(":a | :b");
}

#[test]
fn bar_variant_after_long_same_line_type_remains_lossless() {
    let prefix = "arg ".repeat(64);
    let source = format!("wrapper {prefix}(:a | :b)");
    assert_clean(&source);
}
