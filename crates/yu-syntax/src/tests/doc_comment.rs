use std::sync::Arc;

use crate::tests::support::{StructuralFact, structural_facts};
use crate::{
    HeaderStop, SourceText, StructuralRecoveryKind, SyntaxEnvironment, SyntaxKind, SyntaxNode,
    structural_diagnostic::StructuralKind,
};

fn parse(source: &str) -> crate::ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    crate::parse_file(
        Arc::clone(&source),
        Arc::new(crate::scan_header(Arc::clone(&source))),
        Arc::new(SyntaxEnvironment::empty()),
    )
}

fn count(root: &SyntaxNode, kind: SyntaxKind) -> usize {
    root.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn facts(parsed: &crate::ParsedFile) -> Vec<StructuralFact> {
    structural_facts(parsed.green())
}

#[test]
fn statement_marker_wins_only_at_canonical_statement_start() {
    let source = concat!(
        "prefix (--) 70 = value\n",
        "infix (--) 50 51 = value;\n",
        "infix (---) 50 51 = value;\n",
        "-- statement document\n",
        "my a = --x\n",
        "my b = x -- y\n",
        "my c = x --- y\n",
    );
    let parsed = parse(source);
    assert_eq!(parsed.green().to_string(), source);
    assert!(
        facts(&parsed).is_empty(),
        "{:?} {:#?}",
        facts(&parsed),
        parsed.structural_recoveries(),
    );
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(count(&root, SyntaxKind::DocCommentDeclaration), 1);
    assert_eq!(count(&root, SyntaxKind::PrefixOperatorUse), 1);
    assert_eq!(count(&root, SyntaxKind::InfixOperatorUse), 2);

    let source = "prefix (--) 70 = value\n---\nblock\n---\n";
    let parsed = parse(source);
    assert_eq!(parsed.green().to_string(), source);
    assert!(
        facts(&parsed).is_empty(),
        "{:?} {:#?}",
        facts(&parsed),
        parsed.structural_recoveries(),
    );
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(count(&root, SyntaxKind::DocCommentDeclaration), 1);
    assert_eq!(count(&root, SyntaxKind::DocBlockOpen), 0);
    assert_eq!(
        root.descendants_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::DocLinePrefix)
            .count(),
        0,
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::DocBlockOpen)
            .count(),
        1,
    );
}

#[test]
fn base_column_marker_ends_the_preceding_expression_before_dynamic_led() {
    for source in [
        "infix (-) 5.0.0 5.0.1 = f\nmy y = f\n-- doc\nmy x = 1",
        "infix (-) 5.0.0 5.0.1 = f\n-- doc\nmy x = 1",
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source);
        assert!(
            facts(&parsed).is_empty(),
            "{source:?}: {:?}",
            facts(&parsed)
        );
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(count(&root, SyntaxKind::DocCommentDeclaration), 1);
        assert_eq!(count(&root, SyntaxKind::Error), 0);
    }
}

#[test]
fn base_column_marker_boundary_applies_in_every_statement_container() {
    for source in [
        concat!(
            "infix (-) 5.0.0 5.0.1 = f\n",
            "my y = f\n",
            "-- root\n",
            "my x = 1\n",
        ),
        concat!(
            "infix (-) 5.0.0 5.0.1 = f\n",
            "{\n  f\n  -- braced\n  f\n}\n",
        ),
        concat!(
            "infix (-) 5.0.0 5.0.1 = f\n",
            "if c:\n  f\n  -- indented\n  f\n",
        ),
        concat!(
            "infix (-) 5.0.0 5.0.1 = f\n",
            "mod M: f\n",
            "-- after inline\n",
            "my x = 1\n",
        ),
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source, "{source:?}");
        assert!(
            facts(&parsed).is_empty(),
            "{source:?}: {:?}",
            facts(&parsed)
        );
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            count(&root, SyntaxKind::DocCommentDeclaration),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn base_column_marker_boundary_survives_every_preceding_statement_family() {
    let header = "infix (-) 5.0.0 5.0.1 = f\n";
    for preceding in [
        "my y = f",
        "use p",
        "type T;",
        "type T = U",
        "struct S;",
        "struct S{field:T}",
        "enum E;",
        "enum E{A}",
        "case f: x -> f",
        "if f: f",
    ] {
        let source = format!("{header}{preceding}\n-- doc\nmy x = 1\n");
        let parsed = parse(&source);
        assert_eq!(parsed.green().to_string(), source, "{preceding:?}");
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            count(&root, SyntaxKind::DocCommentDeclaration),
            1,
            "{preceding:?}"
        );
    }
}

#[test]
fn marker_boundary_is_independent_of_declared_operator_spelling_and_fixity() {
    for source in [
        concat!(
            "prefix (-) 5.0.0 = f\n",
            "my y = f\n",
            "-- doc\n",
            "my x = 1\n",
        ),
        concat!(
            "infix (--) 5.0.0 5.0.1 = f\n",
            "my y = f\n",
            "-- doc\n",
            "my x = 1\n",
        ),
        concat!(
            "infix (---) 5.0.0 5.0.1 = f\n",
            "my y = f\n",
            "---\nblock\n---\n",
            "my x = 1\n",
        ),
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source, "{source:?}");
        assert!(
            facts(&parsed).is_empty(),
            "{source:?}: {:?}",
            facts(&parsed)
        );
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            count(&root, SyntaxKind::DocCommentDeclaration),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn deeper_and_mid_line_markers_remain_dynamic_operators() {
    for source in [
        concat!("infix (--) 5.0.0 5.0.1 = f\n", "my y = f\n  -- x\n",),
        concat!("infix (--) 5.0.0 5.0.1 = f\n", "my y = f -- x\n",),
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source, "{source:?}");
        assert!(
            facts(&parsed).is_empty(),
            "{source:?}: {:?}",
            facts(&parsed)
        );
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            count(&root, SyntaxKind::DocCommentDeclaration),
            0,
            "{source:?}"
        );
        assert_eq!(count(&root, SyntaxKind::InfixOperatorUse), 1, "{source:?}");
    }
}

#[test]
fn base_column_marker_boundary_preserves_crlf() {
    let source = concat!(
        "infix (-) 5.0.0 5.0.1 = f\r\n",
        "my y = f\r\n",
        "-- doc\r\n",
        "my x = 1\r\n",
    );
    let parsed = parse(source);
    assert_eq!(parsed.green().to_string(), source);
    assert!(facts(&parsed).is_empty(), "{:?}", facts(&parsed));
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(count(&root, SyntaxKind::DocCommentDeclaration), 1);
}

#[test]
fn root_doc_stops_header_discovery_before_later_imports_and_operators() {
    for source in [
        "-- docs\nuse late\ninfix (+) 50 51 = value\n",
        "---\ndocs\n---\nuse late\ninfix (+) 50 51 = value\n",
    ] {
        let header = crate::scan_header(Arc::from(source));
        assert_eq!(header.coverage().range(), &(0..0), "{source:?}");
        assert_eq!(header.coverage().stop(), HeaderStop::FirstNonHeader);
        assert!(header.imports().is_empty());
        assert!(header.operators().is_empty());
    }
}

#[test]
fn every_canonical_statement_container_dispatches_doc_declarations() {
    for source in [
        "-- root\n",
        "{ -- braced\nvalue }",
        "if condition:\n  -- indented\n  value\n",
        "mod M: -- inline\n",
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source, "{source:?}");
        assert!(facts(&parsed).is_empty(), "{source:?}");
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            count(&root, SyntaxKind::DocCommentDeclaration),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn nested_block_doc_close_uses_the_opening_statement_column() {
    for source in [
        "{\n  ---\n  braced\n  ---\n}\n",
        "if condition:\n  ---\n  indented\n  ---\n  value\n",
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source, "{source:?}");
        assert!(
            facts(&parsed).is_empty(),
            "{source:?}: {:?}",
            facts(&parsed)
        );
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(count(&root, SyntaxKind::DocCommentDeclaration), 1);
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == SyntaxKind::DocBlockClose)
                .count(),
            1,
        );
    }
}

#[test]
fn field_and_owner_specific_sequences_do_not_admit_doc_declarations() {
    for (source, expected) in [
        (
            "struct S { -- docs\nfield: T }",
            vec![
                (StructuralKind::ErrorGroup, 11..13),
                (StructuralKind::Missing, 14..14),
                (StructuralKind::Missing, 18..18),
            ],
        ),
        (
            "enum E { -- docs\nA }",
            vec![(StructuralKind::ErrorGroup, 9..11)],
        ),
        (
            "type R = { -- docs\nfield: T }",
            vec![(StructuralKind::ErrorGroup, 11..18)],
        ),
        (
            "role R:\n  -- docs\n  pub show: T\n",
            vec![(StructuralKind::ErrorGroup, 10..12)],
        ),
        (
            "act A:\n  -- docs\n  pub run: T\n",
            vec![(StructuralKind::ErrorGroup, 9..11)],
        ),
        (
            "role R { -- docs\npub show: T }",
            vec![(StructuralKind::ErrorGroup, 9..11)],
        ),
        (
            "act A { -- docs\npub run: T }",
            vec![(StructuralKind::ErrorGroup, 8..10)],
        ),
        ("role R: -- docs", vec![(StructuralKind::ErrorGroup, 8..10)]),
        ("act A: -- docs", vec![(StructuralKind::ErrorGroup, 7..9)]),
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source, "{source:?}");
        assert_eq!(facts(&parsed), expected, "{source:?}");
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            count(&root, SyntaxKind::DocCommentDeclaration),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn ordinary_comments_and_nonmarkers_keep_their_existing_paths() {
    for source in [
        "// ordinary\nmy x = 1\n",
        "/* ordinary */ my x = 1\n",
        "---x\n",
        "----\n",
        "my x = 1 --- value\n",
        "value; -- not a statement start\n",
    ] {
        let parsed = parse(source);
        assert_eq!(parsed.green().to_string(), source, "{source:?}");
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            count(&root, SyntaxKind::DocCommentDeclaration),
            0,
            "{source:?}"
        );
    }

    let parsed = parse("-- orphan");
    assert_eq!(parsed.green().to_string(), "-- orphan");
    assert!(
        facts(&parsed).is_empty(),
        "{:?} {:#?}",
        facts(&parsed),
        parsed.structural_recoveries(),
    );
}

#[test]
fn whole_file_docs_are_lossless_and_recover_one_unterminated_envelope() {
    let source = concat!(
        "-- line *document* [link](dest)\n",
        "my first = 1\n",
        "---\n",
        "# Heading\n",
        "- item\n",
        "> quote\n",
        "\\note[argument]\n",
        "```rust\n",
        "fn main() {}\n",
        "```\n",
        "---\n",
        "my second = 2\n",
    );
    let parsed = parse(source);
    assert_eq!(parsed.green().to_string(), source);
    assert!(facts(&parsed).is_empty());
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(count(&root, SyntaxKind::DocCommentDeclaration), 2);
    for kind in [
        SyntaxKind::YmSection,
        SyntaxKind::YmList,
        SyntaxKind::YmQuoteBlock,
        SyntaxKind::YmCommand,
        SyntaxKind::YmCodeFence,
    ] {
        assert!(count(&root, kind) >= 1, "missing {kind:?}");
    }

    let crlf = "---\r\n# Heading\r\ntext\r\n---\r\nmy x = 1\r\n";
    let parsed = parse(crlf);
    assert_eq!(parsed.green().to_string(), crlf);
    assert!(
        facts(&parsed).is_empty(),
        "{:?} {:#?}",
        facts(&parsed),
        parsed.structural_recoveries(),
    );

    let unterminated = "---\n# Heading\nbody";
    let parsed = parse(unterminated);
    assert_eq!(parsed.green().to_string(), unterminated);
    let recoveries = parsed.structural_recoveries();
    assert_eq!(recoveries.len(), 1);
    assert_eq!(recoveries[0].kind(), StructuralRecoveryKind::Missing);
    assert_eq!(
        recoveries[0].range(),
        &(unterminated.len()..unterminated.len())
    );
}
