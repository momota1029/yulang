//! WP-18: protected fingerprints captured on the phase-1 parser.
#[path = "../../examples/support/recovery_corpus.rs"]
mod corpus;

/// The fingerprint key is `file:line`, where the line is where a code block starts.
/// It moves whenever a document above the block is edited, which says nothing about the
/// parser. The contract is on (file, source hash, CST hash), so compare without the line.
fn without_block_lines(rows: &str) -> Vec<String> {
    let mut rows: Vec<String> = rows
        .lines()
        .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
        .map(|line| {
            let (key, hashes) = line.split_once('\t').expect("fingerprint row has tabs");
            let file = key.rsplit_once(':').map_or(key, |(file, _)| file);
            format!("{file}\t{hashes}")
        })
        .collect();
    rows.sort();
    rows
}

#[test]
fn valid_corpus_cst_matches_phase_1_fingerprints() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let cases = corpus::corpus(&root);
    assert_eq!(
        without_block_lines(&corpus::fingerprints(&cases)),
        without_block_lines(include_str!("recovery_mutation_fingerprints.tsv"))
    );
}

use crate::{SyntaxKind, SyntaxNode};

fn production(source: &str) -> SyntaxNode {
    let case = corpus::Case {
        name: "WP-18 fixture".into(),
        code: source.into(),
        markdown: true,
    };
    let parsed = corpus::parse(&case, source);
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(root.to_string(), source);
    for token in root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
    {
        let range = usize::from(token.text_range().start())..usize::from(token.text_range().end());
        assert_eq!(&source[range], token.text());
    }
    root
}

fn binding_names(nodes: impl Iterator<Item = SyntaxNode>) -> Vec<String> {
    nodes
        .filter(|node| node.kind() == SyntaxKind::BindingStatement)
        .map(|node| {
            node.children()
                .find(|child| child.kind() == SyntaxKind::BindingHeader)
                .unwrap()
                .children()
                .find(|child| child.kind() == SyntaxKind::Pattern)
                .unwrap()
                .to_string()
        })
        .collect()
}

fn missing_closes(root: &SyntaxNode) -> Vec<(SyntaxKind, usize)> {
    root.descendants()
        .filter(|node| {
            matches!(
                node.kind(),
                SyntaxKind::ParenthesizedExpression
                    | SyntaxKind::ListExpression
                    | SyntaxKind::BracedStatementBlockExpression
                    | SyntaxKind::CallTail
            )
        })
        .flat_map(|owner| {
            owner
                .children_with_tokens()
                .filter(|child| child.kind() == SyntaxKind::Missing)
                .map(|child| (owner.kind(), usize::from(child.text_range().start())))
                .collect::<Vec<_>>()
        })
        .collect()
}

#[test]
fn wp18_example_keeps_later_declarations_at_statement_level() {
    let source = "my a = (1 +\nmy b = 2\nmy c = case n:\n    0 ->\nmy d = 4\nmy e = f(\nmy g = 5\n";
    let root = production(source);
    assert_eq!(
        binding_names(root.children()),
        ["a", "b", "c", "d", "e", "g"]
    );
    assert_eq!(
        missing_closes(&root),
        [
            (
                SyntaxKind::ParenthesizedExpression,
                source.find('\n').unwrap()
            ),
            (SyntaxKind::CallTail, source.find("\nmy g").unwrap()),
        ]
    );
}

#[test]
fn wp18_nested_unmatched_delimiters_close_before_the_pending_leading_trivia() {
    let source = "my a = ([{1\nmy b = 2\nmy c = 3\n";
    let root = production(source);
    assert_eq!(binding_names(root.children()), ["a", "b", "c"]);
    let at = source.find('\n').unwrap();
    assert_eq!(
        missing_closes(&root),
        [
            (SyntaxKind::ParenthesizedExpression, at),
            (SyntaxKind::ListExpression, at),
            (SyntaxKind::BracedStatementBlockExpression, at),
        ]
    );
}

#[test]
fn wp18_unmatched_opener_inside_a_matched_block_does_not_close_the_block() {
    let source = "my a = { my x = (1\nmy b = 2\n}\nmy c = 3\n";
    let root = production(source);
    assert_eq!(binding_names(root.children()), ["a", "c"]);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .unwrap();
    assert_eq!(
        binding_names(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .flat_map(|node| node.children())
        ),
        ["x", "b"]
    );
    assert_eq!(
        missing_closes(&root),
        [(
            SyntaxKind::ParenthesizedExpression,
            source.find('\n').unwrap()
        )]
    );
    assert_eq!(block.last_token().unwrap().kind(), SyntaxKind::RBrace);
}

#[test]
fn wp18_stray_closer_does_not_match_an_unrelated_opener() {
    let source = "my a = (1 ]\nmy b = 2\n";
    let root = production(source);
    assert_eq!(binding_names(root.children()), ["a", "b"]);
    let foreign = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ExpressionDelimitedForeignClose)
        .unwrap();
    assert_eq!(foreign.to_string().trim(), "]");
    // T18: the foreign-close Error is the single close failure, without a
    // second Missing for the same unmatched opener.
    assert!(missing_closes(&root).is_empty());
}

#[test]
fn wp18_string_and_comment_delimiters_do_not_supply_a_closer() {
    let source = "my a = (\"[}]\" /* ] } */ // )\nmy b = 2\n";
    let root = production(source);
    assert_eq!(binding_names(root.children()), ["a", "b"]);
    // WP-18 places Missing before all pending leading, including comments.
    assert_eq!(
        missing_closes(&root),
        [(
            SyntaxKind::ParenthesizedExpression,
            source.find(" /*").unwrap()
        )]
    );
    assert_eq!(
        root.descendants()
            .find(|node| node.kind() == SyntaxKind::StringLiteral)
            .unwrap()
            .to_string(),
        "\"[}]\""
    );
}

#[test]
fn wp18_valid_brace_block_keeps_its_column_zero_binding() {
    let source = "my a = {\nmy b = 2\n}\nmy c = 3\n";
    let root = production(source);
    assert_eq!(binding_names(root.children()), ["a", "c"]);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .unwrap();
    assert_eq!(block.to_string(), "{\nmy b = 2\n}");
    assert_eq!(
        binding_names(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .flat_map(|node| node.children())
        ),
        ["b"]
    );
    assert!(!root.descendants_with_tokens().any(|element| matches!(
        element.kind(),
        SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
    )));
    let openers =
        crate::lexical::unmatched::UnmatchedOpeners::scan(source, &crate::OperatorTable::empty());
    assert!((0..source.len()).all(|at| !openers.contains(at)));
}

#[test]
fn wp18_prepass_ignores_literals_docs_and_yumark_fences() {
    let operators = crate::OperatorTable::empty();
    for opaque in [
        "\"[)]\"",
        "\"escaped \\\" )\"",
        "\"\"\"[)]\"\"\"",
        "~\"[)]\"",
        "rule { \"[)]\" }",
        "/* ( /* [ */ { */",
        "// ( [ {\n",
        "-- 文書 ( [ {\n",
        "---\n文書 ( [ {\n```text\n---\n)]}\n```\n---\n",
        "'{\n```text\n)]}\n```\n}'",
    ] {
        let source = format!("(\n{opaque}\nmy b = 2\n");
        let openers = crate::lexical::unmatched::UnmatchedOpeners::scan(&source, &operators);
        assert_eq!(
            (0..source.len())
                .filter(|at| openers.contains(*at))
                .collect::<Vec<_>>(),
            [0],
            "{source:?}"
        );
    }
}

#[test]
fn wp18_prepass_matches_down_the_stack_and_ignores_stray_closers() {
    for (source, unmatched) in [
        ("([{}])", vec![]),
        ("([)", vec![1]),
        ("(][", vec![0, 2]),
        ("{([}", vec![1, 2]),
        ("]})", vec![]),
    ] {
        let openers = crate::lexical::unmatched::UnmatchedOpeners::scan(
            source,
            &crate::OperatorTable::empty(),
        );
        assert_eq!(
            (0..source.len())
                .filter(|at| openers.contains(*at))
                .collect::<Vec<_>>(),
            unmatched,
            "{source:?}"
        );
    }
}

#[test]
fn wp18_plain_names_and_deeper_declarations_do_not_resynchronize() {
    // Ordinary names and deeper declarations remain inside the unmatched group.
    // T18 separately covers control heads as statement boundaries.
    for source in ["my a = (1\nx\n", "my a = (1\n    my b = 2\n"] {
        assert_eq!(
            binding_names(production(source).children()),
            ["a"],
            "{source:?}"
        );
    }
    let root = production("my a = {\n    my b = (1\n    my c = 2\n}\nmy d = 3\n");
    assert_eq!(binding_names(root.children()), ["a", "d"]);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .unwrap();
    assert_eq!(
        binding_names(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .flat_map(|node| node.children())
        ),
        ["b", "c"]
    );
}

#[test]
fn wp18_shared_declaration_type_pattern_and_catch_owners_return_the_pending_declaration() {
    for source in [
        "struct P { x: int\nmy b = 2\n",
        "enum E { V\nmy b = 2\n",
        "type T = { x: int\nmy b = 2\n",
        "my a = catch x { v -> v\nmy b = 2\n",
        "my (x, 1\nmy b = 2\n",
        "enum opt 'a = nil | just{ 'a\nenum event { moved }\nmy b = 2\n",
    ] {
        let root = production(source);
        assert!(
            binding_names(root.children()).contains(&"b".into()),
            "{source:?}: {root:#?}"
        );
    }
}

#[test]
fn wp18_statement_start_indentation_is_independent_of_the_brace_sequence_baseline() {
    let source = "my a = { 0;\n    my b = (1\n  my c = 2\n}\nmy d = 3\n";
    let root = production(source);
    assert_eq!(binding_names(root.children()), ["a", "d"]);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .unwrap();
    assert_eq!(
        binding_names(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .flat_map(|node| node.children())
        ),
        ["b", "c"]
    );
}

#[test]
fn wp18_matched_parenthesis_shields_an_unmatched_inner_list() {
    let source = "my a = ([1\nmy b = 2\n)\nmy c = 3\n";
    let root = production(source);
    assert_eq!(binding_names(root.children()), ["a", "c"]);
    let paren = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
        .unwrap();
    assert_eq!(paren.last_token().unwrap().kind(), SyntaxKind::RParen);
    assert_eq!(
        missing_closes(&root),
        [(SyntaxKind::ListExpression, source.find('\n').unwrap())]
    );
}
