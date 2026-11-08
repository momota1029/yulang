use yu_syntax::{ParsedFile, SyntaxDiagnosticCause, SyntaxKind, SyntaxNode};

#[allow(dead_code)]
#[path = "../examples/support/recovery_corpus.rs"]
mod corpus;

fn parse(source: &str) -> ParsedFile {
    let parsed = corpus::parse(
        &corpus::Case {
            name: "T18 unmatched delimiters".into(),
            code: source.into(),
            markdown: true,
        },
        source,
    );
    assert_eq!(parsed.green().to_string(), source);
    let root = SyntaxNode::new_root(parsed.green().clone());
    for token in root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
    {
        let range = usize::from(token.text_range().start())..usize::from(token.text_range().end());
        assert_eq!(&source[range], token.text());
    }
    parsed
}

fn root(parsed: &ParsedFile) -> SyntaxNode {
    SyntaxNode::new_root(parsed.green().clone())
}

fn check_diagnostics(parsed: &ParsedFile, count: usize) {
    let diagnostics = parsed.syntax_diagnostics().unwrap();
    assert_eq!(
        diagnostics.len(),
        count,
        "{diagnostics:#?}\n{:#?}",
        root(parsed)
    );
}

fn check_independent_suffix(source: &str, count: usize, middle: SyntaxKind) {
    let parsed = parse(source);
    check_diagnostics(&parsed, count);
    let root = root(&parsed);
    let statements: Vec<_> = root.children().collect();
    assert_eq!(
        statements
            .iter()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::BindingStatement,
            middle,
            SyntaxKind::BindingStatement
        ],
        "{root:#?}"
    );
    assert!(statements[1].to_string().trim_start().starts_with(
        if middle == SyntaxKind::ForStatement {
            "for"
        } else {
            "say"
        }
    ));
    assert_eq!(statements[2].to_string(), "my c = 3");
}

#[test]
fn unmatched_openers_yield_to_say_and_the_following_binding() {
    for opener in ["(", "[", "{"] {
        let source = format!("my a = {opener}1\nsay: 2\nmy c = 3\n");
        check_independent_suffix(&source, 1, SyntaxKind::OperatorChain);
        let parsed = parse(&source);
        let diagnostics = parsed.syntax_diagnostics().unwrap();
        assert!(
            matches!(diagnostics[0].cause(), SyntaxDiagnosticCause::Structural(d)
            if d.message() == Some("delimiter not closed"))
        );
        assert_eq!(
            diagnostics[0].primary(),
            &(source.find('\n').unwrap()..source.find('\n').unwrap())
        );
    }
}

#[test]
fn mismatched_pairs_report_the_missing_opener_close_once() {
    for (open, close) in [
        ("(", "]"),
        ("(", "}"),
        ("[", ")"),
        ("[", "}"),
        ("{", ")"),
        ("{", "]"),
    ] {
        let source = format!("my a = {open}1 {close}\nsay: 2\nmy c = 3\n");
        check_independent_suffix(&source, 1, SyntaxKind::OperatorChain);
        let parsed = parse(&source);
        assert_eq!(
            root(&parsed)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0
        );
    }
}

#[test]
fn nested_unmatched_openers_each_report_once() {
    check_independent_suffix(
        "my a = ([{1\nsay: 2\nmy c = 3\n",
        3,
        SyntaxKind::OperatorChain,
    );
}

#[test]
fn unmatched_openers_yield_to_for_headers() {
    for opener in ["(", "[", "{"] {
        check_independent_suffix(
            &format!("my a = {opener}1\nfor x in xs: x\nmy c = 3\n"),
            1,
            SyntaxKind::ForStatement,
        );
    }
}

#[test]
fn unmatched_groups_in_a_for_header_yield_to_later_statements() {
    let parsed = parse("for x in (xs\nsay: 2\nmy c = 3\n");
    // The header also lacks its required body introducer/body.
    check_diagnostics(&parsed, 2);
    let root = root(&parsed);
    assert_eq!(
        root.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::ForStatement,
            SyntaxKind::OperatorChain,
            SyntaxKind::BindingStatement
        ],
        "{root:#?}"
    );
}

#[test]
fn nested_indentation_keeps_recovered_siblings_in_their_block() {
    let parsed = parse(
        "if ready:\n    my a = ([1\n    say: 2\n    for x in xs: x\n    my c = 3\nmy d = 4\n",
    );
    check_diagnostics(&parsed, 2);
    let root = root(&parsed);
    let say = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IdentifierExpression && node.to_string() == "say")
        .unwrap();
    assert!(!say.ancestors().any(|node| matches!(
        node.kind(),
        SyntaxKind::ParenthesizedExpression | SyntaxKind::ListExpression
    )));
    assert_eq!(root.children().last().unwrap().to_string(), "my d = 4");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::ForStatement)
            .count(),
        1
    );
}

#[test]
fn matched_outer_closers_remain_with_their_owner() {
    for source in [
        "my a = [f(1\n]\nsay: 2\nmy c = 3\n",
        "my a = [{1\n]\nsay: 2\nmy c = 3\n",
        "my a = ({1\n)\nsay: 2\nmy c = 3\n",
        "my a = {\n    my b = (1\n    say: 2\n}\nmy c = 3\n",
    ] {
        let parsed = parse(source);
        check_diagnostics(&parsed, 1);
        let root = root(&parsed);
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ExpressionDelimitedForeignClose)
        );
        assert_eq!(root.children().last().unwrap().to_string(), "my c = 3");
        assert!(root.descendants_with_tokens().any(|element| matches!(
            element.kind(),
            SyntaxKind::RParen | SyntaxKind::RBracket | SyntaxKind::RBrace
        )));
    }
}

#[test]
fn missing_field_brace_preserves_the_with_companion_and_suffix() {
    for source in [
        "struct point { x: int, y: int  with:\n    our p.norm2 = p.x * p.x + p.y * p.y\nmy c = 3\n",
        "struct point { x: int, y: int\n    with:\n        our norm = 2\nmy c = 3\n",
        "struct point { x: int, y: int\n    with { our norm = 2 }\nmy c = 3\n",
    ] {
        let parsed = parse(source);
        check_diagnostics(&parsed, 1);
        let root = root(&parsed);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::StructField)
                .count(),
            2,
            "{root:#?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::DeclarationCompanion)
                .count(),
            1,
            "{root:#?}"
        );
        assert_eq!(root.children().last().unwrap().to_string(), "my c = 3");
    }
}

#[test]
fn valid_multiline_csts_match_shapes_captured_before_t18() {
    for (source, expected) in [
        ("my xs = [\n1,\n2,\n]\n", 0x8a58923bee456292),
        (
            "my a = (\nf(\n{x = 1},\n[\n2,\n3,\n],\n),\n)\n",
            0x0cf892c4b86be183,
        ),
        (
            "my a = {\nmy b = 1\nsay: b\n}\nmy c = 3\n",
            0xd736ad218dafa233,
        ),
    ] {
        let parsed = parse(source);
        check_diagnostics(&parsed, 0);
        let shape = format!("{:#?}", root(&parsed));
        let hash = shape.bytes().fold(0xcbf29ce484222325u64, |hash, byte| {
            (hash ^ u64::from(byte)).wrapping_mul(0x100000001b3)
        });
        assert_eq!(hash, expected, "{shape}");
    }
}

#[test]
fn all_delimiter_owners_return_executable_siblings() {
    for head in [
        "type T = (int",
        "type T = { x: int",
        "type T = '[io",
        "use a::{b",
        "struct S {} with { our x = 1",
        "my a = rule { x",
    ] {
        let source = format!("{head}\nsay: 2\nmy c = 3\n");
        let parsed = parse(&source);
        check_diagnostics(&parsed, 1);
        let root = root(&parsed);
        let children: Vec<_> = root.children().collect();
        assert_eq!(children.len(), 3, "{root:#?}");
        assert_eq!(children[1].to_string(), "say: 2");
        assert_eq!(children[2].to_string(), "my c = 3");
    }
}

#[test]
fn colon_statement_resynchronization_is_independent_of_the_callee_name() {
    for head in ["emit:", "display :", "出力:"] {
        let parsed = parse(&format!("my a = (1\n{head} 2\nmy c = 3\n"));
        check_diagnostics(&parsed, 1);
        assert_eq!(
            root(&parsed).children().nth(1).unwrap().kind(),
            SyntaxKind::OperatorChain
        );
        assert_eq!(root(&parsed).children().count(), 3);
    }
}

#[test]
fn typed_prefixes_and_delimiter_mutations_remain_lossless() {
    for source in [
        "my a = ([{1\r\nsay: 2\r\nmy c = 3\r\n",
        "struct S { x: T, with:\n    our f = 2\nmy c = 3\n",
        "type T = '[io\n出力: 2\nmy c = 3\n",
    ] {
        for at in source
            .char_indices()
            .map(|(at, _)| at)
            .chain(std::iter::once(source.len()))
        {
            parse(&source[..at]);
            for inserted in ['(', '[', '{', ')', ']', '}'] {
                let mutated = format!("{}{}{}", &source[..at], inserted, &source[at..]);
                parse(&mutated);
            }
        }
    }
}

#[test]
fn matching_closers_shield_multiline_control_heads_in_every_owner() {
    for source in [
        "type T = '[\nio,\nnet,\n] int\n",
        "use a::{\nb,\nc,\n}\n",
        "struct S {} with {\nour x = 1\nsay: x\n}\n",
        "my r = rule {\nx\ny\n}\n",
        "my a = (\nif ready: 1,\n2,\n)\n",
    ] {
        check_diagnostics(&parse(source), 0);
    }
}
