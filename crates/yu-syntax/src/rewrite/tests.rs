use chasa_recover::In;
use rowan::{GreenNode, GreenNodeBuilder};

use crate::{
    SyntaxKind, SyntaxNode,
    operator::{BindingPower, OperatorDeclaration, OperatorFixities, OperatorTable},
};

use super::{
    driver::{Either, RewriteIn, TailExit, emit_end, expr, scan_operator},
    item::{OperatorUse, Payload, TokenKind, TriviaKind},
    state::Recover,
};
use crate::scan::operator::OperatorSite;

fn run(source: &str) -> (GreenNode, Option<TailExit>) {
    let operators = OperatorTable::empty();
    run_with(source, &operators)
}

fn run_with(source: &str, operators: &OperatorTable) -> (GreenNode, Option<TailExit>) {
    let mut input = source;
    let mut recover = Recover::new(operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = expr(In::new(&mut input, &mut recover, &mut builder));
    if let Some(Err(Either::Right(end))) = &exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    (builder.finish(), exit)
}

fn dynamic_operator_table() -> OperatorTable {
    OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "~",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new()
                .with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
        ),
        OperatorDeclaration::new(
            "++",
            OperatorFixities::new().with_suffix(BindingPower::scalar(80)),
        ),
        OperatorDeclaration::new("?", OperatorFixities::new().with_nullfix()),
    ])
    .expect("distinct direct rewrite operator declarations")
}

fn scan_dynamic_operator<'source>(
    source: &'source str,
    operators: &OperatorTable,
    site: OperatorSite,
) -> (Option<OperatorUse>, &'source str) {
    let mut remaining = source;
    let mut recover = Recover::new(operators);
    let operator = scan_operator(In::new(&mut remaining, &mut recover, ()), site, false, 0, 0)
        .map(|operator| operator.use_);
    (operator, remaining)
}

fn operator_chain_children(green: &GreenNode) -> Vec<SyntaxKind> {
    SyntaxNode::new_root(green.clone())
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer operator chain")
        .children()
        .map(|node| node.kind())
        .collect()
}

#[test]
fn caller_owned_builder_finishes_after_source_drops() {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = {
        let source = String::from("  αβ  ");
        let mut input = source.as_str();
        expr(In::new(&mut input, &mut recover, &mut builder))
    };
    let Some(Err(Either::Right(end))) = &exit else {
        panic!("the core expression must return EOF trivia to its outer owner")
    };
    emit_end(&mut builder, end);
    builder.finish_node();
    let green = builder.finish();
    assert_eq!(green.to_string(), "  αβ  ");
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.kind(), SyntaxKind::Root);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::IdentifierExpression)
    );
}

#[test]
fn post_core_newline_identifier_is_owned_unemitted_handoff() {
    let (green, exit) = run("a\nβ");
    assert_eq!(green.to_string(), "a");
    let Some(Err(Either::Left(item))) = exit else {
        panic!("the next item is handed to the enclosing owner")
    };
    assert_eq!(
        item.leading
            .0
            .iter()
            .map(|part| (part.kind, &*part.text))
            .collect::<Vec<_>>(),
        [(TriviaKind::Newline, "\n")]
    );
    let Payload::Token(token) = item.payload else {
        panic!("the handed item is lexical")
    };
    assert_eq!(token.kind, TokenKind::Identifier);
    assert_eq!(&*token.text, "β");
}

#[test]
fn handoff_owns_maximal_comment_trivia_without_source_borrow() {
    for (source, comment) in [
        ("a /*c*/β", "/*c*/"),
        (
            "a /* outer /* inner */ outer */β",
            "/* outer /* inner */ outer */",
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), "a");
        let Some(Err(Either::Left(item))) = exit else {
            panic!("the next item is handed to the enclosing owner")
        };
        assert_eq!(
            item.leading
                .0
                .iter()
                .map(|part| (part.kind, &*part.text))
                .collect::<Vec<_>>(),
            [
                (TriviaKind::Whitespace, " "),
                (TriviaKind::BlockComment, comment),
            ]
        );
        let Payload::Token(token) = item.payload else {
            panic!("the handed item is lexical")
        };
        assert_eq!(token.kind, TokenKind::Identifier);
        assert_eq!(&*token.text, "β");
    }
}

#[test]
fn committed_trivia_keeps_its_lexical_token_kinds() {
    let (green, _) = run("a \t// line\n/* outer /* inner */ outer */");
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Identifier, "a".to_owned()),
            (SyntaxKind::Whitespace, " \t".to_owned()),
            (SyntaxKind::LineComment, "// line".to_owned()),
            (SyntaxKind::Newline, "\n".to_owned()),
            (
                SyntaxKind::BlockComment,
                "/* outer /* inner */ outer */".to_owned(),
            ),
        ]
    );
}

#[test]
fn physical_newlines_are_owned_typed_parts_between_horizontal_runs() {
    let (green, _) = run("a \t\r\n \r\t\n  ");
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Identifier, "a".to_owned()),
            (SyntaxKind::Whitespace, " \t".to_owned()),
            (SyntaxKind::Newline, "\r\n".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Newline, "\r".to_owned()),
            (SyntaxKind::Whitespace, "\t".to_owned()),
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::Whitespace, "  ".to_owned()),
        ]
    );
}

#[test]
fn non_breaking_space_is_an_unknown_handoff_not_trivia() {
    let (green, exit) = run("a\u{a0}β");
    assert_eq!(green.to_string(), "a");
    let Some(Err(Either::Left(item))) = exit else {
        panic!("the non-breaking space is handed to the enclosing owner")
    };
    assert!(item.leading.0.is_empty());
    let Payload::Token(token) = item.payload else {
        panic!("the handed item is lexical")
    };
    assert_eq!(token.kind, TokenKind::Unknown);
    assert_eq!(&*token.text, "\u{a0}");
}

#[test]
fn words_match_the_oracle_start_and_suffix_rules() {
    for source in ["_private", "ready?"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
    }
}

#[test]
fn decimal_integer_core_keeps_its_direct_tail_chain() {
    let source = "123(a).field::name";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    assert_eq!(
        outer.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IntegerLiteral,
            SyntaxKind::CallTail,
            SyntaxKind::FieldTail,
            SyntaxKind::PathTail,
        ]
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Integer, "123".to_owned()),
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Identifier, "a".to_owned()),
            (SyntaxKind::RParen, ")".to_owned()),
            (SyntaxKind::Dot, ".".to_owned()),
            (SyntaxKind::Identifier, "field".to_owned()),
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Identifier, "name".to_owned()),
        ]
    );
}

#[test]
fn dynamic_operator_roles_append_to_the_active_flat_chain() {
    let operators = dynamic_operator_table();
    let source = "~a + b++";
    let (green, exit) = run_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer operator chain");
    assert_eq!(
        chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
            SyntaxKind::SuffixOperatorUse,
        ]
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Operator, "~".to_owned()),
            (SyntaxKind::Identifier, "a".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Operator, "+".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "b".to_owned()),
            (SyntaxKind::Operator, "++".to_owned()),
        ]
    );

    let (green, exit) = run_with("?", &operators);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::NullfixOperatorUse)
    );
}

#[test]
fn dynamic_operator_candidate_fallback_is_site_aware() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "+!",
            OperatorFixities::new()
                .with_infix(BindingPower::scalar(50), BindingPower::new(50, [1])),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "!",
            OperatorFixities::new()
                .with_prefix(BindingPower::scalar(80))
                .with_nullfix(),
        ),
    ])
    .expect("overlapping direct rewrite operator declarations");

    let (green, exit) = run_with("+!a", &operators);
    assert_eq!(green.to_string(), "+!a");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("NUD operator chain");
    assert_eq!(
        chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::IdentifierExpression,
        ]
    );

    let (green, exit) = run_with("a+!b", &operators);
    assert_eq!(green.to_string(), "a+!b");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("LED operator chain");
    assert_eq!(
        chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
        ]
    );
}

#[test]
fn dynamic_operator_raw_successor_probe_covers_value_starts_and_trivia() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new("?", OperatorFixities::new().with_nullfix()),
        OperatorDeclaration::new(
            "!",
            OperatorFixities::new().with_prefix(BindingPower::scalar(80)),
        ),
        OperatorDeclaration::new("!", OperatorFixities::new().with_nullfix()),
    ])
    .expect("value-start operator declarations");

    for source in [
        "? \"",
        "? (",
        "? [",
        "? {",
        "? $",
        "? \\",
        "? %",
        "? _",
        "? '",
        "? α",
        "? 1",
        "? .",
        "? !",
        "? // line\n  α",
        "? /* outer /* inner */ outer */ α",
        "? \r\n  α",
    ] {
        let (use_, remaining) = scan_dynamic_operator(source, &operators, OperatorSite::Nud);
        assert!(
            matches!(use_, Some(OperatorUse::Prefix(_))),
            "{source:?} must select Prefix from raw successor evidence"
        );
        assert_eq!(remaining, source.strip_prefix('?').unwrap());
    }

    for source in ["? ", "? /* unterminated"] {
        let (use_, remaining) = scan_dynamic_operator(source, &operators, OperatorSite::Nud);
        assert_eq!(use_, Some(OperatorUse::Nullfix), "{source:?}");
        assert_eq!(remaining, source.strip_prefix('?').unwrap());
    }
}

#[test]
fn dynamic_operator_raw_rejection_keeps_outer_input_and_builder_unchanged() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new("?", OperatorFixities::new().with_nullfix()),
    ])
    .expect("call-sensitive operator declaration");
    let mut input = "?(a)";
    let start = input.as_ptr();
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let scanned = {
        let mut outer: RewriteIn = In::new(&mut input, &mut recover, &mut builder);
        outer.token(|lex| scan_operator(lex, OperatorSite::Nud, false, 0, 0))
    };
    assert!(scanned.is_none());
    assert_eq!(input.as_ptr(), start);
    assert_eq!(input, "?(a)");
    assert!(std::ptr::eq(recover.operators(), &operators));
    builder.finish_node();
    assert_eq!(builder.finish().to_string(), "");
}

#[test]
fn dynamic_operator_multibyte_boundary_falls_back_to_the_shorter_spelling() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "!α",
            OperatorFixities::new()
                .with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
        ),
        OperatorDeclaration::new(
            "!",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
    ])
    .expect("overlapping multibyte operator declarations");

    let (use_, remaining) = scan_dynamic_operator("!αx", &operators, OperatorSite::Nud);
    assert!(matches!(use_, Some(OperatorUse::Prefix(_))));
    assert_eq!(remaining, "αx");
}

#[test]
fn dynamic_operator_no_value_selects_the_without_value_fixity() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "@",
        OperatorFixities::new()
            .with_infix(BindingPower::scalar(40), BindingPower::scalar(40))
            .with_suffix(BindingPower::scalar(70)),
    )])
    .expect("infix-suffix operator declaration");

    let (use_, remaining) = scan_dynamic_operator("@#", &operators, OperatorSite::Led);
    assert!(matches!(use_, Some(OperatorUse::Suffix(_))));
    assert_eq!(remaining, "#");

    let (use_, remaining) = scan_dynamic_operator("@b", &operators, OperatorSite::Led);
    assert!(matches!(use_, Some(OperatorUse::Infix { .. })));
    assert_eq!(remaining, "b");
}

#[test]
fn dynamic_operator_prefix_nullfix_and_call_colon_controls_stay_lexical() {
    let call_sensitive = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new("?", OperatorFixities::new().with_nullfix()),
    ])
    .expect("one call-sensitive operator declaration");

    let (green, exit) = run_with("? a", &call_sensitive);
    assert_eq!(green.to_string(), "? a");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
    );

    for source in ["?(a)", "?:a"] {
        let (green, exit) = run_with(source, &call_sensitive);
        assert_eq!(green.to_string(), "");
        assert_eq!(exit, None);
    }

    let mixed = OperatorTable::from_declarations([OperatorDeclaration::new(
        "?",
        OperatorFixities::new()
            .with_prefix(BindingPower::scalar(70))
            .with_infix(BindingPower::scalar(40), BindingPower::new(40, [1]))
            .with_nullfix(),
    )])
    .expect("mixed-fixity operator declaration");
    let (green, exit) = run_with("?(a)", &mixed);
    assert_eq!(green.to_string(), "?(a)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
    );
}

#[test]
fn dynamic_operator_uses_delimited_baseline_and_matching_stop() {
    let infix = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
    )])
    .expect("one infix operator declaration");
    let (green, exit) = run_with("(\n  a +\n    b)", &infix);
    assert_eq!(green.to_string(), "(\n  a +\n    b)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let (green, exit) = run_with("(a +\nb)", &infix);
    assert_eq!(green.to_string(), "(a");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    let suffix_or_nullfix = OperatorTable::from_declarations([OperatorDeclaration::new(
        "~",
        OperatorFixities::new()
            .with_suffix(BindingPower::scalar(70))
            .with_nullfix(),
    )])
    .expect("one suffix-nullfix operator declaration");
    let (green, exit) = run_with("(a~)", &suffix_or_nullfix);
    assert_eq!(green.to_string(), "(a~)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::SuffixOperatorUse)
    );
}

#[test]
fn dynamic_operator_honours_every_delimited_active_stop() {
    let suffix_or_nullfix = OperatorTable::from_declarations([OperatorDeclaration::new(
        "~",
        OperatorFixities::new()
            .with_suffix(BindingPower::scalar(70))
            .with_nullfix(),
    )])
    .expect("suffix-nullfix operator declaration");

    for source in ["(a~,b)", "(a~;b)", "a[b~]", "a.{a~}"] {
        let (green, exit) = run_with(source, &suffix_or_nullfix);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::SuffixOperatorUse),
            "{source:?} must select the suffix at its active stop"
        );
    }
}

#[test]
fn dynamic_operator_lower_bp_handoff_preserves_trivia_and_flat_output() {
    let outer = OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(10), BindingPower::scalar(50)),
    );
    let lower = OperatorDeclaration::new(
        "*",
        OperatorFixities::new().with_infix(BindingPower::scalar(20), BindingPower::scalar(20)),
    );
    let higher = OperatorDeclaration::new(
        "*",
        OperatorFixities::new().with_infix(BindingPower::scalar(60), BindingPower::scalar(60)),
    );
    let source = "a + b /* carry */ * c";

    let handoff = OperatorTable::from_declarations([outer.clone(), lower])
        .expect("lower binding-power table");
    let accepted =
        OperatorTable::from_declarations([outer, higher]).expect("higher binding-power table");
    let (handoff_green, handoff_exit) = run_with(source, &handoff);
    let (accepted_green, accepted_exit) = run_with(source, &accepted);

    assert_eq!(handoff_green.to_string(), source);
    assert_eq!(accepted_green.to_string(), source);
    assert!(matches!(handoff_exit, Some(Err(Either::Right(_)))));
    assert!(matches!(accepted_exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&handoff_green),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
        ]
    );
    assert_eq!(
        operator_chain_children(&handoff_green),
        operator_chain_children(&accepted_green),
        "only binding powers differ; flat CST stays fixed"
    );
    assert!(
        SyntaxNode::new_root(handoff_green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::BlockComment && token.text() == "/* carry */")
    );
}

#[test]
fn parenthesized_primary_owns_its_sequence_and_outer_ml_tail() {
    let source = "(a,b;c) d";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let group = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
        .expect("parenthesized primary");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        3
    );
    assert_eq!(
        outer
            .children()
            .filter(|node| node.kind() == SyntaxKind::MlArgument)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::LParen,
            SyntaxKind::Identifier,
            SyntaxKind::Comma,
            SyntaxKind::Identifier,
            SyntaxKind::Semicolon,
            SyntaxKind::Identifier,
            SyntaxKind::RParen,
            SyntaxKind::Whitespace,
            SyntaxKind::Identifier,
        ]
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn call_and_index_own_valid_multiple_item_sequences() {
    let source = "f(a,b;c)[x,y;z]";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let call = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::CallTail)
        .expect("call tail");
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        3
    );
    let index = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("index tail");
    assert_eq!(
        index
            .children()
            .filter(|node| node.kind() == SyntaxKind::IndexItem)
            .count(),
        3
    );
    let rparen = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RParen)
        .expect("call close");
    assert_eq!(
        rparen.parent().expect("call close owner").kind(),
        SyntaxKind::CallTail
    );
    let rbracket = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RBracket)
        .expect("index close");
    assert_eq!(
        rbracket.parent().expect("index close owner").kind(),
        SyntaxKind::IndexTail
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn each_delimited_owner_accepts_an_empty_valid_sequence() {
    for (source, owner) in [
        ("()", SyntaxKind::ParenthesizedExpression),
        ("f()", SyntaxKind::CallTail),
        ("x[]", SyntaxKind::IndexTail),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let node = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            node.children()
                .filter(|node| matches!(
                    node.kind(),
                    SyntaxKind::OperatorChain | SyntaxKind::IndexItem
                ))
                .count(),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn fixed_field_and_path_tails_keep_their_own_tokens() {
    let source = "a .field:: name b";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    assert_eq!(
        outer.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::FieldTail,
            SyntaxKind::PathTail,
            SyntaxKind::MlArgument,
        ]
    );
    let field = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::FieldTail)
        .expect("field tail");
    assert_eq!(
        field
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Dot, ".".to_owned()),
            (SyntaxKind::Identifier, "field".to_owned()),
        ]
    );
    let path = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::PathTail)
        .expect("path tail");
    assert_eq!(
        path.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "name".to_owned()),
        ]
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn double_dot_is_not_a_field_tail() {
    for source in ["a..", "a..."] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), "a", "{source:?}");
        assert!(
            matches!(
                exit,
                Some(Err(Either::Left(item)))
                    if matches!(item.payload, Payload::Token(ref token)
                        if token.kind == TokenKind::Unknown && &*token.text == ".")
            ),
            "{source:?}"
        );
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::FieldTail),
            "{source:?}"
        );
    }
}

#[test]
fn dot_projections_precede_field_dispatch_and_own_their_closes() {
    let source = "a.(x,y).{left,right}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    assert_eq!(
        outer.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::ProjectionRecordTail,
        ]
    );
    for (kind, close, expected_items) in [
        (SyntaxKind::ProjectionTupleTail, SyntaxKind::RParen, 2),
        (SyntaxKind::ProjectionRecordTail, SyntaxKind::RBrace, 2),
    ] {
        let projection = outer
            .children()
            .find(|node| node.kind() == kind)
            .expect("projection tail");
        assert_eq!(
            projection
                .children()
                .filter(|node| node.kind() == SyntaxKind::OperatorChain)
                .count(),
            expected_items
        );
        let close = projection
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == close)
            .expect("projection close");
        assert_eq!(close.parent().expect("close owner").kind(), kind);
    }
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn index_item_accepts_ml_argument_without_separator_recovery() {
    let (green, exit) = run("x[a b]");
    assert_eq!(green.to_string(), "x[a b]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let indexes = outer_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::IndexTail)
        .collect::<Vec<_>>();
    assert_eq!(indexes.len(), 1);
    let items = indexes[0]
        .children()
        .filter(|node| node.kind() == SyntaxKind::IndexItem)
        .collect::<Vec<_>>();
    assert_eq!(items.len(), 1);
    let item_chain = items[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("the index item owns its expression chain");
    let ml_arguments = item_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(ml_arguments.len(), 1);
    let argument_chain = ml_arguments[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("the ML argument owns its expression chain");
    assert_eq!(
        argument_chain
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        [" ", "b"]
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Identifier,
            SyntaxKind::LBracket,
            SyntaxKind::Identifier,
            SyntaxKind::Whitespace,
            SyntaxKind::Identifier,
            SyntaxKind::RBracket,
        ]
    );
    let rbracket = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RBracket)
        .expect("index close");
    assert_eq!(
        rbracket.parent().expect("index close owner").kind(),
        SyntaxKind::IndexTail
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn index_item_multiple_ml_arguments_stay_siblings() {
    let (green, exit) = run("x[a b c]");
    assert_eq!(green.to_string(), "x[a b c]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let index = outer_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("outer index tail");
    let item_chain = index
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexItem)
        .and_then(|item| {
            item.children()
                .find(|node| node.kind() == SyntaxKind::OperatorChain)
        })
        .expect("the index item owns its expression chain");
    let arguments = item_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(arguments.len(), 2);
    for argument in arguments {
        assert!(
            !argument
                .descendants()
                .skip(1)
                .any(|node| node.kind() == SyntaxKind::MlArgument)
        );
    }
}

#[test]
fn index_item_ml_child_keeps_its_continuation_after_call() {
    let (green, exit) = run("x[a b(c) d]");
    assert_eq!(green.to_string(), "x[a b(c) d]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let index = outer_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("outer index tail");
    let item_chain = index
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexItem)
        .and_then(|item| {
            item.children()
                .find(|node| node.kind() == SyntaxKind::OperatorChain)
        })
        .expect("the index item owns its expression chain");
    let arguments = item_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(arguments.len(), 2);
    assert!(
        arguments[0]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::CallTail)
    );
    for argument in arguments {
        assert!(
            !argument
                .descendants()
                .skip(1)
                .any(|node| node.kind() == SyntaxKind::MlArgument)
        );
    }
}

#[test]
fn index_item_nested_call_keeps_close_owner_control() {
    let (green, exit) = run("x[a(b)]");
    assert_eq!(green.to_string(), "x[a(b)]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let index = outer_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("outer index tail");
    let items = index
        .children()
        .filter(|node| node.kind() == SyntaxKind::IndexItem)
        .collect::<Vec<_>>();
    assert_eq!(items.len(), 1);
    let item_chain = items[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("the index item owns its expression chain");
    let call = item_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::CallTail)
        .expect("the index expression owns its nested call tail");
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Identifier,
            SyntaxKind::LBracket,
            SyntaxKind::Identifier,
            SyntaxKind::LParen,
            SyntaxKind::Identifier,
            SyntaxKind::RParen,
            SyntaxKind::RBracket,
        ]
    );
    let rparen = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RParen)
        .expect("call close");
    assert_eq!(
        rparen.parent().expect("call close owner").kind(),
        SyntaxKind::CallTail
    );
    let rbracket = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RBracket)
        .expect("index close");
    assert_eq!(
        rbracket.parent().expect("index close owner").kind(),
        SyntaxKind::IndexTail
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}
