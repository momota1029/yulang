use super::*;
use crate::rewrite::{
    item::{
        Boundary, ForeignSplit, Item, LeadingTrivia, Payload, PendingBoundary, StopKind, Token,
        Trivia,
    },
    rule::{
        RuleWitnessExit, rule_body_witness, scan_rule_introducer_successor_witness,
        scan_rule_item_witness,
    },
    yumark::{FenceBoundary, FenceOpener, FencePrefixPolicy, QuoteTransitionKind},
};
use reborrow_generic::Reborrow as _;

fn run_rule_body<'source>(source: &'source str) -> (GreenNode, RuleWitnessExit, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let mut lex = In::new(&mut input, &mut recover, ());
    let opener = scan_rule_item_witness(lex.rb()).expect("RuleBody opener");
    let current = scan_rule_item_witness(lex).expect("first RuleBody current Item");

    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = rule_body_witness(
        In::new(&mut input, &mut recover, &mut builder),
        opener,
        current,
    );
    builder.finish_node();
    (builder.finish(), exit, input)
}

fn run_rule_body_with<'source>(
    source: &'source str,
    current: Item,
) -> (GreenNode, RuleWitnessExit, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = rule_body_witness(
        In::new(&mut input, &mut recover, &mut builder),
        token_item(TokenKind::LBrace, "{"),
        current,
    );
    builder.finish_node();
    (builder.finish(), exit, input)
}

fn token_item(kind: TokenKind, text: &str) -> Item {
    Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind,
            text: text.into(),
        }),
    )
}

fn active_fence(depth: usize) -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth, base: 0 },
        close_column: 0,
    }
}

fn plain_fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::None,
        close_column: 0,
    }
}

fn root(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
}

fn count(green: &GreenNode, kind: SyntaxKind) -> usize {
    root(green)
        .descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn tokens(green: &GreenNode) -> Vec<(SyntaxKind, String)> {
    root(green)
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .map(|token| (token.kind(), token.text().to_owned()))
        .collect()
}

fn returned(exit: RuleWitnessExit) -> Item {
    match exit {
        RuleWitnessExit::Returned(item) | RuleWitnessExit::Deferred(item) => item,
        RuleWitnessExit::Complete => panic!("expected an unconsumed current Item"),
    }
}

#[test]
fn body_and_parenthesis_alternations_own_all_branches_and_separators() {
    for (source, sequences, pipes, newlines) in [
        ("{}", 1, 0, 0),
        ("{a|}", 2, 1, 0),
        ("{a||b}", 3, 2, 0),
        ("{a\n\nb}", 3, 0, 2),
    ] {
        let (green, exit, remainder) = run_rule_body(source);
        assert_eq!(exit, RuleWitnessExit::Complete, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(count(&green, SyntaxKind::RuleBody), 1, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::RuleAlternation), 1, "{source:?}");
        assert_eq!(
            count(&green, SyntaxKind::RuleSequence),
            sequences,
            "{source:?}"
        );
        assert_eq!(
            tokens(&green)
                .iter()
                .filter(|(kind, _)| *kind == SyntaxKind::Pipe)
                .count(),
            pipes,
            "{source:?}"
        );
        assert_eq!(
            tokens(&green)
                .iter()
                .filter(|(kind, _)| *kind == SyntaxKind::Newline)
                .count(),
            newlines,
            "{source:?}"
        );
        assert_eq!(count(&green, SyntaxKind::Missing), 0, "{source:?}");
    }

    let (green, exit, _) = run_rule_body("{(a,b||)}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(count(&green, SyntaxKind::RuleAlternation), 2);
    assert_eq!(count(&green, SyntaxKind::RuleSequence), 5);
    let parenthesized = root(&green)
        .descendants()
        .find(|node| {
            node.kind() == SyntaxKind::RuleItem
                && node
                    .first_token()
                    .is_some_and(|token| token.kind() == SyntaxKind::LParen)
        })
        .expect("parenthesized RuleItem");
    assert_eq!(
        parenthesized.first_token().unwrap().kind(),
        SyntaxKind::LParen
    );
    assert_eq!(
        parenthesized.last_token().unwrap().kind(),
        SyntaxKind::RParen
    );
    assert_eq!(count(&green, SyntaxKind::Missing), 0);
}

#[test]
fn rule_core_accepts_unicode_sigils_integer_range_and_never_identifier_suffixes() {
    let (green, exit, remainder) = run_rule_body("{α $β &γ _δ 'ε _ 123 .. a? b!}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(remainder, "");
    assert_eq!(count(&green, SyntaxKind::RuleItem), 10);
    assert_eq!(count(&green, SyntaxKind::RuleQuantifier), 1);
    assert!(tokens(&green).contains(&(SyntaxKind::RuleQuantifierToken, "?".to_owned())));
    assert_eq!(count(&green, SyntaxKind::Error), 1);
    assert_eq!(
        tokens(&green)
            .into_iter()
            .filter(|(kind, _)| *kind == SyntaxKind::SigilIdentifier)
            .map(|(_, text)| text)
            .collect::<Vec<_>>(),
        ["$β", "&γ", "_δ", "'ε"]
    );
}

#[test]
fn every_bare_rule_stop_keyword_returns_unchanged() {
    for keyword in ["do", "if", "else", "case", "catch", "rule"] {
        let source = format!("{{{keyword}}}");
        let (green, exit, remainder) = run_rule_body(&source);
        let item = returned(exit);
        assert_eq!(
            item,
            token_item(TokenKind::Identifier, keyword),
            "{keyword}"
        );
        assert_eq!(remainder, "}", "{keyword}");
        assert_eq!(count(&green, SyntaxKind::Missing), 1, "{keyword}");
        assert!(!root(&green).to_string().contains(keyword), "{keyword}");
    }
}

#[test]
fn all_rule_quantifiers_are_one_dedicated_token() {
    for quantifier in ["*", "+", "?", "*?", "+?"] {
        let source = format!("{{a{quantifier}}}");
        let (green, exit, _) = run_rule_body(&source);
        assert_eq!(exit, RuleWitnessExit::Complete, "{quantifier}");
        assert_eq!(count(&green, SyntaxKind::RuleQuantifier), 1, "{quantifier}");
        assert_eq!(
            tokens(&green)
                .into_iter()
                .filter(|(kind, _)| *kind == SyntaxKind::RuleQuantifierToken)
                .collect::<Vec<_>>(),
            [(SyntaxKind::RuleQuantifierToken, quantifier.to_owned())]
        );
    }
}

#[test]
fn capture_is_terminal_and_owns_the_full_postfixed_rhs_item() {
    let (green, exit, _) = run_rule_body("{left=right*?.field::Path next}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(count(&green, SyntaxKind::RuleCapture), 1);
    assert_eq!(count(&green, SyntaxKind::RuleQuantifier), 1);
    assert_eq!(count(&green, SyntaxKind::RuleField), 1);
    assert_eq!(count(&green, SyntaxKind::RulePath), 1);

    let capture = root(&green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::RuleCapture)
        .expect("capture owner");
    assert_eq!(
        capture
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::RuleItem)
            .count(),
        1
    );
    assert!(!capture.text().to_string().contains("next"));
}

#[test]
fn field_and_path_recover_at_their_immediate_owner() {
    let (green, exit, _) = run_rule_body("{a.field::Path}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(count(&green, SyntaxKind::RuleField), 1);
    assert_eq!(count(&green, SyntaxKind::RulePath), 1);
    assert_eq!(count(&green, SyntaxKind::Missing), 0);

    let (green, exit, _) = run_rule_body("{a.}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    let field = root(&green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::RuleField)
        .unwrap();
    assert_eq!(
        field
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit, _) = run_rule_body("{a:: /*tail*/");
    let eof = returned(exit);
    assert!(matches!(eof.payload, Payload::Eof));
    assert_eq!(
        eof.leading
            .0
            .iter()
            .map(|trivia| &*trivia.text)
            .collect::<Vec<_>>(),
        [" ", "/*tail*/"]
    );
    assert!(!root(&green).to_string().contains("/*tail*/"));
    assert_eq!(count(&green, SyntaxKind::Missing), 2);

    let (green, exit, _) = run_rule_body("{a.@*}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(count(&green, SyntaxKind::Error), 1);
    assert_eq!(count(&green, SyntaxKind::Missing), 0);
    assert_eq!(count(&green, SyntaxKind::RuleQuantifier), 1);
}

#[test]
fn only_capture_survives_inline_non_newline_trivia() {
    let (green, exit, _) = run_rule_body("{a .f b ::P c * d = e}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(count(&green, SyntaxKind::RuleField), 0);
    assert_eq!(count(&green, SyntaxKind::RulePath), 0);
    assert_eq!(count(&green, SyntaxKind::RuleQuantifier), 0);
    assert_eq!(count(&green, SyntaxKind::RuleCapture), 1);
    assert_eq!(count(&green, SyntaxKind::Error), 3);
}

#[test]
fn nested_parentheses_consume_only_matching_close_and_recover_outer_close() {
    let (green, exit, _) = run_rule_body("{((a|b),c)}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(count(&green, SyntaxKind::RuleAlternation), 3);
    assert_eq!(count(&green, SyntaxKind::Missing), 0);

    let (green, exit, remainder) = run_rule_body("{(a}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(remainder, "");
    assert_eq!(count(&green, SyntaxKind::Missing), 1);
    let missing_parent = root(&green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Missing)
        .unwrap()
        .parent()
        .unwrap();
    assert_eq!(missing_parent.kind(), SyntaxKind::RuleItem);
}

#[test]
fn non_core_successors_return_exact_item_and_live_suffix() {
    for (source, expected_kind, expected_text, expected_suffix) in [
        ("{\"x}", TokenKind::Unknown, "\"", "x}"),
        ("{[x]}", TokenKind::LBracket, "[", "x]}"),
        ("{a(x)}", TokenKind::LParen, "(", "x)}"),
        ("{a[x]}", TokenKind::LBracket, "[", "x]}"),
    ] {
        let source_start = source.as_ptr();
        let (green, exit, remainder) = run_rule_body(source);
        let item = returned(exit);
        assert_eq!(item, token_item(expected_kind, expected_text), "{source:?}");
        assert_eq!(remainder, expected_suffix, "{source:?}");
        let offset = source.len() - expected_suffix.len();
        assert_eq!(
            remainder.as_ptr(),
            source_start.wrapping_add(offset),
            "{source:?}"
        );
        assert_eq!(count(&green, SyntaxKind::Missing), 0, "{source:?}");
    }
}

#[test]
fn unexpected_items_are_one_item_errors_without_host_pratt_or_ml_nodes() {
    for (source, malformed) in [("{a-b c}", "-"), ("{a==b}", "=="), ("{a->>b}", "->>")] {
        let (green, exit, _) = run_rule_body(source);
        assert_eq!(exit, RuleWitnessExit::Complete, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::OperatorChain), 0, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::RuleCall), 0, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::RuleIndex), 0, "{source:?}");
        let error = root(&green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("one malformed operator Error");
        assert_eq!(error.text().to_string(), malformed, "{source:?}");
    }

    let (green, exit, _) = run_rule_body("{a=b}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(count(&green, SyntaxKind::RuleCapture), 1);
    assert_eq!(count(&green, SyntaxKind::Error), 0);
}

#[test]
fn capture_and_body_missing_preserve_eof_or_boundary_trivia() {
    let boundary = Item::plain(
        LeadingTrivia(
            vec![Trivia {
                kind: TriviaKind::Whitespace,
                text: "  ".into(),
            }]
            .into_boxed_slice(),
        ),
        Payload::Boundary(PendingBoundary::new(
            90..91,
            Boundary::Stop(StopKind::YumarkFence(Box::new(
                crate::rewrite::yumark::YumarkFenceTransition {
                    line: 90,
                    expected_depth: 2,
                    expected_base: 0,
                    indentation: 90..90,
                    observed: None,
                    kind: QuoteTransitionKind::NonPrefix,
                    inspected: 90..91,
                },
            ))),
        )),
    );
    let (green, exit, _) = run_rule_body_with("", boundary);
    let boundary = returned(exit);
    assert_eq!(boundary.leading.0[0].text.as_ref(), "  ");
    assert!(matches!(boundary.payload, Payload::Boundary(_)));
    assert_eq!(root(&green).to_string(), "{");
    assert_eq!(count(&green, SyntaxKind::Missing), 1);

    let (green, exit, _) = run_rule_body("{a= /*eof*/");
    let eof = returned(exit);
    assert!(matches!(eof.payload, Payload::Eof));
    assert_eq!(eof.leading.0.len(), 2);
    assert!(!root(&green).to_string().contains("/*eof*/"));
    assert_eq!(count(&green, SyntaxKind::Missing), 2);
}

#[test]
fn introducer_trivia_is_one_fence_aware_successor_item() {
    for source in ["\n{}", " /*comment*/ {}"] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new(&operators);
        let mut input = source;
        let item = scan_rule_introducer_successor_witness(
            In::new(&mut input, &mut recover, ()),
            4,
            &plain_fence(),
        );
        assert!(
            matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::LBrace)
        );
        assert_eq!(input, "}");
        assert_eq!(item.fragments(), None);
    }

    let source = "\n> > {}";
    let start = source.as_ptr();
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let item = scan_rule_introducer_successor_witness(
        In::new(&mut input, &mut recover, ()),
        4,
        &active_fence(2),
    );
    assert!(matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::LBrace));
    assert_eq!(input, "}");
    assert_eq!(input.as_ptr(), start.wrapping_add(source.len() - 1));
    let fragments = item.fragments().expect("accepted quote-prefix carrier");
    assert_eq!(fragments.foreign(), &[ForeignSplit::quote_prefix(5, 4)]);

    let source = "\n> stop\n";
    let start = source.as_ptr();
    let mut input = source;
    let item = scan_rule_introducer_successor_witness(
        In::new(&mut input, &mut recover, ()),
        4,
        &active_fence(2),
    );
    assert!(matches!(item.payload, Payload::Boundary(_)));
    assert_eq!(input, "> stop\n");
    assert_eq!(input.as_ptr(), start.wrapping_add(1));
    assert_eq!(item.fragments(), None);
}

#[test]
fn segmented_introducer_opener_enters_rule_body_once_in_physical_order() {
    let source = "\n> > {}tail";
    let start = source.as_ptr();
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let mut lex = In::new(&mut input, &mut recover, ());
    let opener = scan_rule_introducer_successor_witness(lex.rb(), 4, &active_fence(2));
    assert_eq!(
        opener
            .fragments()
            .expect("accepted quote-prefix carrier")
            .foreign(),
        &[ForeignSplit::quote_prefix(5, 4)]
    );
    let current = scan_rule_item_witness(lex).expect("RuleBody current Item");
    let suffix_before_body = input;
    let suffix_pointer_before_body = input.as_ptr();

    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = rule_body_witness(
        In::new(&mut input, &mut recover, &mut builder),
        opener,
        current,
    );
    builder.finish_node();
    let green = builder.finish();

    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(input, suffix_before_body);
    assert_eq!(input.as_ptr(), suffix_pointer_before_body);
    assert_eq!(input, "tail");
    assert_eq!(
        input.as_ptr(),
        start.wrapping_add(source.len() - input.len())
    );
    assert_eq!(
        tokens(&green),
        [
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::LBrace, "{".to_owned()),
            (SyntaxKind::RBrace, "}".to_owned()),
        ]
    );
}

#[test]
fn introducer_block_comment_reuses_fence_scanner_and_carrier() {
    let source = " /*x\r\n> > y*/ {}";
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let item = scan_rule_introducer_successor_witness(
        In::new(&mut input, &mut recover, ()),
        20,
        &active_fence(2),
    );
    assert!(matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::LBrace));
    assert_eq!(input, "}");
    assert_eq!(item.fragments().unwrap().foreign().len(), 1);
    assert_eq!(
        item.leading
            .0
            .iter()
            .map(|trivia| &*trivia.text)
            .collect::<Vec<_>>(),
        [" ", "/*x\r\n> > y*/", " "]
    );
}
