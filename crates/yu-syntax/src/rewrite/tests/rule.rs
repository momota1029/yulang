use super::*;
use crate::rewrite::{
    item::{Boundary, Item, LeadingTrivia, Payload, PendingBoundary, StopKind, Token},
    rule::{
        RuleWitnessExit, expression_list_handoff_witness, rule_body_witness,
        scan_rule_introducer_successor_witness, scan_rule_item_witness,
    },
    yumark::{FenceBoundary, FenceOpener, FencePrefixPolicy, QuoteTransitionKind},
};
use reborrow_generic::Reborrow as _;

fn run_rule_body<'source>(source: &'source str) -> (GreenNode, RuleWitnessExit, &'source str) {
    run_rule_body_fenced(source, 0, &plain_fence())
}

fn run_rule_body_fenced<'source>(
    source: &'source str,
    source_origin: usize,
    fence: &FenceBoundary,
) -> (GreenNode, RuleWitnessExit, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let mut lex = In::new(&mut input, &mut recover, ());
    let opener = scan_rule_item_witness(lex.rb()).expect("RuleBody opener");
    let current = scan_rule_item_witness(lex).expect("first RuleBody current Item");
    let origin = source_origin + source.len() - input.len();

    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = rule_body_witness(
        In::new(&mut input, &mut recover, &mut builder),
        opener,
        current,
        origin,
        fence,
    );
    builder.finish_node();
    (builder.finish(), exit, input)
}

fn run_rule_body_with<'source>(
    source: &'source str,
    current: Item,
    origin: usize,
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
        origin,
        &plain_fence(),
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

fn expected_boundary_item(
    suffix: &str,
    coordinate: usize,
    fence: &FenceBoundary,
    leading: &[(&str, TriviaKind)],
) -> Item {
    let crate::rewrite::yumark::FenceLineDecision::Boundary(pending) =
        crate::rewrite::yumark::judge_fence_line(suffix, coordinate, fence)
    else {
        panic!("the control suffix must be a fence boundary")
    };
    Item::plain(
        LeadingTrivia::ordinary(
            leading
                .iter()
                .map(|(text, kind)| ordinary_trivia(*kind, *text))
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        ),
        Payload::Boundary(pending),
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
    let mut eof = returned(exit);
    assert!(eof.payload_view().is_eof());
    assert_eq!(
        emit_pending_leading_tokens(&mut eof),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::BlockComment, "/*tail*/".to_owned()),
        ]
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
fn l5_rule_atoms_and_argument_tails_take_over_the_l4_deferred_positions() {
    for (source, literal, calls, indices) in [
        ("{\"x\"}", 1, 0, 0),
        ("{\"x\" \"y\"}", 2, 0, 0),
        ("{[x]}", 0, 0, 0),
        ("{a(x)}", 0, 1, 0),
        ("{a[x]}", 0, 0, 1),
    ] {
        let (green, exit, remainder) = run_rule_body(source);
        assert_eq!(exit, RuleWitnessExit::Complete, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(
            count(&green, SyntaxKind::StringLiteral),
            literal,
            "{source:?}"
        );
        assert_eq!(count(&green, SyntaxKind::RuleCall), calls, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::RuleIndex), indices, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::Missing), 0, "{source:?}");
        if literal == 1 {
            let string = root(&green)
                .descendants()
                .find(|node| node.kind() == SyntaxKind::StringLiteral)
                .unwrap();
            assert_eq!(string.parent().unwrap().kind(), SyntaxKind::RuleItem);
        }
    }
}

#[test]
fn nested_string_interpolation_stays_an_exact_later_gate_handoff() {
    let source = "{\"text%{x}\"}";
    let start = source.as_ptr();
    let (green, exit, remainder) = run_rule_body(source);
    let item = returned(exit);
    assert_eq!(item, token_item(TokenKind::Unknown, "%"));
    assert_eq!(remainder, "{x}\"}");
    assert_eq!(
        remainder.as_ptr(),
        start.wrapping_add(source.len() - remainder.len())
    );
    assert_eq!(count(&green, SyntaxKind::StringInterpolation), 0);
}

#[test]
fn expression_lists_own_commas_newlines_and_local_item_recovery() {
    let source = "{[a,b] call(1,2\n3,) index[3]}";
    let (green, exit, remainder) = run_rule_body(source);
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(remainder, "");
    assert_eq!(count(&green, SyntaxKind::RuleCall), 1);
    assert_eq!(count(&green, SyntaxKind::RuleIndex), 1);
    assert_eq!(count(&green, SyntaxKind::OperatorChain), 6);
    assert_eq!(count(&green, SyntaxKind::Missing), 0);
    assert!(tokens(&green).contains(&(SyntaxKind::Newline, "\n".to_owned())));

    let (green, exit, _) = run_rule_body("{a(1,,@,2)}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(count(&green, SyntaxKind::Missing), 2);
    assert_eq!(count(&green, SyntaxKind::Error), 1);
}

#[test]
fn expression_list_partial_leading_repeats_missing_newline_order_and_finishes_cleanly() {
    let source = "{a(1\n\n2)}";
    let (green, exit, remainder) = run_rule_body(source);
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(remainder, "");
    assert_eq!(green.to_string(), source);
    assert_eq!(count(&green, SyntaxKind::RuleCall), 1);
    assert_eq!(count(&green, SyntaxKind::Missing), 1);

    let order = root(&green)
        .descendants_with_tokens()
        .filter_map(|element| match element {
            rowan::NodeOrToken::Node(node) if node.kind() == SyntaxKind::Missing => {
                Some("missing".to_owned())
            }
            rowan::NodeOrToken::Token(token) if token.kind() == SyntaxKind::Integer => {
                Some(token.text().to_owned())
            }
            rowan::NodeOrToken::Token(token) if token.kind() == SyntaxKind::Newline => {
                Some("newline".to_owned())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(order, ["1", "newline", "missing", "newline", "2"]);
}

#[test]
fn expression_list_errors_do_not_satisfy_a_required_expression_slot() {
    for (source, malformed, errors) in [("{a(@x)}", "@", 1), ("{a(@@x)}", "@@", 2)] {
        let (green, exit, remainder) = run_rule_body(source);
        assert_eq!(exit, RuleWitnessExit::Complete, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(count(&green, SyntaxKind::Error), errors, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::OperatorChain), 1, "{source:?}");
        let recovered = root(&green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<String>();
        assert_eq!(recovered, malformed, "{source:?}");
        assert!(tokens(&green).contains(&(SyntaxKind::Identifier, "x".to_owned())));
    }

    for source in ["{a(@,x)}", "{a(@)}", "{a(@\n)}"] {
        let (green, exit, remainder) = run_rule_body(source);
        assert_eq!(exit, RuleWitnessExit::Complete, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(count(&green, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::Missing), 1, "{source:?}");
        let recovery = root(&green)
            .descendants()
            .filter_map(|node| match node.kind() {
                SyntaxKind::Error => Some(SyntaxKind::Error),
                SyntaxKind::Missing => Some(SyntaxKind::Missing),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            recovery,
            [SyntaxKind::Error, SyntaxKind::Missing],
            "{source:?}"
        );
    }
}

#[test]
fn rule_atom_string_uses_the_immediate_origin_and_real_fence() {
    let source_origin = 40;
    let fence = active_fence(2);
    for boundary_line in ["> > ```\r\n", "> stop\r\n"] {
        let source = format!("{{\"α\r\n> > β\"\r\n{boundary_line}");
        let boundary_offset = source.len() - boundary_line.len();
        let start = source.as_ptr();
        let (green, exit, remainder) = run_rule_body_fenced(&source, source_origin, &fence);
        let pending = returned(exit);
        assert_eq!(remainder, boundary_line, "{boundary_line:?}");
        assert_eq!(
            remainder.as_ptr(),
            start.wrapping_add(boundary_offset),
            "{boundary_line:?}"
        );
        assert_eq!(
            pending,
            expected_boundary_item(boundary_line, source_origin + boundary_offset, &fence, &[],),
            "{boundary_line:?}"
        );
        assert_eq!(count(&green, SyntaxKind::StringLiteral), 1);
        assert_eq!(count(&green, SyntaxKind::Missing), 1);
        assert_eq!(
            tokens(&green)
                .iter()
                .filter(|(kind, _)| *kind == SyntaxKind::YmQuotePrefix)
                .map(|(_, text)| text.as_str())
                .collect::<Vec<_>>(),
            ["> > "]
        );
        assert!(root(&green).to_string().contains("α\r\n> > β\"\r\n"));
    }

    let source = "{a\r\n> > \"β\"\r\n> stop\r\n";
    let boundary_offset = source.find("> stop").unwrap();
    let start = source.as_ptr();
    let (green, exit, remainder) = run_rule_body_fenced(source, source_origin, &fence);
    assert_eq!(remainder, &source[boundary_offset..]);
    assert_eq!(remainder.as_ptr(), start.wrapping_add(boundary_offset));
    assert_eq!(
        returned(exit),
        expected_boundary_item(remainder, source_origin + boundary_offset, &fence, &[],)
    );
    assert_eq!(count(&green, SyntaxKind::StringLiteral), 1);
    assert!(tokens(&green).contains(&(SyntaxKind::StringText, "β".to_owned())));
    assert!(tokens(&green).contains(&(SyntaxKind::YmQuotePrefix, "> > ".to_owned())));
}

#[test]
fn expression_list_missing_close_preserves_outer_close_or_eof_item() {
    let (green, exit, remainder) = run_rule_body("{a(1}");
    assert_eq!(exit, RuleWitnessExit::Complete);
    assert_eq!(remainder, "");
    assert_eq!(count(&green, SyntaxKind::Missing), 1);
    assert_eq!(count(&green, SyntaxKind::RuleCall), 1);

    let (green, exit, remainder) = run_rule_body("{a[1 /*eof*/");
    let mut eof = returned(exit);
    assert!(eof.payload_view().is_eof());
    assert_eq!(remainder, "");
    assert_eq!(emit_pending_leading_text(&mut eof), " /*eof*/");
    assert!(!root(&green).to_string().contains("/*eof*/"));
    assert_eq!(count(&green, SyntaxKind::Missing), 2);
}

#[test]
fn expression_list_fence_handoff_keeps_the_exact_item_and_leading_trivia() {
    let boundary = Item::plain(
        LeadingTrivia::ordinary(
            vec![
                ordinary_trivia(TriviaKind::Newline, "\n"),
                ordinary_trivia(TriviaKind::Whitespace, "  "),
            ]
            .into_boxed_slice(),
        ),
        Payload::Boundary(PendingBoundary::new(
            70..71,
            Boundary::Stop(StopKind::YumarkFence(Box::new(
                crate::rewrite::yumark::YumarkFenceTransition {
                    line: 70,
                    expected_depth: 2,
                    expected_base: 0,
                    indentation: 70..70,
                    observed: None,
                    kind: QuoteTransitionKind::NonPrefix,
                    inspected: 70..71,
                },
            ))),
        )),
    );
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = "";
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = expression_list_handoff_witness(
        In::new(&mut input, &mut recover, &mut builder),
        boundary,
        TokenKind::RParen,
        70,
    );
    builder.finish_node();
    let green = builder.finish();
    let returned = returned(exit);
    let (leading, pending) = emit_terminal_leading_text(returned);
    assert_eq!(leading, "\n  ");
    assert_eq!(pending.inspected(), &(70..71));
    assert_eq!(root(&green).to_string(), "");
    assert_eq!(count(&green, SyntaxKind::Missing), 1);
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
        LeadingTrivia::ordinary(
            vec![ordinary_trivia(TriviaKind::Whitespace, "  ")].into_boxed_slice(),
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
    let (green, exit, _) = run_rule_body_with("", boundary, 90);
    let boundary = returned(exit);
    let (leading, _) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "  ");
    assert_eq!(root(&green).to_string(), "{");
    assert_eq!(count(&green, SyntaxKind::Missing), 1);

    let (green, exit, _) = run_rule_body("{a= /*eof*/");
    let mut eof = returned(exit);
    assert!(eof.payload_view().is_eof());
    assert_eq!(emit_pending_leading_tokens(&mut eof).len(), 2);
    assert!(!root(&green).to_string().contains("/*eof*/"));
    assert_eq!(count(&green, SyntaxKind::Missing), 2);
}

#[test]
fn introducer_trivia_is_one_fence_aware_successor_item() {
    for source in ["\n{}", " /*comment*/ {}"] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new(&operators);
        let mut input = source;
        let mut item = scan_rule_introducer_successor_witness(
            In::new(&mut input, &mut recover, ()),
            4,
            &plain_fence(),
        );
        assert_eq!(item.payload_view().token_kind(), Some(TokenKind::LBrace));
        assert_eq!(input, "}");
        assert_eq!(
            emit_pending_leading_text(&mut item),
            &source[..source.len() - 2]
        );
    }

    let source = "\n> > {}";
    let start = source.as_ptr();
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let mut item = scan_rule_introducer_successor_witness(
        In::new(&mut input, &mut recover, ()),
        4,
        &active_fence(2),
    );
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::LBrace));
    assert_eq!(input, "}");
    assert_eq!(input.as_ptr(), start.wrapping_add(source.len() - 1));
    assert_eq!(
        emit_pending_leading_tokens(&mut item),
        [
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
        ]
    );

    let source = "\n> stop\n";
    let start = source.as_ptr();
    let mut input = source;
    let item = scan_rule_introducer_successor_witness(
        In::new(&mut input, &mut recover, ()),
        4,
        &active_fence(2),
    );
    assert!(item.payload_view().is_boundary());
    assert_eq!(input, "> stop\n");
    assert_eq!(input.as_ptr(), start.wrapping_add(1));
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
    let current = scan_rule_item_witness(lex).expect("RuleBody current Item");
    let suffix_before_body = input;
    let suffix_pointer_before_body = input.as_ptr();

    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let origin = 4 + source.len() - input.len();
    let exit = rule_body_witness(
        In::new(&mut input, &mut recover, &mut builder),
        opener,
        current,
        origin,
        &active_fence(2),
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
    let mut item = scan_rule_introducer_successor_witness(
        In::new(&mut input, &mut recover, ()),
        20,
        &active_fence(2),
    );
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::LBrace));
    assert_eq!(input, "}");
    assert_eq!(
        emit_pending_leading_tokens(&mut item),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::BlockComment, "/*x\r\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::BlockComment, "y*/".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
        ]
    );
}
