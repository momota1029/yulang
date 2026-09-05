use super::*;
use crate::rewrite::{
    item::{
        BorrowedTarget, Boundary, ForeignSplit, Item, LeadingTrivia, Payload, PendingBoundary,
        PendingFragments, StopKind, Token, TokenKind, Trivia, TriviaKind,
    },
    yumark::{FenceCloseFacts, QuoteTransitionKind, YumarkFenceTransition},
};

fn borrowed_close_item() -> Item {
    Item::plain(
        LeadingTrivia(
            vec![Trivia {
                kind: TriviaKind::Whitespace,
                text: "  ".into(),
            }]
            .into_boxed_slice(),
        ),
        Payload::Boundary(PendingBoundary::new(
            40..46,
            Boundary::BorrowedClose(BorrowedTarget::YumarkFence(Box::new(FenceCloseFacts {
                line: 40,
                inspected: 40..46,
                prefix: None,
                indentation: 40..42,
                indentation_column: 2,
                marker: 42..45,
                marker_width: 3,
                horizontal_suffix: 45..45,
                newline: Some(45..46),
            }))),
        )),
    )
}

fn transition_item() -> Item {
    Item::plain(
        LeadingTrivia::default(),
        Payload::Boundary(PendingBoundary::new(
            80..87,
            Boundary::Stop(StopKind::YumarkFence(Box::new(YumarkFenceTransition {
                line: 80,
                expected_depth: 2,
                expected_base: 0,
                indentation: 80..81,
                observed: None,
                kind: QuoteTransitionKind::Reduced,
                inspected: 80..87,
            }))),
        )),
    )
}

fn eof_boundary_item() -> Item {
    Item::plain(
        LeadingTrivia(
            vec![Trivia {
                kind: TriviaKind::Newline,
                text: "\n".into(),
            }]
            .into_boxed_slice(),
        ),
        Payload::Boundary(PendingBoundary::new(120..120, Boundary::EofAfterTrivia)),
    )
}

fn count(root: &SyntaxNode, kind: SyntaxKind) -> usize {
    root.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

#[test]
fn isolated_cell_composes_current_root_style_statements_on_one_builder() {
    for (source, statements) in [("", 0), ("x", 1), ("x; y", 2), ("our x", 1)] {
        let (green, exit, remaining) = run_yumark_cell(source, borrowed_close_item());
        assert_eq!(remaining, "", "{source:?}");
        assert_eq!(exit, Err(Either::Left(borrowed_close_item())), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");

        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(count(&root, SyntaxKind::Root), 1, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::YmYulangCodeCell), 1, "{source:?}");
        assert_eq!(
            count(&root, SyntaxKind::Statement),
            statements,
            "{source:?}"
        );
        assert_eq!(
            root.children().map(|node| node.kind()).collect::<Vec<_>>(),
            [SyntaxKind::YmYulangCodeCell],
            "{source:?}"
        );
        let cell = root.first_child().expect("YmYulangCodeCell");
        if source == "x; y" {
            assert!(
                cell.children_with_tokens()
                    .any(|element| element.into_token().is_some_and(|token| {
                        token.kind() == SyntaxKind::Semicolon && token.text() == ";"
                    }))
            );
            assert_eq!(count(&cell, SyntaxKind::BlockStatementSeparator), 0);
        }
        if source == "our x" {
            assert_eq!(count(&cell, SyntaxKind::BindingStatement), 1);
            assert!(cell.descendants_with_tokens().any(|element| {
                element
                    .into_token()
                    .is_some_and(|token| token.kind() == SyntaxKind::OurKw)
            }));
        }
    }
}

#[test]
fn isolated_cell_returns_each_injected_boundary_exactly_without_emitting_it() {
    let cases = [
        (borrowed_close_item(), borrowed_close_item()),
        (transition_item(), transition_item()),
        (eof_boundary_item(), eof_boundary_item()),
    ];
    for (terminal, expected) in cases {
        let (green, exit, remaining) = run_yumark_cell("our x", terminal);
        assert_eq!(remaining, "");
        assert_eq!(exit, Err(Either::Left(expected)));
        assert_eq!(green.to_string(), "our x");
    }
}

#[test]
fn successor_boundary_is_returned_before_ordinary_token_predicates() {
    let item = fragmented_identifier_item();
    let expected = borrowed_close_item();
    let (green, exit) = run_fragmented_statement_successor(item, borrowed_close_item());
    assert_eq!(exit, Err(Either::Left(expected)));
    assert_eq!(green.to_string(), " \n> name");

    let root = SyntaxNode::new_root(green);
    assert_eq!(count(&root, SyntaxKind::Statement), 1);
    assert_eq!(count(&root, SyntaxKind::IdentifierExpression), 1);
}

#[test]
fn accepted_fragmented_statement_and_borrowed_close_share_one_cell_contract() {
    let item = fragmented_identifier_item();
    let expected = borrowed_close_item();
    let (green, exit) = run_fragmented_statement_successor(item, borrowed_close_item());
    assert_eq!(exit, Err(Either::Left(expected)));
    assert_eq!(green.to_string(), " \n> name");

    let root = SyntaxNode::new_root(green);
    assert_eq!(count(&root, SyntaxKind::Root), 1);
    assert_eq!(count(&root, SyntaxKind::YmYulangCodeCell), 1);
    assert_eq!(count(&root, SyntaxKind::Statement), 1);
    assert_eq!(count(&root, SyntaxKind::IdentifierExpression), 1);
    let cell = root.first_child().expect("YmYulangCodeCell");
    assert_eq!(count(&cell, SyntaxKind::Statement), 1);
    assert_eq!(count(&cell, SyntaxKind::IdentifierExpression), 1);
    assert_eq!(
        cell.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::Identifier, "name".to_owned()),
        ]
    );
}

fn fragmented_identifier_item() -> Item {
    let mut item = Item::plain(
        LeadingTrivia(
            vec![
                Trivia {
                    kind: TriviaKind::Whitespace,
                    text: " ".into(),
                },
                Trivia {
                    kind: TriviaKind::Newline,
                    text: "\n".into(),
                },
                Trivia {
                    kind: TriviaKind::Whitespace,
                    text: "> ".into(),
                },
            ]
            .into_boxed_slice(),
        ),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "name".into(),
        }),
    );
    let fragments =
        PendingFragments::finish(Some(vec![ForeignSplit::quote_prefix(102, 2)]), 100, 8)
            .expect("valid fragment carrier")
            .expect("one foreign split");
    item.with_fragments(fragments)
        .expect("fragment carrier matches the accepted item");
    item
}

#[test]
fn terminal_fragments_remain_unemitted_with_the_boundary() {
    let terminal = fragmented_terminal();
    let expected = fragmented_terminal();
    let (green, exit, remaining) = run_yumark_cell("", terminal);
    assert_eq!(remaining, "");
    assert_eq!(exit, Err(Either::Left(expected)));
    assert_eq!(green.to_string(), "");
    let root = SyntaxNode::new_root(green);
    assert_eq!(count(&root, SyntaxKind::YmQuotePrefix), 0);
}

fn fragmented_terminal() -> Item {
    let mut item = Item::plain(
        LeadingTrivia(
            vec![Trivia {
                kind: TriviaKind::Whitespace,
                text: "> ".into(),
            }]
            .into_boxed_slice(),
        ),
        Payload::Boundary(PendingBoundary::new(200..202, Boundary::EofAfterTrivia)),
    );
    let fragments =
        PendingFragments::finish(Some(vec![ForeignSplit::quote_prefix(200, 2)]), 200, 2)
            .expect("valid terminal fragment carrier")
            .expect("one terminal foreign split");
    item.with_fragments(fragments)
        .expect("terminal carrier matches its leading trivia");
    item
}
