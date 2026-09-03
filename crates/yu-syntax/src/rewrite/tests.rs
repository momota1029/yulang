use chasa_recover::In;
use rowan::{GreenNode, GreenNodeBuilder};

use crate::{SyntaxKind, SyntaxNode, operator::OperatorTable};

use super::{
    driver::{Either, TailExit, emit_end, expr},
    item::{Payload, TokenKind, TriviaKind},
    state::Recover,
};

fn run(source: &str) -> (GreenNode, Option<TailExit>) {
    let mut input = source;
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = expr(In::new(&mut input, &mut recover, &mut builder));
    if let Some(Err(Either::Right(end))) = &exit {
        emit_end(&mut builder, end);
    }
    builder.finish_node();
    (builder.finish(), exit)
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
