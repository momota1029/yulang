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
fn post_core_identifier_is_owned_unemitted_handoff() {
    let (green, exit) = run("a β");
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
        [(TriviaKind::Whitespace, " ")]
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
