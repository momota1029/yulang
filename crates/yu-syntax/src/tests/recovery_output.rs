//! CST recovery witnesses shared by malformed-input tests.

use rowan::GreenNodeBuilder;

use crate::{
    SyntaxKind, SyntaxNode,
    cursor::recovery::emit::{
        emit_recovery_error_item, emit_recovery_error_run, emit_recovery_missing,
    },
    cursor::{Recover, SyntaxIn},
    lexical::item::{Item, LeadingTrivia, Payload, Token, TokenKind, Trivia},
    operator_table::OperatorTable,
    tests::support::finish_with_discarded_recoveries,
};

/// A test view of a raw Error-token group or structured Invalid node. It is
/// derived from the CST; it never observes parser recovery state.
#[derive(Clone, Debug)]
pub(super) enum RecoveryGroup {
    Raw(Vec<crate::SyntaxToken>),
    Structured(SyntaxNode),
}

impl RecoveryGroup {
    pub(super) fn descendants(&self) -> impl Iterator<Item = SyntaxNode> {
        match self {
            Self::Raw(_) => Vec::new(),
            Self::Structured(node) => node.descendants().collect(),
        }
        .into_iter()
    }

    pub(super) fn descendants_with_tokens(
        &self,
    ) -> impl Iterator<Item = rowan::NodeOrToken<SyntaxNode, crate::SyntaxToken>> {
        match self {
            Self::Raw(tokens) => tokens.iter().cloned().map(Into::into).collect::<Vec<_>>(),
            Self::Structured(node) => node.descendants_with_tokens().collect(),
        }
        .into_iter()
    }

    pub(super) fn text(&self) -> String {
        match self {
            Self::Raw(tokens) => tokens.iter().map(|token| token.text()).collect(),
            Self::Structured(node) => node.to_string(),
        }
    }

    pub(super) fn text_range(&self) -> rowan::TextRange {
        match self {
            Self::Raw(tokens) => rowan::TextRange::new(
                tokens[0].text_range().start(),
                tokens.last().unwrap().text_range().end(),
            ),
            Self::Structured(node) => node.text_range(),
        }
    }

    pub(super) fn parent(&self) -> Option<SyntaxNode> {
        match self {
            Self::Raw(tokens) => tokens[0].parent(),
            Self::Structured(node) => node.parent(),
        }
    }

    pub(super) fn next_sibling_or_token(
        &self,
    ) -> Option<rowan::NodeOrToken<SyntaxNode, crate::SyntaxToken>> {
        match self {
            Self::Raw(tokens) => tokens.last().unwrap().next_sibling_or_token(),
            Self::Structured(node) => node.next_sibling_or_token(),
        }
    }

    pub(super) fn children(&self) -> impl Iterator<Item = SyntaxNode> {
        match self {
            Self::Raw(_) => Vec::new(),
            Self::Structured(node) => node.children().collect(),
        }
        .into_iter()
    }

    pub(super) fn children_with_tokens(
        &self,
    ) -> impl Iterator<Item = rowan::NodeOrToken<SyntaxNode, crate::SyntaxToken>> {
        match self {
            Self::Raw(tokens) => tokens.iter().cloned().map(Into::into).collect::<Vec<_>>(),
            Self::Structured(node) => node.children_with_tokens().collect(),
        }
        .into_iter()
    }

    pub(super) fn first_token(&self) -> Option<crate::SyntaxToken> {
        match self {
            Self::Raw(tokens) => tokens.first().cloned(),
            Self::Structured(node) => node.first_token(),
        }
    }

    pub(super) fn last_token(&self) -> Option<crate::SyntaxToken> {
        match self {
            Self::Raw(tokens) => tokens.last().cloned(),
            Self::Structured(node) => node.last_token(),
        }
    }
}

impl std::fmt::Display for RecoveryGroup {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.text())
    }
}

pub(super) fn recovery_groups(root: &SyntaxNode) -> Vec<RecoveryGroup> {
    fn visit(node: &SyntaxNode, groups: &mut Vec<RecoveryGroup>) {
        assert_ne!(node.kind(), SyntaxKind::Error, "Error must be a token");
        if node.kind() == SyntaxKind::Invalid {
            groups.push(RecoveryGroup::Structured(node.clone()));
        }
        let mut children = node.children_with_tokens().peekable();
        while let Some(child) = children.next() {
            match child {
                rowan::NodeOrToken::Node(node) => visit(&node, groups),
                rowan::NodeOrToken::Token(token) if token.kind() == SyntaxKind::Error => {
                    let mut tokens = vec![token];
                    while children
                        .peek()
                        .is_some_and(|next| next.kind() == SyntaxKind::Error)
                    {
                        let next = children.next().unwrap().into_token().expect("Error leaf");
                        assert_eq!(tokens.last().unwrap().parent(), next.parent());
                        assert_eq!(
                            tokens.last().unwrap().text_range().end(),
                            next.text_range().start()
                        );
                        tokens.push(next);
                    }
                    groups.push(RecoveryGroup::Raw(tokens));
                }
                _ => {}
            }
        }
    }

    let mut groups = Vec::new();
    visit(root, &mut groups);
    groups
}

fn unknown_item(text: &str) -> Item {
    Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: text.into(),
        }),
    )
}

#[test]
fn direct_recovery_emission_is_lossless_and_cst_derived() {
    let mut source = "";
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    emit_recovery_missing(
        SyntaxIn::new(&mut source, &mut recover, &mut output),
        LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        1,
    );
    emit_recovery_error_item(
        SyntaxIn::new(&mut source, &mut recover, &mut output),
        unknown_item("α"),
        3,
    );
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    assert_eq!(green.to_string(), " α");
    assert_eq!(
        crate::tests::support::structural_facts(&green),
        [
            (crate::structural_diagnostic::StructuralKind::Missing, 1..1),
            (
                crate::structural_diagnostic::StructuralKind::ErrorGroup,
                1..3
            ),
        ]
    );
}

#[test]
fn error_run_preserves_source_order_for_continuation() {
    let mut source = "";
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    emit_recovery_error_run(
        SyntaxIn::new(&mut source, &mut recover, &mut output),
        |run| {
            run.emit_item_as(unknown_item("@"), 1);
            run.emit_item_as(unknown_item("β"), 3);
        },
    );
    output.token(SyntaxKind::Identifier.into(), "next");
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    assert_eq!(green.to_string(), "@βnext");
    assert_eq!(
        crate::tests::support::structural_facts(&green),
        [(
            crate::structural_diagnostic::StructuralKind::ErrorGroup,
            0..3
        )]
    );
    let root = SyntaxNode::new_root(green);
    let groups = recovery_groups(&root);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].text(), "@β");
    assert_eq!(
        groups[0]
            .next_sibling_or_token()
            .unwrap()
            .into_token()
            .unwrap()
            .text(),
        "next"
    );
}
