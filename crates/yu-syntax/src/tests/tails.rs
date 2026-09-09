use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    lexical::{
        item::{BorrowedTarget, Boundary},
        yumark::{FenceOpener, FencePrefixPolicy},
    },
    statement::StatementLineHandoff,
};

fn range(node: &SyntaxNode) -> std::ops::Range<usize> {
    usize::from(node.text_range().start())..usize::from(node.text_range().end())
}

fn run_fixed_tail_normalized(
    source: &str,
    operators: &OperatorTable,
    threshold: Option<&BindingPower>,
    ml_mode: MlMode,
) -> (GreenNode, NormalizedExit) {
    let mut input = source;
    let mut recover = Recover::new_for_test(operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        SyntaxIn::new(&mut input, &mut recover, &mut output),
        threshold,
        0,
        0,
        ml_mode,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .expect("admitted fixed tail expression");
    output.finish_node();
    (finish_with_discarded_recoveries(output, recover), exit)
}

fn run_fixed_tail_fenced(
    source: &str,
    origin: usize,
    fence: &FenceBoundary,
) -> (GreenNode, NormalizedExit, String) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        Some(fence),
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .expect("admitted fenced fixed tail expression");
    output.finish_node();
    (
        finish_with_discarded_recoveries(output, recover),
        exit,
        input.to_owned(),
    )
}

#[test]
fn fixed_tail_name_slots_have_direct_rowan_admission_shapes() {
    let source = "x .field:: $name";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let chain = root.first_child().expect("outer OperatorChain");
    assert_eq!(chain.kind(), SyntaxKind::OperatorChain);
    let children = chain.children().collect::<Vec<_>>();
    assert_eq!(
        children.iter().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::FieldTail,
            SyntaxKind::PathTail,
        ]
    );
    let field = &children[1];
    assert_eq!(range(field), 1..8);
    assert_eq!(field.parent(), Some(chain.clone()));
    assert_eq!(
        field
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Whitespace,
            SyntaxKind::Dot,
            SyntaxKind::Identifier,
        ]
    );
    let path = &children[2];
    assert_eq!(range(path), 8..16);
    assert_eq!(path.parent(), Some(chain.clone()));
    assert_eq!(
        path.children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::ColonColon,
            SyntaxKind::Whitespace,
            SyntaxKind::SigilIdentifier,
        ]
    );

    let source = "x::\r\n&name";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PathTail)
        .expect("PathTail");
    assert_eq!(range(&path), 1..10);
    assert_eq!(
        path.children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::ColonColon,
            SyntaxKind::Newline,
            SyntaxKind::SigilIdentifier,
        ]
    );
    assert_eq!(path.to_string(), "::\r\n&name");
}

#[test]
fn fixed_tail_name_slots_keep_missing_and_field_leading_at_the_outer_slot() {
    let (green, exit) = run("x. field");
    assert_eq!(green.to_string(), "x. field");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let chain = root.first_child().expect("outer OperatorChain");
    let children = chain.children().collect::<Vec<_>>();
    assert_eq!(
        children.iter().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::FieldTail,
            SyntaxKind::MlArgument,
        ]
    );
    let field = &children[1];
    assert_eq!(range(field), 1..2);
    assert_eq!(
        field
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Dot, SyntaxKind::Missing]
    );
    let missing = field.last_child().expect("FieldName Missing");
    assert_eq!(missing.kind(), SyntaxKind::Missing);
    assert_eq!(range(&missing), 2..2);
    assert_eq!(missing.parent(), Some(field.clone()));
    let argument = &children[2];
    assert_eq!(
        argument.first_token().expect("field leading").kind(),
        SyntaxKind::Whitespace
    );
    assert_eq!(argument.first_token().unwrap().text(), " ");

    let (green, exit) = run("x::,");
    assert_eq!(green.to_string(), "x::");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item))) if token_kind(&item) == Some(TokenKind::Comma)
    ));
    let root = SyntaxNode::new_root(green);
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PathTail)
        .expect("PathTail");
    assert_eq!(range(&path), 1..3);
    assert_eq!(
        path.children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::ColonColon, SyntaxKind::Missing]
    );
    let missing = path.last_child().expect("PathSegment Missing");
    assert_eq!(missing.kind(), SyntaxKind::Missing);
    assert_eq!(range(&missing), 3..3);
    assert_eq!(missing.parent(), Some(path));
}

#[test]
fn fixed_tail_name_slots_keep_raw_error_and_later_tails_as_siblings() {
    let (green, exit) = run("x.@::later");
    assert_eq!(green.to_string(), "x.@::later");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let chain = root.first_child().expect("outer OperatorChain");
    let tails = chain
        .children()
        .filter(|node| matches!(node.kind(), SyntaxKind::FieldTail | SyntaxKind::PathTail))
        .collect::<Vec<_>>();
    assert_eq!(
        tails.iter().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::FieldTail, SyntaxKind::PathTail]
    );
    assert_eq!(
        tails[0]
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Dot, SyntaxKind::Error]
    );
    let error = tails[0].last_token().expect("FieldName Error");
    assert_eq!((error.kind(), error.text()), (SyntaxKind::Error, "@"));
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        2..3
    );
    assert_eq!(error.parent(), Some(tails[0].clone()));
    assert_eq!(
        tails[1].first_token().expect("later path").kind(),
        SyntaxKind::ColonColon
    );
    assert_eq!(
        tails[1]
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::ColonColon, SyntaxKind::Identifier]
    );
    assert_eq!(tails[1].parent(), Some(chain.clone()));
    assert!(
        !tails[0]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Identifier)
    );

    let (green, exit) = run("x:: @::later");
    assert_eq!(green.to_string(), "x:: @::later");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let chain = root.first_child().expect("outer OperatorChain");
    let tails = chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::PathTail)
        .collect::<Vec<_>>();
    assert_eq!(tails.len(), 2);
    let first = &tails[0];
    assert_eq!(range(first), 1..5);
    assert_eq!(
        first
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::ColonColon,
            SyntaxKind::Whitespace,
            SyntaxKind::Error
        ]
    );
    let leaves = first
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .collect::<Vec<_>>();
    assert_eq!(
        leaves
            .iter()
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Error, "@".to_owned()),
        ]
    );
    assert_eq!(
        usize::from(leaves[2].text_range().start())..usize::from(leaves[2].text_range().end()),
        4..5
    );
    assert_eq!(leaves[2].parent(), Some(first.clone()));
    assert_eq!(tails[1].parent(), Some(chain));
    assert_eq!(
        tails[1]
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::ColonColon, SyntaxKind::Identifier]
    );

    let source = "x::💥";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(range(&root), 0..source.len());
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PathTail)
        .expect("PathTail");
    assert_eq!(range(&path), 1..source.len());
    assert_eq!(
        path.children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::ColonColon, SyntaxKind::Error]
    );
    let error = path.last_token().expect("UTF-8 PathSegment Error");
    assert_eq!(error.text(), "💥");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        3..source.len()
    );
}

#[test]
fn fixed_tail_raw_error_keeps_a_quoted_fence_pending_outside_the_cst() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "x::💥\r\n> > ```\nouter";
    let (green, exit, remainder) = run_fixed_tail_fenced(source, 100, &fence);
    assert_eq!(green.to_string(), "x::💥");
    let root = SyntaxNode::new_root(green);
    assert_eq!(range(&root), 0..7);
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PathTail)
        .expect("PathTail");
    assert_eq!(range(&path), 1..7);
    assert_eq!(
        path.children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::ColonColon, SyntaxKind::Error]
    );
    let error = path.last_token().expect("PathSegment Error");
    assert_eq!(error.text(), "💥");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        3..7
    );
    assert_eq!(remainder, "> > ```\nouter");
    let NormalizedExit::Complete(Err(Either::Left(item)), line) = exit else {
        panic!("quoted fence remains pending")
    };
    assert_eq!(line, LineEntry::PhysicalStart);
    assert!(item.payload_view().is_boundary());
    assert!(item.leading_view().has_ordinary_newline());
    assert_eq!(item.leading_view().remaining_physical_parts(), 1);
    let boundary = item
        .payload_view()
        .pending_boundary()
        .expect("quoted fence boundary");
    assert_eq!(boundary.inspected(), &(109..117));
    assert!(matches!(
        boundary.kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
    assert_eq!(
        item.extent(100 + source.len() - remainder.len())
            .recovery_range(),
        107..109,
        "the pending Item owns only the CRLF leading; its fence facts remain in the boundary"
    );
}

#[test]
fn fixed_tail_name_slots_preserve_projection_priority_and_path_brace_recovery() {
    for (source, tail_kind) in [
        ("x.{field}", SyntaxKind::ProjectionRecordTail),
        ("x.(field)", SyntaxKind::ProjectionTupleTail),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        assert!(root.descendants().any(|node| node.kind() == tail_kind));
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::FieldTail)
        );
    }

    let (green, exit) = run("x::{field}");
    assert_eq!(green.to_string(), "x::{");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item))) if token_kind(&item) == Some(TokenKind::Identifier)
    ));
    let root = SyntaxNode::new_root(green);
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PathTail)
        .expect("PathTail");
    assert_eq!(range(&path), 1..4);
    assert_eq!(
        path.children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::ColonColon, SyntaxKind::Error]
    );
    let error = path.last_token().expect("PathSegment Error");
    assert_eq!(error.kind(), SyntaxKind::Error);
    assert_eq!(error.text(), "{");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        3..4
    );
    assert_eq!(error.parent(), Some(path));
}

#[test]
fn fixed_tail_name_slots_preserve_threshold_and_ml_outer_handoffs() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(20), BindingPower::scalar(21)),
    )])
    .expect("fixed-tail handoff operator table");
    let threshold = BindingPower::scalar(70);
    let (green, exit) =
        run_fixed_tail_normalized("x.@ + y", &operators, Some(&threshold), MlMode::All);
    assert_eq!(green.to_string(), "x.@");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(item)), _)
            if token_kind(&item) == Some(TokenKind::Operator)
    ));
    let root = SyntaxNode::new_root(green);
    let chain = root.first_child().expect("outer OperatorChain");
    assert_eq!(
        chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::IdentifierExpression, SyntaxKind::FieldTail]
    );
    let field = chain.last_child().expect("FieldTail");
    assert_eq!(
        field
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Dot, SyntaxKind::Error]
    );

    let (green, exit) =
        run_fixed_tail_normalized("x::123 name", &OperatorTable::empty(), None, MlMode::None);
    assert_eq!(green.to_string(), "x::123");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(item)), _)
            if token_kind(&item) == Some(TokenKind::Identifier)
    ));
    let root = SyntaxNode::new_root(green);
    let chain = root.first_child().expect("outer OperatorChain");
    assert_eq!(
        chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::IdentifierExpression, SyntaxKind::PathTail]
    );
    let path = chain.last_child().expect("PathTail");
    assert_eq!(
        path.children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::ColonColon, SyntaxKind::Error]
    );
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
    assert!(!root.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
    )));
}

#[test]
fn path_tails_classify_sigil_segments() {
    let source = "a::$value?:: &reference::'label::_hidden::_";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let paths = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::PathTail)
        .map(|path| {
            path.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::ColonColon
                            | SyntaxKind::Identifier
                            | SyntaxKind::SigilIdentifier
                    )
                })
                .map(|token| (token.kind(), token.text().to_owned()))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        paths,
        [
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::SigilIdentifier, "$value?".to_owned()),
            ],
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::SigilIdentifier, "&reference".to_owned()),
            ],
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::SigilIdentifier, "'label".to_owned()),
            ],
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::SigilIdentifier, "_hidden".to_owned()),
            ],
            vec![
                (SyntaxKind::ColonColon, "::".to_owned()),
                (SyntaxKind::Identifier, "_".to_owned()),
            ],
        ]
    );
    assert!(!root.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
    )));
}

#[test]
fn fixed_tails_keep_missing_and_invalid_identifier_slots_local() {
    for (source, tail_kind, recovery_kind) in [
        ("x.", SyntaxKind::FieldTail, SyntaxKind::Missing),
        ("x.@", SyntaxKind::FieldTail, SyntaxKind::Error),
        ("x::", SyntaxKind::PathTail, SyntaxKind::Missing),
        ("x::123", SyntaxKind::PathTail, SyntaxKind::Error),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let tail = root
            .descendants()
            .find(|node| node.kind() == tail_kind)
            .expect("fixed tail");
        assert_eq!(
            tail.children_with_tokens()
                .filter(|node| node.kind() == recovery_kind)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run("x::::name");
    assert_eq!(green.to_string(), "x::::name");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::PathTail)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
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
                    if item.payload_view().token_kind() == Some(TokenKind::Unknown)
                        && item.payload_view().spelling() == Some(".")
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
fn lone_colon_tail_is_terminal_and_preserves_outer_comma_ownership() {
    let (green, exit) = run("f: x");
    assert_eq!(green.to_string(), "f: x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&green),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::ColonApplicationTail,
        ]
    );

    let operators = dynamic_operator_table();
    let (green, exit) = run_with("a + b: x", &operators);
    assert_eq!(green.to_string(), "a + b: x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    assert_eq!(
        chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
            SyntaxKind::ColonApplicationTail,
        ]
    );
    let colon = chain
        .children()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::OperatorChain]
    );

    let (green, exit) = run("f: x, y");
    assert_eq!(green.to_string(), "f: x, y");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let colon = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        2
    );
    assert_eq!(
        colon
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Comma)
            .count(),
        1
    );

    let (green, exit) = run("(f: x, y)");
    assert_eq!(green.to_string(), "(f: x, y)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let colon = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Comma)
            .count(),
        1
    );

    let (green, exit) = run("f::T");
    assert_eq!(green.to_string(), "f::T");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::PathTail)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail)
    );

    let (green, exit) = run("f\n: x");
    assert_eq!(green.to_string(), "f");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Colon)
    ));
}

#[test]
fn with_c5_is_a_terminal_direct_body_tail() {
    let (green, exit) = run("f with: x");
    assert_eq!(green.to_string(), "f with: x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&green),
        [SyntaxKind::IdentifierExpression, SyntaxKind::WithBodyTail,]
    );

    for source in ["f /*c*/ with : x", "f\n  with:\n    x"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::WithBodyTail)
        );
    }

    for source in ["f withx", "f with?"] {
        let (green, _) = run(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::WithBodyTail),
            "{source:?}"
        );
    }

    let with_operator = OperatorTable::from_declarations([OperatorDeclaration::new(
        "with",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(40)),
    )])
    .expect("contextual with test table");
    let (green, exit) = run_with("f with: x", &with_operator);
    assert_eq!(green.to_string(), "f with: x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::WithKw)
    );
    for source in ["f with?: x", "f with!: x"] {
        let (green, _) = run_with(source, &with_operator);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::WithBodyTail),
            "{source:?}"
        );
    }

    for source in ["f with: x: y", "f with: x with: y"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.children()
                .find(|node| node.kind() == SyntaxKind::OperatorChain)
                .expect("outer chain")
                .children()
                .filter(|node| node.kind() == SyntaxKind::WithBodyTail)
                .count(),
            1,
            "{source:?}"
        );
    }

    for source in ["f with", "f with x", "f with: ", "f with:\n  "] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let tail = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::WithBodyTail)
            .expect("with tail");
        assert_eq!(
            tail.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run("f with:\nx");
    assert_eq!(green.to_string(), "f with:");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                && item.payload_view().spelling() == Some("x")
    ));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert_eq!(
        tail.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run("f with\nx");
    assert_eq!(green.to_string(), "f with");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                && item.payload_view().spelling() == Some("x")
    ));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert_eq!(
        tail.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !tail
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Newline)
    );

    let (green, exit) = run("f with ;");
    // The inline recovery contract preserves the protected semicolon's whole Item.
    assert_eq!(green.to_string(), "f with");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Semicolon)
    ));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert!(
        !tail
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Semicolon)
    );

    for source in ["f with: ;", "f with: @;", "f with: @ x"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let tail = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::WithBodyTail)
            .expect("with tail");
        if source == "f with: ;" {
            assert_eq!(
                tail.children()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                1
            );
        } else {
            assert_eq!(
                crate::tests::recovery_output::recovery_groups(&tail)
                    .into_iter()
                    .filter(|group| group.parent().as_ref() == Some(&tail))
                    .count(),
                1,
                "{source:?}"
            );
        }
        if source != "f with: @ x" {
            assert!(
                tail.descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == SyntaxKind::Semicolon)
            );
        }
    }

    let (green, exit) = run("f with {}");
    // Missing-introducer recovery also protects the braced candidate's leading.
    assert_eq!(green.to_string(), "f with");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::LBrace)
    ));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert_eq!(
        tail.descendants()
            .filter(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .count(),
        0
    );

    let (green, exit) = run("(f with: x, y)");
    assert_eq!(green.to_string(), "(f with: x, y)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let tail = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::WithBodyTail)
        .expect("with tail");
    assert!(
        !tail
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Comma)
    );
}

#[test]
fn colon_c4_commits_and_recovers_mandatory_inline_slots() {
    for (source, expected) in [
        ("f:", "f:"),
        ("f:   ", "f:   "),
        ("f:\nx", "f:"),
        ("f:\n  ", "f:\n  "),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), expected, "{source:?}");
        let root = SyntaxNode::new_root(green);
        let colon = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("accepted colon tail");
        assert_eq!(
            colon
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !colon
                .descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid)),
            "{source:?}"
        );
        if source == "f:\nx" {
            assert!(matches!(
                exit,
                Some(Err(Either::Left(item)))
                    if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                        && item.payload_view().spelling() == Some("x")
            ));
            assert!(
                !colon
                    .descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == SyntaxKind::Newline)
            );
        } else {
            assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        }
    }

    for source in ["f: , x", "f: x,"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let colon = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("colon tail");
        assert_eq!(
            colon
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            colon
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Comma)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run("(f:, y)");
    assert_eq!(green.to_string(), "(f:, y)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let colon = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !colon
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Comma)
    );

    let (green, exit) = run("f: @ x");
    assert_eq!(green.to_string(), "f: @ x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let colon = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&colon)
            .into_iter()
            .filter(|group| group.parent().as_ref() == Some(&colon))
            .count(),
        1
    );
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );
    assert_eq!(
        colon
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );

    let (green, exit) = run("f: @  ");
    assert_eq!(green.to_string(), "f: @  ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let colon = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("colon tail");
    assert_eq!(
        colon.last_token().expect("tail trailing trivia").text(),
        "  "
    );

    let (green, exit) = run("f: {x}");
    assert_eq!(green.to_string(), "f: {x}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
    );

    let operators = dynamic_operator_table();
    for (source, kind) in [
        ("f: ~x", SyntaxKind::PrefixOperatorUse),
        ("f: ?", SyntaxKind::NullfixOperatorUse),
    ] {
        let (green, exit) = run_with(source, &operators);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let colon = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .expect("colon tail");
        assert!(
            colon.descendants().any(|node| node.kind() == kind),
            "{source:?}"
        );
    }
}

#[test]
fn colon_c2_indented_expression_statement_block_preserves_dedent() {
    let (green, exit) = run("f:\n  x");
    assert_eq!(green.to_string(), "f:\n  x");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("indented colon block");
    assert_eq!(
        block.first_token().expect("opening newline").kind(),
        SyntaxKind::Newline
    );
    assert_eq!(
        block.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::Statement]
    );

    let (green, exit) = run("f:\n  x\n  y");
    assert_eq!(green.to_string(), "f:\n  x\n  y");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("indented colon block");
    assert_eq!(
        block.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::Statement,
            SyntaxKind::BlockStatementSeparator,
            SyntaxKind::Statement,
        ]
    );

    let (green, exit) = run("f:\n  x\nz");
    assert_eq!(green.to_string(), "f:\n  x");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                && item.payload_view().spelling() == Some("z")
    ));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        1
    );

    let (green, exit) = run("f:\n    x\n      y");
    assert_eq!(green.to_string(), "f:\n    x\n      y");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("indented colon block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        1
    );
    assert!(
        block
            .descendants()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );
}

#[test]
fn dynamic_nuds_are_direct_canonical_statements() {
    let operators = dynamic_operator_table();
    for (source, operator_kind) in [
        ("~x", SyntaxKind::PrefixOperatorUse),
        ("?", SyntaxKind::NullfixOperatorUse),
    ] {
        let (green, exit) = run_statement_with(source, &operators);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .count(),
            1,
            "{source:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == operator_kind)
                .count(),
            1,
            "{source:?}",
        );
    }
}

#[test]
fn dynamic_nuds_enter_strict_indented_statement_blocks() {
    let operators = dynamic_operator_table();
    for (source, operator_kind) in [
        ("f:\n  ~x\nz", SyntaxKind::PrefixOperatorUse),
        ("f:\n  ?\nz", SyntaxKind::NullfixOperatorUse),
    ] {
        let (green, exit) = run_with(source, &operators);
        assert_eq!(green.to_string(), &source[..source.len() - 2], "{source:?}");
        assert!(
            matches!(
                exit,
                Some(Err(Either::Left(item)))
                    if item.payload_view().token_kind() == Some(TokenKind::Identifier)
                        && item.payload_view().spelling() == Some("z")
            ),
            "{source:?}",
        );

        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .expect("strict indented statement block");
        assert_eq!(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .count(),
            1,
            "{source:?}",
        );
        assert_eq!(
            block
                .descendants()
                .filter(|node| node.kind() == operator_kind)
                .count(),
            1,
            "{source:?}",
        );
    }
}

#[test]
fn dynamic_nuds_enter_braced_statement_sequences_and_leave_close_owned() {
    let operators = dynamic_operator_table();
    for (source, operator_kind) in [
        ("{~x}", SyntaxKind::PrefixOperatorUse),
        ("{?}", SyntaxKind::NullfixOperatorUse),
    ] {
        let (green, exit) = run_with(source, &operators);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .expect("braced statement sequence");
        assert_eq!(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .count(),
            1,
            "{source:?}",
        );
        assert_eq!(
            block
                .descendants()
                .filter(|node| node.kind() == operator_kind)
                .count(),
            1,
            "{source:?}",
        );
        assert_eq!(
            block
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::RBrace)
                .count(),
            1,
            "{source:?}",
        );
    }
}

#[test]
fn colon_c4_recovers_deep_indented_statement_slots() {
    let (green, exit) = run("f:\n  ");
    assert_eq!(green.to_string(), "f:\n  ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("deep block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    for source in ["f:\n  @", "f:\n  @ x"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .expect("deep block");
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&block)
                .into_iter()
                .filter(|group| group.parent().as_ref() == Some(&block))
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
            "{source:?}"
        );
    }

    let (green, exit) = run("f:\n  x\n  @\n  y");
    assert_eq!(green.to_string(), "f:\n  x\n  @\n  y");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("deep block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .count(),
        2
    );
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&block)
            .into_iter()
            .filter(|group| group.parent().as_ref() == Some(&block))
            .count(),
        1
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
}

#[test]
fn braced_statement_block_owns_normal_sequence_and_colon_comma() {
    for source in ["{}", "{ }", "{\n}"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .expect("braced statement block");
        assert!(
            !block
                .children()
                .any(|node| node.kind() == SyntaxKind::Statement)
        );
    }

    let (green, exit) = run("{x: 1}");
    assert_eq!(green.to_string(), "{x: 1}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        block.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::Statement]
    );
    assert_eq!(
        block
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .count(),
        1
    );

    for (source, separator) in [
        ("{x,y}", SyntaxKind::Comma),
        ("{x;y}", SyntaxKind::Semicolon),
        ("{x\ny}", SyntaxKind::Newline),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .expect("braced statement block");
        assert_eq!(
            block.children().map(|node| node.kind()).collect::<Vec<_>>(),
            [
                SyntaxKind::Statement,
                SyntaxKind::BlockStatementSeparator,
                SyntaxKind::Statement,
            ],
            "{source:?}"
        );
        let separator_node = block
            .children()
            .find(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .expect("block separator");
        assert!(
            separator_node
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == separator),
            "{source:?}"
        );
    }

    for source in ["{x,}", "{x;}", "{x\n}"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .expect("braced statement block");
        assert_eq!(
            block.children().map(|node| node.kind()).collect::<Vec<_>>(),
            [SyntaxKind::Statement, SyntaxKind::BlockStatementSeparator],
            "{source:?}"
        );
        assert!(
            !block.descendants_with_tokens().any(|node| matches!(
                node.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            )),
            "{source:?}"
        );
    }

    let (green, exit) = run("{x: 1, y: 2}");
    assert_eq!(green.to_string(), "{x: 1, y: 2}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
    assert_eq!(
        block
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .count(),
        2
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .count(),
        1
    );
}

#[test]
fn braced_statement_block_recovers_close_and_keeps_nested_boundaries() {
    for source in ["{", "{x", "{x,"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .expect("braced statement block");
        assert_eq!(
            block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run("{@}");
    assert_eq!(green.to_string(), "{@}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&root)
            .into_iter()
            .count(),
        1
    );

    // Braced recovery's authoritative Slots, boundary and retry rule protects
    // nonlocal closes: `]` and the later `}` remain outside this block.
    let (green, exit, remainder) =
        run_normalized("{x]}", &OperatorTable::empty(), 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "{x");
    assert_eq!(remainder, "}");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
        panic!("protected nonlocal close")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
    assert_eq!(item.extent(3).recovery_range(), 2..3);
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&block)
            .into_iter()
            .filter(|group| group.parent().as_ref() == Some(&block))
            .count(),
        0
    );
    assert_eq!(
        block
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::RBrace)
            .count(),
        0
    );
    assert!(
        block
            .children()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run("{x\n  y}");
    assert_eq!(green.to_string(), "{x\n  y}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        1
    );
    assert!(
        block
            .descendants()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );

    let (green, exit) = run("{x,@\ny}");
    assert_eq!(green.to_string(), "{x,@\ny}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&block)
            .into_iter()
            .filter(|group| group.parent().as_ref() == Some(&block))
            .count(),
        1
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .count(),
        2
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );

    let (green, exit) = run("{x\n  @}");
    assert_eq!(green.to_string(), "{x\n  @}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
            .count(),
        0
    );
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&block)
            .into_iter()
            .filter(|group| group.parent().as_ref() == Some(&block))
            .count(),
        1
    );

    let (green, exit) = run("{{x}}.field");
    assert_eq!(green.to_string(), "{{x}}.field");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&green),
        [
            SyntaxKind::BracedStatementBlockExpression,
            SyntaxKind::FieldTail,
        ]
    );
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .count(),
        2
    );
}
