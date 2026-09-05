use chasa_recover::In;
use rowan::GreenNodeBuilder;

use crate::{SyntaxKind, SyntaxNode, operator::OperatorTable};

use super::{ordinary_trivia, physical_leading};

use super::super::{
    item::{
        BorrowedTarget, Boundary, Delimiter, ForeignSplit, FragmentError, Item, LayoutEvidence,
        LeadingTrivia, OperatorToken, OperatorUse, Payload, PendingBoundary, PendingFragments,
        PhysicalLeadingTrivia, StopKind, Token, TokenKind, TriviaKind,
    },
    lexer::scan_statement_item,
    state::Recover,
    yumark::{
        FenceBoundary, FenceLineDecision, FenceOpener, FencePrefixPolicy, QuoteTransitionKind,
        is_yulang_fence_info, judge_fence_line,
    },
};

fn boundary(prefix_policy: FencePrefixPolicy, close_column: usize) -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 10,
            marker: 12..15,
            marker_width: 3,
        },
        prefix_policy,
        close_column,
    }
}

fn emit_item(item: Item, payload_kind: SyntaxKind) -> Vec<(SyntaxKind, String)> {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    item.emit_remaining(&mut builder, payload_kind);
    builder.finish_node();
    SyntaxNode::new_root(builder.finish())
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .map(|token| (token.kind(), token.text().to_owned()))
        .collect()
}

#[test]
fn yulang_fence_selector_uses_only_the_exact_first_info_atom() {
    for info in ["yulang", "  yulang", "\tyulang anything", "yulang test"] {
        assert!(is_yulang_fence_info(info), "selected: {info:?}");
    }
    for info in [
        "",
        " \t ",
        "Yulang",
        "yulang2",
        "tag yulang",
        "  rust yulang",
        "yulang\n",
        "yulang\r\n",
    ] {
        assert!(!is_yulang_fence_info(info), "raw: {info:?}");
    }
}

#[test]
fn eof_boundary_has_precedence_without_consuming_caller_input() {
    let source = "";
    let pointer = source.as_ptr();
    let decision = judge_fence_line(source, 41, &boundary(FencePrefixPolicy::None, 0));
    assert_eq!(source.as_ptr(), pointer);
    assert_eq!(source, "");
    let FenceLineDecision::Boundary(pending) = decision else {
        panic!("EOF was not a pending boundary");
    };
    assert_eq!(pending.coordinate(), 41);
    assert_eq!(pending.inspected(), &(41..41));
    assert_eq!(pending.kind(), &Boundary::EofAfterTrivia);
}

#[test]
fn unquoted_strict_close_records_physical_ranges_for_lf_crlf_and_eof() {
    for (source, newline) in [
        ("  ``` \t\nnext", Some(107..108)),
        ("  ``` \t\r\nnext", Some(107..109)),
        ("  ``` \t", None),
    ] {
        let decision = judge_fence_line(source, 100, &boundary(FencePrefixPolicy::None, 2));
        let FenceLineDecision::Boundary(pending) = decision else {
            panic!("strict close not borrowed: {source:?}");
        };
        assert_eq!(pending.coordinate(), 100);
        let Boundary::BorrowedClose(BorrowedTarget::YumarkFence(facts)) = pending.into_kind()
        else {
            panic!("strict close not borrowed: {source:?}");
        };
        assert_eq!(facts.line, 100);
        let extent = source.find('\n').map_or(source.len(), |lf| lf + 1);
        assert_eq!(facts.inspected, 100..100 + extent);
        assert_eq!(facts.prefix, None);
        assert_eq!(facts.indentation, 100..102);
        assert_eq!(facts.indentation_column, 2);
        assert_eq!(facts.marker, 102..105);
        assert_eq!(facts.marker_width, 3);
        assert_eq!(facts.horizontal_suffix, 105..107);
        assert_eq!(facts.newline, newline);
    }
}

#[test]
fn unquoted_close_like_text_stays_body() {
    for (source, close_column) in [(" ```\n", 0), ("```x\n", 0), ("````\n", 0)] {
        assert_eq!(
            judge_fence_line(source, 17, &boundary(FencePrefixPolicy::None, close_column)),
            FenceLineDecision::Body {
                prefix: None,
                content: 17,
            },
            "close-like row: {source:?}"
        );
    }
}

#[test]
fn equivalent_prefix_close_is_borrowed_before_prefix_acceptance() {
    let source = " \t> \t>\t```\r\nfollowing";
    let decision = judge_fence_line(
        source,
        50,
        &boundary(
            FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
            0,
        ),
    );
    let FenceLineDecision::Boundary(pending) = decision else {
        panic!("equivalent-prefix close was not borrowed");
    };
    assert_eq!(pending.coordinate(), 50);
    let Boundary::BorrowedClose(BorrowedTarget::YumarkFence(facts)) = pending.into_kind() else {
        panic!("equivalent-prefix close was not borrowed");
    };
    let prefix = facts.prefix.expect("close prefix facts");
    assert_eq!(prefix.depth, 2);
    assert!(!prefix.explicit);
    assert_eq!(
        &source[prefix.extent.start - 50..prefix.extent.end - 50],
        " \t> \t>\t"
    );
    assert_eq!(
        &source[facts.marker.start - 50..facts.marker.end - 50],
        "```"
    );
    assert_eq!(facts.line, 50);
    assert_eq!(facts.inspected, 50..50 + source.find('\n').unwrap() + 1);
}

#[test]
fn equivalent_prefix_variations_become_foreign_body_decoration_after_close_fails() {
    for source in ["> > body\n", " \t>\t> \tbody\n", "> \t> body\n"] {
        let decision = judge_fence_line(
            source,
            70,
            &boundary(
                FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
                0,
            ),
        );
        let FenceLineDecision::Body {
            prefix: Some(prefix),
            content,
        } = decision
        else {
            panic!("same-depth prefix did not continue: {source:?}");
        };
        assert_eq!(prefix.facts.depth, 2);
        assert!(!prefix.facts.explicit);
        assert_eq!(prefix.content, content);
        assert_eq!(&source[content - 70..], "body\n");
    }
}

#[test]
fn non_equivalent_prefixes_stop_with_the_whole_line_unconsumed() {
    for (source, depth, kind) in [
        ("> body\n", 2, QuoteTransitionKind::Reduced),
        ("> > body\n", 1, QuoteTransitionKind::Greater),
        ("body\n", 1, QuoteTransitionKind::NonPrefix),
        (">>>\n", 3, QuoteTransitionKind::Explicit),
    ] {
        let pointer = source.as_ptr();
        let decision = judge_fence_line(
            source,
            300,
            &boundary(FencePrefixPolicy::ActivePrefixQuote { depth, base: 0 }, 0),
        );
        let FenceLineDecision::Boundary(pending) = decision else {
            panic!("transition not returned: {source:?}");
        };
        assert_eq!(pending.coordinate(), 300);
        assert_eq!(pending.inspected(), &(300..300 + source.len()));
        let Boundary::Stop(StopKind::YumarkFence(transition)) = pending.into_kind() else {
            panic!("transition not returned: {source:?}");
        };
        assert_eq!(source.as_ptr(), pointer);
        assert_eq!(transition.line, 300);
        assert_eq!(transition.kind, kind);
        assert_eq!(transition.expected_depth, depth);
        assert_eq!(transition.expected_base, 0);
        let indentation = source
            .bytes()
            .take_while(|byte| matches!(byte, b' ' | b'\t'))
            .count();
        assert_eq!(transition.indentation, 300..300 + indentation);
        assert_eq!(transition.inspected, 300..300 + source.len());
    }
}

#[test]
fn fragment_carrier_is_absent_until_the_first_split_and_preserves_order() {
    let mut pending = None;
    PendingFragments::record(&mut pending, ForeignSplit::quote_prefix(4, 2)).unwrap();
    assert_eq!(pending.as_ref().map(Vec::len), Some(1));
    PendingFragments::record(&mut pending, ForeignSplit::quote_prefix(12, 3)).unwrap();
    assert_eq!(
        pending,
        Some(vec![
            ForeignSplit::quote_prefix(4, 2),
            ForeignSplit::quote_prefix(12, 3),
        ])
    );
}

#[test]
fn item_wide_utf8_crlf_splits_reconstruct_all_parts_after_move_only_handoff() {
    fn handoff(item: Item) -> Item {
        item
    }

    let first = "/*α\r\n> a*/";
    let second = "/*β\r\n> b*/";
    let payload = "γ\r\n> c";
    let origin = 1_000;
    let second_origin = origin + first.len();
    let payload_origin = second_origin + second.len();
    let total = first.len() + second.len() + payload.len();
    let mut pending = None;
    PendingFragments::record(
        &mut pending,
        ForeignSplit::quote_prefix(origin + "/*α\r\n".len(), 2),
    )
    .unwrap();
    PendingFragments::record(
        &mut pending,
        ForeignSplit::quote_prefix(second_origin + "/*β\r\n".len(), 2),
    )
    .unwrap();
    PendingFragments::record(
        &mut pending,
        ForeignSplit::quote_prefix(payload_origin + "γ\r\n".len(), 2),
    )
    .unwrap();
    let item = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
            vec![
                ordinary_trivia(TriviaKind::BlockComment, first),
                ordinary_trivia(TriviaKind::BlockComment, second),
            ]
            .into_boxed_slice(),
        )),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: payload.into(),
        }),
        pending,
        origin,
    )
    .unwrap();
    let item = handoff(item);
    assert_eq!(
        emit_item(item, SyntaxKind::Unknown),
        [
            (SyntaxKind::BlockComment, "/*α\r\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::BlockComment, "a*/".to_owned()),
            (SyntaxKind::BlockComment, "/*β\r\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::BlockComment, "b*/".to_owned()),
            (SyntaxKind::Unknown, "γ\r\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::Unknown, "c".to_owned()),
        ]
    );
    assert_eq!(total, first.len() + second.len() + payload.len());
}

#[test]
fn fragment_validation_rejects_empty_overflow_order_overlap_and_bad_extent() {
    let mut pending = None;
    assert_eq!(
        PendingFragments::record(&mut pending, ForeignSplit::quote_prefix(4, 0)),
        Err(FragmentError::Empty)
    );
    assert!(pending.is_none());
    assert_eq!(
        PendingFragments::record(&mut pending, ForeignSplit::quote_prefix(usize::MAX, 1),),
        Err(FragmentError::Overflow)
    );
    assert!(pending.is_none());

    PendingFragments::record(&mut pending, ForeignSplit::quote_prefix(8, 2)).unwrap();
    assert_eq!(
        PendingFragments::record(&mut pending, ForeignSplit::quote_prefix(7, 1)),
        Err(FragmentError::OutOfOrder)
    );
    assert_eq!(
        PendingFragments::record(&mut pending, ForeignSplit::quote_prefix(9, 2)),
        Err(FragmentError::Overlap)
    );

    assert_eq!(
        Item::finish(
            PhysicalLeadingTrivia::default(),
            Payload::Token(Token {
                kind: TokenKind::Unknown,
                text: "four".into(),
            }),
            Some(vec![ForeignSplit::quote_prefix(3, 2)]),
            4,
        ),
        Err(FragmentError::OutsidePhysicalText)
    );
    assert_eq!(
        Item::finish(
            PhysicalLeadingTrivia::default(),
            Payload::Token(Token {
                kind: TokenKind::Unknown,
                text: "four".into(),
            }),
            Some(vec![ForeignSplit::quote_prefix(4, 0)]),
            4,
        ),
        Err(FragmentError::Empty)
    );
    assert_eq!(
        Item::finish(
            PhysicalLeadingTrivia::default(),
            Payload::Token(Token {
                kind: TokenKind::Unknown,
                text: "four".into(),
            }),
            Some(vec![
                ForeignSplit::quote_prefix(4, 2),
                ForeignSplit::quote_prefix(5, 1),
            ]),
            4,
        ),
        Err(FragmentError::Overlap)
    );
    assert_eq!(
        Item::finish(
            PhysicalLeadingTrivia::default(),
            Payload::Token(Token {
                kind: TokenKind::Unknown,
                text: "four".into(),
            }),
            Some(vec![ForeignSplit::quote_prefix(usize::MAX, 1)]),
            0,
        ),
        Err(FragmentError::Overflow)
    );
    assert_eq!(
        Item::finish(
            PhysicalLeadingTrivia::default(),
            Payload::Token(Token {
                kind: TokenKind::Unknown,
                text: "αb".into(),
            }),
            Some(vec![ForeignSplit::quote_prefix(5, 1)]),
            4,
        ),
        Err(FragmentError::InvalidTextBoundary)
    );
    assert_eq!(
        Item::finish(
            PhysicalLeadingTrivia::default(),
            Payload::Token(Token {
                kind: TokenKind::Unknown,
                text: "abcdef".into(),
            }),
            Some(vec![
                ForeignSplit::quote_prefix(7, 1),
                ForeignSplit::quote_prefix(6, 1),
            ]),
            4,
        ),
        Err(FragmentError::OutOfOrder)
    );

    assert!(
        Item::finish(
            PhysicalLeadingTrivia::default(),
            Payload::Token(Token {
                kind: TokenKind::Unknown,
                text: "four".into(),
            }),
            Some(vec![ForeignSplit::quote_prefix(4, 1)]),
            4,
        )
        .is_ok(),
        "atomic construction derives the physical length"
    );

    assert_eq!(
        Item::finish(
            PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
                vec![ordinary_trivia(TriviaKind::Whitespace, "ab")].into_boxed_slice(),
            )),
            Payload::Token(Token {
                kind: TokenKind::Unknown,
                text: "cd".into(),
            }),
            Some(vec![ForeignSplit::quote_prefix(5, 2)]),
            4,
        ),
        Err(FragmentError::CrossesPartBoundary)
    );
}

#[test]
fn ordinary_scanner_items_have_no_fragment_carrier() {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut remaining = "α";
    let item = scan_statement_item(In::new(&mut remaining, &mut recover, ()), 0, 0)
        .expect("ordinary scanned item");
    assert_eq!(
        emit_item(item, SyntaxKind::Identifier),
        [(SyntaxKind::Identifier, "α".to_owned())]
    );
}

#[test]
fn item_wide_extent_includes_operator_payload_and_eof_contributes_zero_text() {
    let origin = 80;
    let leading = "> ";
    let operator = "++";
    let operator_item = Item::finish(
        physical_leading([(TriviaKind::YmQuotePrefix, leading.into())]),
        Payload::Operator(OperatorToken {
            text: operator.into(),
            use_: OperatorUse::Nullfix,
        }),
        Some(vec![ForeignSplit::quote_prefix(origin, leading.len())]),
        origin,
    )
    .unwrap();
    assert_eq!(
        emit_item(operator_item, SyntaxKind::Operator),
        [
            (SyntaxKind::YmQuotePrefix, leading.to_owned()),
            (SyntaxKind::Operator, operator.to_owned()),
        ]
    );

    let mut eof_item = Item::finish(
        physical_leading([(TriviaKind::YmQuotePrefix, leading.into())]),
        Payload::Eof,
        Some(vec![ForeignSplit::quote_prefix(origin, leading.len())]),
        origin,
    )
    .unwrap();
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    eof_item.emit_eof_leading(&mut builder);
    builder.finish_node();
    assert_eq!(
        SyntaxNode::new_root(builder.finish())
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [(SyntaxKind::YmQuotePrefix, leading.to_owned())]
    );
}

#[test]
fn pending_boundary_fits_the_existing_operator_payload_envelope() {
    assert!(
        std::mem::size_of::<PendingBoundary>() <= std::mem::size_of::<OperatorToken>(),
        "an inert boundary must not enlarge Payload beyond its existing operator variant"
    );
}

#[test]
fn boundary_payload_keeps_its_leading_trivia() {
    let leading = LeadingTrivia::ordinary(
        vec![ordinary_trivia(TriviaKind::Newline, "\n")].into_boxed_slice(),
    );
    let item = Item::plain(
        leading.clone(),
        Payload::Boundary(PendingBoundary::new(
            9..10,
            Boundary::BorrowedClose(BorrowedTarget::Delimiter(Delimiter::Bracket)),
        )),
    );
    assert!(item.leading_view().has_ordinary_newline());
    assert!(item.payload_view().is_boundary());

    let vocabulary = [
        PendingBoundary::new(20..21, Boundary::Close(Delimiter::Parenthesis)),
        PendingBoundary::new(
            30..31,
            Boundary::BorrowedClose(BorrowedTarget::Delimiter(Delimiter::Brace)),
        ),
        PendingBoundary::new(
            40..42,
            Boundary::Dedent(LayoutEvidence {
                baseline: 2,
                indentation: 1,
            }),
        ),
        PendingBoundary::new(50..51, Boundary::Stop(StopKind::Newline)),
    ];
    assert_eq!(
        vocabulary
            .iter()
            .map(|boundary| (boundary.coordinate(), boundary.inspected().clone()))
            .collect::<Vec<_>>(),
        [(20, 20..21), (30, 30..31), (40, 40..42), (50, 50..51),]
    );
}
