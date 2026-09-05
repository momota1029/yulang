use chasa_recover::In;

use crate::operator::OperatorTable;

use super::super::{
    item::{
        BorrowedTarget, Boundary, Delimiter, ForeignKind, ForeignSplit, FragmentError, Item,
        ItemTextPart, LayoutEvidence, LeadingTrivia, OperatorToken, OperatorUse, Payload,
        PendingBoundary, PendingFragments, StopKind, Token, TokenKind, Trivia, TriviaKind,
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

#[derive(Debug, Eq, PartialEq)]
enum Reconstructed<'text> {
    Ordinary(ItemTextPart, &'text str),
    QuotePrefix(ItemTextPart, &'text str),
}

fn reconstruct(item: &Item) -> Vec<Reconstructed<'_>> {
    let mut reconstructed = Vec::new();
    for part in item.fragmented_parts().expect("fragmented item parts") {
        let mut cursor = 0;
        for split in part.foreign {
            let start = split.offset - part.physical.start;
            let end = start + split.length;
            if cursor < start {
                reconstructed.push(Reconstructed::Ordinary(
                    part.kind,
                    &part.text[cursor..start],
                ));
            }
            assert_eq!(split.kind, ForeignKind::YmQuotePrefix);
            reconstructed.push(Reconstructed::QuotePrefix(
                part.kind,
                &part.text[start..end],
            ));
            cursor = end;
        }
        if cursor < part.text.len() {
            reconstructed.push(Reconstructed::Ordinary(part.kind, &part.text[cursor..]));
        }
    }
    reconstructed
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
    assert_eq!(PendingFragments::finish(None, 4, 11), Ok(None));
    assert_eq!(PendingFragments::finish(Some(Vec::new()), 4, 11), Ok(None));

    let mut pending = None;
    PendingFragments::record(&mut pending, ForeignSplit::quote_prefix(4, 2)).unwrap();
    assert_eq!(pending.as_ref().map(Vec::len), Some(1));
    PendingFragments::record(&mut pending, ForeignSplit::quote_prefix(12, 3)).unwrap();
    let fragments = PendingFragments::finish(pending, 4, 11)
        .unwrap()
        .expect("split carrier");
    assert_eq!(fragments.physical(), &(4..15));
    assert_eq!(
        fragments.foreign(),
        &[
            ForeignSplit {
                offset: 4,
                length: 2,
                kind: ForeignKind::YmQuotePrefix,
            },
            ForeignSplit {
                offset: 12,
                length: 3,
                kind: ForeignKind::YmQuotePrefix,
            },
        ]
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
    let fragments = PendingFragments::finish(pending, origin, total)
        .unwrap()
        .expect("split carrier");
    let pointer = fragments.foreign().as_ptr();
    let mut item = Item::plain(
        LeadingTrivia(
            vec![
                Trivia {
                    kind: TriviaKind::BlockComment,
                    text: first.into(),
                },
                Trivia {
                    kind: TriviaKind::BlockComment,
                    text: second.into(),
                },
            ]
            .into_boxed_slice(),
        ),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: payload.into(),
        }),
    );
    item.with_fragments(fragments).unwrap();
    let mut item = handoff(item);
    assert_eq!(
        item.fragments().expect("moved carrier").foreign().as_ptr(),
        pointer
    );
    assert_eq!(
        reconstruct(&item),
        [
            Reconstructed::Ordinary(ItemTextPart::LeadingTrivia(0), "/*α\r\n"),
            Reconstructed::QuotePrefix(ItemTextPart::LeadingTrivia(0), "> "),
            Reconstructed::Ordinary(ItemTextPart::LeadingTrivia(0), "a*/"),
            Reconstructed::Ordinary(ItemTextPart::LeadingTrivia(1), "/*β\r\n"),
            Reconstructed::QuotePrefix(ItemTextPart::LeadingTrivia(1), "> "),
            Reconstructed::Ordinary(ItemTextPart::LeadingTrivia(1), "b*/"),
            Reconstructed::Ordinary(ItemTextPart::PayloadToken, "γ\r\n"),
            Reconstructed::QuotePrefix(ItemTextPart::PayloadToken, "> "),
            Reconstructed::Ordinary(ItemTextPart::PayloadToken, "c"),
        ]
    );

    let second_carrier = PendingFragments::finish(
        Some(vec![ForeignSplit::quote_prefix(origin + 1, 1)]),
        origin,
        total,
    )
    .unwrap()
    .expect("second carrier");
    assert_eq!(
        item.with_fragments(second_carrier),
        Err(FragmentError::AlreadyAttached)
    );
    assert_eq!(
        item.fragments()
            .expect("original carrier")
            .foreign()
            .as_ptr(),
        pointer
    );
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
        PendingFragments::finish(Some(vec![ForeignSplit::quote_prefix(3, 2)]), 4, 4),
        Err(FragmentError::OutsidePhysicalText)
    );
    assert_eq!(
        PendingFragments::finish(Some(vec![ForeignSplit::quote_prefix(4, 0)]), 4, 4),
        Err(FragmentError::Empty)
    );
    assert_eq!(
        PendingFragments::finish(
            Some(vec![
                ForeignSplit::quote_prefix(4, 2),
                ForeignSplit::quote_prefix(5, 1),
            ]),
            4,
            4,
        ),
        Err(FragmentError::Overlap)
    );
    assert_eq!(
        PendingFragments::finish(
            Some(vec![ForeignSplit::quote_prefix(usize::MAX, 1)]),
            0,
            usize::MAX,
        ),
        Err(FragmentError::Overflow)
    );
    let invalid_utf8 =
        PendingFragments::finish(Some(vec![ForeignSplit::quote_prefix(5, 1)]), 4, "αb".len())
            .unwrap()
            .expect("numerically valid carrier");
    let mut invalid_utf8_item = Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: "αb".into(),
        }),
    );
    assert_eq!(
        invalid_utf8_item.with_fragments(invalid_utf8),
        Err(FragmentError::InvalidTextBoundary)
    );
    assert_eq!(
        PendingFragments::finish(
            Some(vec![
                ForeignSplit::quote_prefix(7, 1),
                ForeignSplit::quote_prefix(6, 1),
            ]),
            4,
            6,
        ),
        Err(FragmentError::OutOfOrder)
    );

    let wrong_length = PendingFragments::finish(Some(vec![ForeignSplit::quote_prefix(4, 1)]), 4, 5)
        .unwrap()
        .expect("numerically valid carrier");
    let mut wrong_length_item = Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: "four".into(),
        }),
    );
    assert_eq!(
        wrong_length_item.with_fragments(wrong_length),
        Err(FragmentError::PhysicalLengthMismatch)
    );

    let crossing = PendingFragments::finish(Some(vec![ForeignSplit::quote_prefix(5, 2)]), 4, 4)
        .unwrap()
        .expect("numerically valid carrier");
    let mut crossing_item = Item::plain(
        LeadingTrivia(
            vec![Trivia {
                kind: TriviaKind::Whitespace,
                text: "ab".into(),
            }]
            .into_boxed_slice(),
        ),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: "cd".into(),
        }),
    );
    assert_eq!(
        crossing_item.with_fragments(crossing),
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
    assert!(item.fragments().is_none());
}

#[test]
fn item_wide_extent_includes_operator_payload_and_eof_contributes_zero_text() {
    let origin = 80;
    let leading = "> ";
    let operator = "++";
    let fragments = PendingFragments::finish(
        Some(vec![ForeignSplit::quote_prefix(origin, leading.len())]),
        origin,
        leading.len() + operator.len(),
    )
    .unwrap()
    .expect("operator item carrier");
    let mut operator_item = Item::plain(
        LeadingTrivia(
            vec![Trivia {
                kind: TriviaKind::Whitespace,
                text: leading.into(),
            }]
            .into_boxed_slice(),
        ),
        Payload::Operator(OperatorToken {
            text: operator.into(),
            use_: OperatorUse::Nullfix,
        }),
    );
    operator_item.with_fragments(fragments).unwrap();
    assert_eq!(
        operator_item
            .fragmented_parts()
            .expect("operator item parts")
            .map(|part| (part.kind, part.physical, part.text))
            .collect::<Vec<_>>(),
        [
            (ItemTextPart::LeadingTrivia(0), origin..origin + 2, leading),
            (
                ItemTextPart::PayloadOperator,
                origin + 2..origin + 4,
                operator,
            ),
        ]
    );

    let eof_fragments = PendingFragments::finish(
        Some(vec![ForeignSplit::quote_prefix(origin, leading.len())]),
        origin,
        leading.len(),
    )
    .unwrap()
    .expect("EOF item carrier");
    let mut eof_item = Item::plain(
        LeadingTrivia(
            vec![Trivia {
                kind: TriviaKind::Whitespace,
                text: leading.into(),
            }]
            .into_boxed_slice(),
        ),
        Payload::Eof,
    );
    eof_item.with_fragments(eof_fragments).unwrap();
    assert_eq!(
        eof_item
            .fragmented_parts()
            .expect("EOF item parts")
            .map(|part| (part.kind, part.physical, part.text))
            .collect::<Vec<_>>(),
        [(ItemTextPart::LeadingTrivia(0), origin..origin + 2, leading)]
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
    let leading = LeadingTrivia(
        vec![Trivia {
            kind: TriviaKind::Newline,
            text: "\n".into(),
        }]
        .into_boxed_slice(),
    );
    let item = Item::plain(
        leading.clone(),
        Payload::Boundary(PendingBoundary::new(
            9..10,
            Boundary::BorrowedClose(BorrowedTarget::Delimiter(Delimiter::Bracket)),
        )),
    );
    assert_eq!(item.leading, leading);
    assert!(item.fragments().is_none());

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
