use super::*;
use crate::rewrite::{
    emit::emit_literal_item,
    item::{BorrowedTarget, Boundary, ForeignSplit, Item, LeadingTrivia, Payload, StopKind},
    literal::{
        LiteralPiece, StringMode, scan_string_close_witness, scan_string_opener_witness,
        scan_string_text_witness,
    },
    yumark::{
        FenceBoundary, FenceLineDecision, FenceOpener, FencePrefixPolicy, QuoteTransitionKind,
        judge_fence_line,
    },
};

fn fence(prefix_policy: FencePrefixPolicy) -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy,
        close_column: 0,
    }
}

fn active_fence(depth: usize) -> FenceBoundary {
    fence(FencePrefixPolicy::ActivePrefixQuote { depth, base: 0 })
}

fn scan_opener(source: &str) -> ((Item, StringMode), &str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let opener =
        scan_string_opener_witness(In::new(&mut input, &mut recover, ())).expect("literal opener");
    (opener, input)
}

fn scan_close(source: &str, mode: StringMode) -> (Option<Item>, &str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let close = scan_string_close_witness(In::new(&mut input, &mut recover, ()), mode);
    (close, input)
}

fn scan_text<'source>(
    source: &'source str,
    origin: usize,
    boundary: &FenceBoundary,
    mode: StringMode,
) -> (LiteralPiece, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let piece = scan_string_text_witness(
        In::new(&mut input, &mut recover, ()),
        origin,
        boundary,
        mode,
    );
    (piece, input)
}

fn token_text(item: &Item) -> &str {
    let Payload::Token(token) = &item.payload else {
        panic!("literal witness emits a token Item")
    };
    &token.text
}

fn expected_pending(source: &str, coordinate: usize, boundary: &FenceBoundary) -> Item {
    let FenceLineDecision::Boundary(pending) = judge_fence_line(source, coordinate, boundary)
    else {
        panic!("fixture must denote a fence boundary")
    };
    Item::plain(LeadingTrivia::default(), Payload::Boundary(pending))
}

fn emit_literal(item: Item, kind: SyntaxKind) -> GreenNode {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = "";
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut i = In::new(&mut input, &mut recover, &mut builder);
    emit_literal_item(&mut i, item, kind);
    builder.finish_node();
    builder.finish()
}

#[test]
fn literal_quote_openers_classify_one_three_four_and_empty_normal() {
    for (source, expected_text, expected_mode, remainder) in [
        ("\"tail", "\"", StringMode::Normal, "tail"),
        (
            "\"\"\"tail",
            "\"\"\"",
            StringMode::Heredoc { quotes: 3 },
            "tail",
        ),
        (
            "\"\"\"\"tail",
            "\"\"\"\"",
            StringMode::Heredoc { quotes: 4 },
            "tail",
        ),
    ] {
        let ((opener, mode), actual_remainder) = scan_opener(source);
        assert_eq!(token_text(&opener), expected_text, "{source:?}");
        assert_eq!(mode, expected_mode, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
    }

    let ((opener, mode), remainder) = scan_opener("\"\"tail");
    assert_eq!(mode, StringMode::Normal);
    assert_eq!(token_text(&opener), "\"");
    assert_eq!(remainder, "\"tail");
    let (close, remainder) = scan_close(remainder, mode);
    assert_eq!(
        token_text(close.as_ref().expect("empty normal close")),
        "\""
    );
    assert_eq!(remainder, "tail");
}

#[test]
fn heredoc_close_requires_the_exact_whole_quote_run() {
    let mode = StringMode::Heredoc { quotes: 3 };
    for source in ["\"\"tail", "\"\"\"\"tail"] {
        let start = source.as_ptr();
        let (close, remainder) = scan_close(source, mode);
        assert!(close.is_none(), "{source:?}");
        assert_eq!(remainder, source, "{source:?}");
        assert_eq!(remainder.as_ptr(), start, "{source:?}");
    }

    for (source, accepted) in [
        ("\"\"x\"\"\"tail", "\"\"x"),
        ("\"\"\"\"x\"\"\"tail", "\"\"\"\"x"),
    ] {
        let (piece, remainder) = scan_text(source, 0, &fence(FencePrefixPolicy::None), mode);
        let LiteralPiece::Complete(item) = piece else {
            panic!("an exact later close completes the preceding text Item")
        };
        assert_eq!(token_text(&item), accepted, "{source:?}");
        assert_eq!(remainder, "\"\"\"tail", "{source:?}");
        let (close, remainder) = scan_close(remainder, mode);
        assert_eq!(token_text(close.as_ref().expect("exact close")), "\"\"\"");
        assert_eq!(remainder, "tail");
    }
}

#[test]
fn multiline_text_keeps_utf8_crlf_coordinates_and_direct_close_unconsumed() {
    let root = "前🌱α\r\nβ\n```\r\nrest";
    let origin = "前🌱".len();
    let source = &root[origin..];
    let accepted_text = "α\r\nβ\n";
    let boundary = fence(FencePrefixPolicy::None);
    let (piece, remainder) = scan_text(source, origin, &boundary, StringMode::Normal);
    let LiteralPiece::Boundary {
        accepted: Some(accepted),
        pending,
    } = piece
    else {
        panic!("the direct fence close stops literal text")
    };

    assert_eq!(token_text(&accepted), accepted_text);
    assert!(accepted.fragments().is_none());
    assert_eq!(remainder, "```\r\nrest");
    assert_eq!(
        remainder.as_ptr(),
        root[origin + accepted_text.len()..].as_ptr()
    );
    assert_eq!(
        pending,
        expected_pending(remainder, origin + accepted_text.len(), &boundary)
    );
    assert!(matches!(
        pending.payload,
        Payload::Boundary(ref boundary)
            if matches!(boundary.kind(), Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_)))
    ));
}

#[test]
fn prefixed_body_records_one_split_and_prefixed_close_stays_unconsumed() {
    let source = "α\n> > β\r\n> > ```\nrest";
    let accepted_text = "α\n> > β\r\n";
    let boundary = active_fence(2);
    let (piece, remainder) = scan_text(source, 0, &boundary, StringMode::Normal);
    let LiteralPiece::Boundary {
        accepted: Some(accepted),
        pending,
    } = piece
    else {
        panic!("the prefixed close stops literal text")
    };

    assert_eq!(token_text(&accepted), accepted_text);
    assert_eq!(remainder, "> > ```\nrest");
    assert_eq!(remainder.as_ptr(), source[accepted_text.len()..].as_ptr());
    let fragments = accepted.fragments().expect("one body quote prefix");
    assert_eq!(
        fragments.foreign(),
        &[ForeignSplit::quote_prefix("α\n".len(), "> > ".len())]
    );
    assert_eq!(
        pending,
        expected_pending(remainder, accepted_text.len(), &boundary)
    );

    let green = emit_literal(accepted, SyntaxKind::StringText);
    assert_eq!(green.to_string(), accepted_text);
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::StringText, "α\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::StringText, "β\r\n".to_owned()),
        ]
    );
}

#[test]
fn every_quote_transition_returns_the_judged_item_untouched() {
    for (line, depth, expected) in [
        ("> body\nnext", 2, QuoteTransitionKind::Reduced),
        ("> > > body\nnext", 2, QuoteTransitionKind::Greater),
        ("body\nnext", 2, QuoteTransitionKind::NonPrefix),
        (">>>\nnext", 3, QuoteTransitionKind::Explicit),
    ] {
        let source = format!("本文🌱\n{line}");
        let accepted_text = "本文🌱\n";
        let boundary = active_fence(depth);
        let (piece, remainder) = scan_text(&source, 0, &boundary, StringMode::Normal);
        let LiteralPiece::Boundary {
            accepted: Some(accepted),
            pending,
        } = piece
        else {
            panic!("transition returns the completed text Item and pending Item")
        };

        assert_eq!(token_text(&accepted), accepted_text, "{expected:?}");
        assert!(accepted.fragments().is_none(), "{expected:?}");
        assert_eq!(remainder, line, "{expected:?}");
        assert_eq!(remainder.as_ptr(), source[accepted_text.len()..].as_ptr());
        assert_eq!(
            pending,
            expected_pending(remainder, accepted_text.len(), &boundary),
            "{expected:?}"
        );
        let Payload::Boundary(pending) = pending.payload else {
            panic!("transition stays a typed boundary")
        };
        let Boundary::Stop(StopKind::YumarkFence(transition)) = pending.into_kind() else {
            panic!("transition stays a Yumark fence stop")
        };
        assert_eq!(transition.kind, expected);
    }
}

#[test]
fn physical_eof_returns_pending_item_with_or_without_accepted_text() {
    let boundary = active_fence(2);
    let (piece, remainder) = scan_text("", 41, &boundary, StringMode::Normal);
    let LiteralPiece::Boundary {
        accepted: None,
        pending,
    } = piece
    else {
        panic!("empty input returns only EOF")
    };
    assert_eq!(remainder, "");
    assert_eq!(pending, expected_pending("", 41, &boundary));

    let source = "終端🌱";
    let (piece, remainder) = scan_text(source, 41, &boundary, StringMode::Normal);
    let LiteralPiece::Boundary {
        accepted: Some(accepted),
        pending,
    } = piece
    else {
        panic!("accepted text precedes EOF")
    };
    assert_eq!(token_text(&accepted), source);
    assert!(accepted.fragments().is_none());
    assert_eq!(remainder, "");
    assert_eq!(remainder.as_ptr(), source[source.len()..].as_ptr());
    assert_eq!(pending, expected_pending("", 41 + source.len(), &boundary));
}
