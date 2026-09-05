use super::*;
use crate::rewrite::{
    emit::emit_literal_item,
    item::{BorrowedTarget, Boundary, ForeignSplit, Item, LeadingTrivia, Payload, StopKind},
    literal::{
        LiteralPiece, StringLiteralExit, StringMode, scan_string_close_witness,
        scan_string_opener_witness, scan_string_text_witness, string_literal_witness,
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

fn run_string<'source>(
    source: &'source str,
    origin: usize,
    boundary: &FenceBoundary,
) -> (GreenNode, StringLiteralExit, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let (opener, mode) =
        scan_string_opener_witness(In::new(&mut input, &mut recover, ())).expect("string opener");
    let interior_origin = origin + token_text(&opener).len();
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = string_literal_witness(
        In::new(&mut input, &mut recover, &mut builder),
        opener,
        mode,
        interior_origin,
        boundary,
    );
    builder.finish_node();
    (builder.finish(), exit, input)
}

fn syntax_tokens(green: &GreenNode) -> Vec<(SyntaxKind, String)> {
    SyntaxNode::new_root(green.clone())
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .map(|token| (token.kind(), token.text().to_owned()))
        .collect()
}

fn node_count(green: &GreenNode, kind: SyntaxKind) -> usize {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn node_texts(green: &GreenNode, kind: SyntaxKind) -> Vec<String> {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .filter(|node| node.kind() == kind)
        .map(|node| node.text().to_string())
        .collect()
}

fn syntax_shape(green: &GreenNode) -> String {
    use std::fmt::Write as _;

    fn push_node(shape: &mut String, node: SyntaxNode) {
        write!(shape, "{:?}(", node.kind()).expect("writing to a String cannot fail");
        for (index, child) in node.children_with_tokens().enumerate() {
            if index != 0 {
                shape.push(',');
            }
            match child {
                rowan::NodeOrToken::Node(node) => push_node(shape, node),
                rowan::NodeOrToken::Token(token) => {
                    write!(shape, "{:?}({:?})", token.kind(), token.text())
                        .expect("writing to a String cannot fail");
                }
            }
        }
        shape.push(')');
    }

    let mut shape = String::new();
    push_node(&mut shape, SyntaxNode::new_root(green.clone()));
    shape
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

#[test]
fn string_literal_witness_completes_normal_and_exact_heredoc_before_suffix() {
    let boundary = fence(FencePrefixPolicy::None);
    for (source, expected_tokens, suffix) in [
        (
            "\"α\r\nβ\"tail",
            vec![
                (SyntaxKind::StringStart, "\"".to_owned()),
                (SyntaxKind::StringText, "α\r\nβ".to_owned()),
                (SyntaxKind::StringEnd, "\"".to_owned()),
            ],
            "tail",
        ),
        (
            "\"\"\"α\nβ\"\"\"tail",
            vec![
                (SyntaxKind::StringStart, "\"\"\"".to_owned()),
                (SyntaxKind::StringText, "α\nβ".to_owned()),
                (SyntaxKind::StringEnd, "\"\"\"".to_owned()),
            ],
            "tail",
        ),
    ] {
        let (green, exit, remainder) = run_string(source, 0, &boundary);
        assert_eq!(exit, StringLiteralExit::Complete, "{source:?}");
        assert_eq!(remainder, suffix, "{source:?}");
        assert_eq!(
            remainder.as_ptr(),
            source[source.len() - suffix.len()..].as_ptr()
        );
        assert_eq!(green.to_string(), &source[..source.len() - suffix.len()]);
        assert_eq!(syntax_tokens(&green), expected_tokens, "{source:?}");
        assert_eq!(node_count(&green, SyntaxKind::StringLiteral), 1);
        assert_eq!(node_count(&green, SyntaxKind::Missing), 0);
    }
}

#[test]
fn string_text_boundary_paths_close_with_one_missing_and_preserve_pending_item() {
    for (source, boundary, expected_remainder, expected_text, prefixes) in [
        (
            "\"本文🌱\r\n次\n```\nrest",
            fence(FencePrefixPolicy::None),
            "```\nrest",
            "本文🌱\r\n次\n",
            0,
        ),
        (
            "\"本文\n> > 次\r\n> > ```\nrest",
            active_fence(2),
            "> > ```\nrest",
            "本文\n> > 次\r\n",
            1,
        ),
        (
            "\"本文\n> stop\nrest",
            active_fence(2),
            "> stop\nrest",
            "本文\n",
            0,
        ),
        (
            "\"本文\n> > > stop\nrest",
            active_fence(2),
            "> > > stop\nrest",
            "本文\n",
            0,
        ),
        (
            "\"本文\nstop\nrest",
            active_fence(2),
            "stop\nrest",
            "本文\n",
            0,
        ),
        (
            "\"本文\n>>>\nrest",
            active_fence(3),
            ">>>\nrest",
            "本文\n",
            0,
        ),
        ("\"本文🌱", active_fence(2), "", "本文🌱", 0),
        ("\"", active_fence(2), "", "", 0),
    ] {
        let (green, exit, remainder) = run_string(source, 0, &boundary);
        let StringLiteralExit::Boundary(pending) = exit else {
            panic!("boundary fixture must hand off its pending Item")
        };
        assert_eq!(remainder, expected_remainder, "{source:?}");
        assert_eq!(
            remainder.as_ptr(),
            source[source.len() - remainder.len()..].as_ptr()
        );
        assert_eq!(
            pending,
            expected_pending(remainder, source.len() - remainder.len(), &boundary),
            "{source:?}"
        );
        assert_eq!(node_count(&green, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(node_count(&green, SyntaxKind::StringLiteral), 1);
        assert_eq!(node_count(&green, SyntaxKind::StringInterpolation), 0);
        assert_eq!(
            syntax_tokens(&green)
                .iter()
                .filter(|(kind, _)| *kind == SyntaxKind::YmQuotePrefix)
                .count(),
            prefixes,
            "{source:?}"
        );
        assert_eq!(
            SyntaxNode::new_root(green.clone())
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::StringText)
                .map(|token| token.text().to_owned())
                .collect::<String>(),
            expected_text.replace("> > ", ""),
            "{source:?}"
        );
    }
}

#[test]
fn simple_escape_scalar_lf_and_crlf_keep_the_selected_item_split() {
    let boundary = active_fence(2);
    for (source, expected_tokens, expected_shape) in [
        (
            "\"\\λ\"tail",
            vec![
                (SyntaxKind::StringStart, "\"".to_owned()),
                (SyntaxKind::StringEscapeLead, "\\".to_owned()),
                (SyntaxKind::StringEscapeSimple, "λ".to_owned()),
                (SyntaxKind::StringEnd, "\"".to_owned()),
            ],
            r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeSimple("λ")),StringEnd("\"")))"#,
        ),
        (
            "\"\\uX\"tail",
            vec![
                (SyntaxKind::StringStart, "\"".to_owned()),
                (SyntaxKind::StringEscapeLead, "\\".to_owned()),
                (SyntaxKind::StringEscapeSimple, "u".to_owned()),
                (SyntaxKind::StringText, "X".to_owned()),
                (SyntaxKind::StringEnd, "\"".to_owned()),
            ],
            r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeSimple("u")),StringText("X"),StringEnd("\"")))"#,
        ),
        (
            "\"\\\n> > x\"tail",
            vec![
                (SyntaxKind::StringStart, "\"".to_owned()),
                (SyntaxKind::StringEscapeLead, "\\".to_owned()),
                (SyntaxKind::StringEscapeSimple, "\n".to_owned()),
                (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
                (SyntaxKind::StringText, "x".to_owned()),
                (SyntaxKind::StringEnd, "\"".to_owned()),
            ],
            r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeSimple("\n")),YmQuotePrefix("> > "),StringText("x"),StringEnd("\"")))"#,
        ),
        (
            "\"\\\r\n> > x\"tail",
            vec![
                (SyntaxKind::StringStart, "\"".to_owned()),
                (SyntaxKind::StringEscapeLead, "\\".to_owned()),
                (SyntaxKind::StringEscapeSimple, "\r".to_owned()),
                (SyntaxKind::StringText, "\n".to_owned()),
                (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
                (SyntaxKind::StringText, "x".to_owned()),
                (SyntaxKind::StringEnd, "\"".to_owned()),
            ],
            r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeSimple("\r")),StringText("\n"),YmQuotePrefix("> > "),StringText("x"),StringEnd("\"")))"#,
        ),
    ] {
        let (green, exit, remainder) = run_string(source, 0, &boundary);
        assert_eq!(exit, StringLiteralExit::Complete, "{source:?}");
        assert_eq!(remainder, "tail", "{source:?}");
        assert_eq!(syntax_tokens(&green), expected_tokens, "{source:?}");
        assert_eq!(syntax_shape(&green), expected_shape, "{source:?}");
        assert_eq!(node_count(&green, SyntaxKind::StringEscape), 1);
        assert_eq!(node_count(&green, SyntaxKind::Missing), 0);
    }
}

#[test]
fn escape_sentinel_keeps_quote_or_boundary_for_the_string_owner() {
    let boundary = active_fence(2);
    let (green, exit, remainder) = run_string("\"\\\"tail", 0, &boundary);
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "tail");
    assert_eq!(node_count(&green, SyntaxKind::Missing), 1);
    assert_eq!(
        syntax_tokens(&green),
        [
            (SyntaxKind::StringStart, "\"".to_owned()),
            (SyntaxKind::StringEscapeLead, "\\".to_owned()),
            (SyntaxKind::StringEnd, "\"".to_owned()),
        ]
    );
    assert_eq!(
        syntax_shape(&green),
        r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),Missing()),StringEnd("\"")))"#
    );

    let source = "\"\\\n> > ```\nrest";
    let (green, exit, remainder) = run_string(source, 0, &boundary);
    let StringLiteralExit::Boundary(pending) = exit else {
        panic!("escaped LF must hand the close to the string owner")
    };
    assert_eq!(remainder, "> > ```\nrest");
    assert_eq!(
        pending,
        expected_pending(remainder, source.len() - remainder.len(), &boundary)
    );
    assert_eq!(node_count(&green, SyntaxKind::Missing), 1);
    assert_eq!(node_count(&green, SyntaxKind::StringEscape), 1);
    assert!(
        syntax_tokens(&green)
            .iter()
            .all(|(kind, _)| *kind != SyntaxKind::YmQuotePrefix)
    );
    assert_eq!(
        syntax_shape(&green),
        r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeSimple("\n")),Missing()))"#
    );

    let (green, exit, remainder) = run_string("\"\\", 0, &boundary);
    assert!(matches!(exit, StringLiteralExit::Boundary(_)));
    assert_eq!(remainder, "");
    assert_eq!(node_count(&green, SyntaxKind::Missing), 2);
    assert_eq!(
        syntax_shape(&green),
        r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),Missing()),Missing()))"#
    );
}

#[test]
fn unicode_escape_valid_empty_and_malformed_end_have_exact_recovery() {
    for (source, missing, errors, expected_tokens, expected_shape) in [
        (
            "\"\\u{1aF}\"tail",
            0,
            Vec::<String>::new(),
            vec![
                (SyntaxKind::StringStart, "\"".to_owned()),
                (SyntaxKind::StringEscapeLead, "\\".to_owned()),
                (SyntaxKind::StringEscapeUnicodeStart, "u{".to_owned()),
                (SyntaxKind::StringEscapeUnicodeHex, "1aF".to_owned()),
                (SyntaxKind::StringEscapeUnicodeEnd, "}".to_owned()),
                (SyntaxKind::StringEnd, "\"".to_owned()),
            ],
            r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),StringEscapeUnicodeHex("1aF"),StringEscapeUnicodeEnd("}")),StringEnd("\"")))"#,
        ),
        (
            "\"\\u{}\"tail",
            1,
            Vec::new(),
            vec![
                (SyntaxKind::StringStart, "\"".to_owned()),
                (SyntaxKind::StringEscapeLead, "\\".to_owned()),
                (SyntaxKind::StringEscapeUnicodeStart, "u{".to_owned()),
                (SyntaxKind::StringEscapeUnicodeEnd, "}".to_owned()),
                (SyntaxKind::StringEnd, "\"".to_owned()),
            ],
            r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Missing(),StringEscapeUnicodeEnd("}")),StringEnd("\"")))"#,
        ),
        (
            "\"\\u{g!}\"tail",
            0,
            vec!["g!".to_owned()],
            vec![
                (SyntaxKind::StringStart, "\"".to_owned()),
                (SyntaxKind::StringEscapeLead, "\\".to_owned()),
                (SyntaxKind::StringEscapeUnicodeStart, "u{".to_owned()),
                (SyntaxKind::StringEscapeUnicodeHex, "g!".to_owned()),
                (SyntaxKind::StringEscapeUnicodeEnd, "}".to_owned()),
                (SyntaxKind::StringEnd, "\"".to_owned()),
            ],
            r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Error(StringEscapeUnicodeHex("g!")),StringEscapeUnicodeEnd("}")),StringEnd("\"")))"#,
        ),
    ] {
        let (green, exit, remainder) = run_string(source, 0, &fence(FencePrefixPolicy::None));
        assert_eq!(exit, StringLiteralExit::Complete, "{source:?}");
        assert_eq!(remainder, "tail", "{source:?}");
        assert_eq!(
            node_count(&green, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(node_texts(&green, SyntaxKind::Error), errors, "{source:?}");
        assert_eq!(syntax_tokens(&green), expected_tokens, "{source:?}");
        assert_eq!(syntax_shape(&green), expected_shape, "{source:?}");
    }
}

#[test]
fn unicode_terminator_percent_and_eof_sentinels_remain_unconsumed() {
    struct Case {
        source: &'static str,
        remainder: &'static str,
        missing: usize,
        error: Option<&'static str>,
        exit: u8,
        shape: &'static str,
    }
    for case in [
        Case {
            source: "\"\\u{\"tail",
            remainder: "tail",
            missing: 2,
            error: None,
            exit: 0,
            shape: r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Missing(),Missing()),StringEnd("\"")))"#,
        },
        Case {
            source: "\"\\u{1\"tail",
            remainder: "tail",
            missing: 1,
            error: None,
            exit: 0,
            shape: r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),StringEscapeUnicodeHex("1"),Missing()),StringEnd("\"")))"#,
        },
        Case {
            source: "\"\\u{%fmt",
            remainder: "%fmt",
            missing: 2,
            error: None,
            exit: 1,
            shape: r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Missing(),Missing())))"#,
        },
        Case {
            source: "\"\\u{1%fmt",
            remainder: "%fmt",
            missing: 1,
            error: None,
            exit: 1,
            shape: r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),StringEscapeUnicodeHex("1"),Missing())))"#,
        },
        Case {
            source: "\"\\u{g\"tail",
            remainder: "tail",
            missing: 1,
            error: Some("g"),
            exit: 0,
            shape: r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Error(StringEscapeUnicodeHex("g")),Missing()),StringEnd("\"")))"#,
        },
        Case {
            source: "\"\\u{g%fmt",
            remainder: "%fmt",
            missing: 1,
            error: Some("g"),
            exit: 1,
            shape: r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Error(StringEscapeUnicodeHex("g")),Missing())))"#,
        },
        Case {
            source: "\"\\u{",
            remainder: "",
            missing: 3,
            error: None,
            exit: 2,
            shape: r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Missing(),Missing()),Missing()))"#,
        },
        Case {
            source: "\"\\u{1",
            remainder: "",
            missing: 2,
            error: None,
            exit: 2,
            shape: r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),StringEscapeUnicodeHex("1"),Missing()),Missing()))"#,
        },
        Case {
            source: "\"\\u{g",
            remainder: "",
            missing: 2,
            error: Some("g"),
            exit: 2,
            shape: r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Error(StringEscapeUnicodeHex("g")),Missing()),Missing()))"#,
        },
    ] {
        let (green, exit, remainder) = run_string(case.source, 0, &fence(FencePrefixPolicy::None));
        assert_eq!(remainder, case.remainder, "{:?}", case.source);
        assert_eq!(
            node_count(&green, SyntaxKind::Missing),
            case.missing,
            "{:?}",
            case.source
        );
        assert_eq!(
            node_texts(&green, SyntaxKind::Error),
            case.error
                .into_iter()
                .map(str::to_owned)
                .collect::<Vec<_>>(),
            "{:?}",
            case.source
        );
        assert_eq!(syntax_shape(&green), case.shape, "{:?}", case.source);
        match case.exit {
            0 => assert_eq!(exit, StringLiteralExit::Complete, "{:?}", case.source),
            1 => assert_eq!(
                exit,
                StringLiteralExit::InterpolationStop,
                "{:?}",
                case.source
            ),
            2 => assert!(matches!(exit, StringLiteralExit::Boundary(_))),
            _ => unreachable!(),
        }
        if case.exit == 1 {
            assert_eq!(node_count(&green, SyntaxKind::StringInterpolation), 0);
            assert!(
                syntax_tokens(&green)
                    .iter()
                    .all(|(kind, _)| *kind != SyntaxKind::StringEnd)
            );
        }
    }
}

#[test]
fn multiline_unicode_error_emits_prefix_outside_error_text_and_hands_off_close() {
    let source = "\"\\u{g\n> > h\r\n> > ```\nrest";
    let boundary = active_fence(2);
    let (green, exit, remainder) = run_string(source, 0, &boundary);
    let StringLiteralExit::Boundary(pending) = exit else {
        panic!("malformed unicode must return the fence close")
    };
    assert_eq!(remainder, "> > ```\nrest");
    assert_eq!(
        remainder.as_ptr(),
        source[source.len() - remainder.len()..].as_ptr()
    );
    assert_eq!(
        pending,
        expected_pending(remainder, source.len() - remainder.len(), &boundary)
    );
    assert_eq!(node_count(&green, SyntaxKind::Error), 1);
    assert_eq!(node_texts(&green, SyntaxKind::Error), ["g\n> > h\r\n"]);
    assert_eq!(node_count(&green, SyntaxKind::Missing), 2);
    assert_eq!(
        syntax_tokens(&green),
        [
            (SyntaxKind::StringStart, "\"".to_owned()),
            (SyntaxKind::StringEscapeLead, "\\".to_owned()),
            (SyntaxKind::StringEscapeUnicodeStart, "u{".to_owned()),
            (SyntaxKind::StringEscapeUnicodeHex, "g\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::StringEscapeUnicodeHex, "h\r\n".to_owned()),
        ]
    );
    assert_eq!(
        syntax_shape(&green),
        r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Error(StringEscapeUnicodeHex("g\n"),YmQuotePrefix("> > "),StringEscapeUnicodeHex("h\r\n")),Missing()),Missing()))"#
    );
}

#[test]
fn raw_percent_after_text_is_an_unconsumed_l2_stop_without_recovery() {
    let source = "\"α%format {body}";
    let (green, exit, remainder) = run_string(source, 0, &active_fence(2));
    assert_eq!(exit, StringLiteralExit::InterpolationStop);
    assert_eq!(remainder, "%format {body}");
    assert_eq!(remainder.as_ptr(), source["\"α".len()..].as_ptr());
    assert_eq!(node_count(&green, SyntaxKind::Missing), 0);
    assert_eq!(node_count(&green, SyntaxKind::StringInterpolation), 0);
    assert_eq!(
        syntax_tokens(&green),
        [
            (SyntaxKind::StringStart, "\"".to_owned()),
            (SyntaxKind::StringText, "α".to_owned()),
        ]
    );
}

#[test]
fn structural_item_after_body_prefix_owns_that_prefix() {
    let boundary = active_fence(2);

    let source = "\"α\n> > \\q\"tail";
    let (green, exit, remainder) = run_string(source, 0, &boundary);
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "tail");
    assert_eq!(
        syntax_shape(&green),
        r#"Root(StringLiteral(StringStart("\""),StringText("α\n"),StringEscape(YmQuotePrefix("> > "),StringEscapeLead("\\"),StringEscapeSimple("q")),StringEnd("\"")))"#
    );

    let source = "\"\\u{g\n> > }\"tail";
    let (green, exit, remainder) = run_string(source, 0, &boundary);
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "tail");
    assert_eq!(node_texts(&green, SyntaxKind::Error), ["g\n"]);
    assert_eq!(
        syntax_shape(&green),
        r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Error(StringEscapeUnicodeHex("g\n")),YmQuotePrefix("> > "),StringEscapeUnicodeEnd("}")),StringEnd("\"")))"#
    );

    let source = "\"α\n> > %format {body}";
    let (green, exit, remainder) = run_string(source, 0, &boundary);
    assert_eq!(exit, StringLiteralExit::InterpolationStop);
    assert_eq!(remainder, "> > %format {body}");
    assert_eq!(remainder.as_ptr(), source["\"α\n".len()..].as_ptr());
    assert_eq!(
        syntax_shape(&green),
        r#"Root(StringLiteral(StringStart("\""),StringText("α\n")))"#
    );

    let source = "\"\\u{g\n> > %format {body}";
    let (green, exit, remainder) = run_string(source, 0, &boundary);
    assert_eq!(exit, StringLiteralExit::InterpolationStop);
    assert_eq!(remainder, "> > %format {body}");
    assert_eq!(remainder.as_ptr(), source["\"\\u{g\n".len()..].as_ptr());
    assert_eq!(node_texts(&green, SyntaxKind::Error), ["g\n"]);
    assert_eq!(
        syntax_shape(&green),
        r#"Root(StringLiteral(StringStart("\""),StringEscape(StringEscapeLead("\\"),StringEscapeUnicodeStart("u{"),Error(StringEscapeUnicodeHex("g\n")),Missing())))"#
    );
}

#[test]
fn escaped_lf_and_crlf_preserve_every_fence_transition_item() {
    for newline in ["\n", "\r\n"] {
        for (line, depth, expected) in [
            ("> body\nnext", 2, QuoteTransitionKind::Reduced),
            ("> > > body\nnext", 2, QuoteTransitionKind::Greater),
            ("body\nnext", 2, QuoteTransitionKind::NonPrefix),
            (">>>\nnext", 3, QuoteTransitionKind::Explicit),
        ] {
            let source = format!("\"\\{newline}{line}");
            let boundary = active_fence(depth);
            let (green, exit, remainder) = run_string(&source, 0, &boundary);
            let StringLiteralExit::Boundary(pending) = exit else {
                panic!("escaped {newline:?} must return {expected:?}")
            };
            assert_eq!(remainder, line, "{newline:?} {expected:?}");
            assert_eq!(
                remainder.as_ptr(),
                source[source.len() - line.len()..].as_ptr(),
                "{newline:?} {expected:?}"
            );
            assert_eq!(
                pending,
                expected_pending(remainder, source.len() - line.len(), &boundary),
                "{newline:?} {expected:?}"
            );
            let Payload::Boundary(ref pending_boundary) = pending.payload else {
                panic!("escaped transition remains a typed pending Item")
            };
            let Boundary::Stop(StopKind::YumarkFence(transition)) = pending_boundary.kind() else {
                panic!("escaped transition remains a Yumark stop")
            };
            assert_eq!(transition.kind, expected, "{newline:?}");
            assert_eq!(node_count(&green, SyntaxKind::Missing), 1);
            assert_eq!(node_count(&green, SyntaxKind::StringEscape), 1);
        }
    }
}
