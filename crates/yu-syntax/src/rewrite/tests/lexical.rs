use super::*;
use crate::rewrite::{
    driver::handoff,
    emit::{emit_identifier_core, emit_literal_item, emit_token_item},
    item::{
        BorrowedTarget, Boundary, ForeignSplit, FragmentError, Item, LeadingTrivia, Payload,
        PhysicalLeadingTrivia, StopKind, Token,
    },
    lexer::{
        FencedBlockComment, scan_block_comment_fenced_witness, scan_fenced_prior_trivia_part,
        scan_statement_item,
    },
    yumark::{FenceBoundary, FenceOpener, FencePrefixPolicy, QuoteTransitionKind},
};

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

fn fenced_boundary_item<'source>(
    root: &'source str,
    item_start: usize,
    fence: &FenceBoundary,
) -> (Item, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = &root[item_start..];
    let item_origin = checked_source_coordinate(root, input);
    let mut i = In::new(&mut input, &mut recover, ());
    let mut leading = Vec::new();
    while let Some(part) = i.token(scan_fenced_prior_trivia_part) {
        leading.push(part);
    }
    let accepted_before_comment = checked_source_coordinate(root, i.remainder()) - item_origin;
    let part_origin = item_origin
        .checked_add(accepted_before_comment)
        .expect("comment coordinate");
    assert_eq!(checked_source_coordinate(root, i.remainder()), part_origin);

    let mut foreign = None;
    let scanned = scan_block_comment_fenced_witness(i, part_origin, fence, &mut foreign)
        .expect("fenced block-comment opener");
    let FencedBlockComment::Boundary { accepted, pending } = scanned else {
        panic!("fenced block-comment boundary fixture")
    };
    leading.push(accepted);

    let item = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(leading.into_boxed_slice())),
        Payload::Boundary(pending),
        foreign,
        item_origin,
    )
    .expect("one valid whole-item fragment carrier");
    (item, input)
}

fn checked_source_coordinate(root: &str, suffix: &str) -> usize {
    let coordinate = root
        .len()
        .checked_sub(suffix.len())
        .expect("suffix cannot exceed root");
    assert_eq!(root.as_ptr().wrapping_add(coordinate), suffix.as_ptr());
    coordinate
}

fn emit_accepted_literal_item(item: Item, kind: SyntaxKind) -> GreenNode {
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

fn emit_accepted_token_item(item: Item) -> GreenNode {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = "";
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut i = In::new(&mut input, &mut recover, &mut builder);
    emit_token_item(&mut i, item);
    builder.finish_node();
    builder.finish()
}

fn emit_accepted_identifier(item: Item) -> GreenNode {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = "";
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut i = In::new(&mut input, &mut recover, &mut builder);
    emit_identifier_core(&mut i, item);
    builder.finish_node();
    builder.finish()
}

fn emit_accepted_end(item: Item) -> GreenNode {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut end = crate::rewrite::driver::End { item };
    emit_end(&mut builder, &mut end);
    builder.finish_node();
    builder.finish()
}

fn emit_accepted_boundary(item: Item) -> (GreenNode, super::super::item::PendingBoundary) {
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let boundary = item.emit_terminal_boundary(&mut builder);
    builder.finish_node();
    (builder.finish(), boundary)
}

fn literal_item(text: &str) -> Item {
    Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: text.into(),
        }),
    )
}

#[test]
fn ordinary_block_comment_scanner_remains_unsplit() {
    let source = "/* outer\n> > inner */name";
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let mut item = scan_statement_item(In::new(&mut input, &mut recover, ()), 0, 0)
        .expect("ordinary statement item");

    assert_eq!(input, "");
    assert_eq!(
        emit_pending_leading_tokens(&mut item),
        [(
            SyntaxKind::BlockComment,
            "/* outer\n> > inner */".to_owned()
        )]
    );
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some("name"));
}

#[test]
fn unsplit_literal_item_emits_one_supplied_literal_token() {
    let green = emit_accepted_literal_item(literal_item("α\r\nβ"), SyntaxKind::StringText);
    let root = SyntaxNode::new_root(green);

    assert_eq!(root.to_string(), "α\r\nβ");
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [(SyntaxKind::StringText, "α\r\nβ".to_owned())]
    );
}

#[test]
fn fragmented_literal_item_preserves_source_order_and_quote_prefix_kind() {
    let text = "α\n> > β\r\n> > γ";
    let origin = 17;
    let item = Item::finish(
        PhysicalLeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: text.into(),
        }),
        Some(vec![
            ForeignSplit::quote_prefix(origin + "α\n".len(), "> > ".len()),
            ForeignSplit::quote_prefix(origin + "α\n> > β\r\n".len(), "> > ".len()),
        ]),
        origin,
    )
    .expect("valid literal carrier");

    let green = emit_accepted_literal_item(item, SyntaxKind::RuleLiteralText);
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), text);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::RuleLiteralText, "α\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::RuleLiteralText, "β\r\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::RuleLiteralText, "γ".to_owned()),
        ]
    );
}

#[test]
fn standalone_quote_prefix_is_physical_but_grammar_inert() {
    let item = Item::finish(
        physical_leading([
            (TriviaKind::YmQuotePrefix, "> > ".into()),
            (TriviaKind::Newline, "\r\n".into()),
            (TriviaKind::YmQuotePrefix, "> > ".into()),
            (TriviaKind::Whitespace, "  ".into()),
        ]),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "x".into(),
        }),
        Some(vec![
            ForeignSplit::quote_prefix(0, 4),
            ForeignSplit::quote_prefix(6, 4),
        ]),
        0,
    )
    .expect("physical prefixes have exact matching carrier splits");
    let leading = item.leading_view();

    assert!(leading.has_ordinary_trivia());
    assert!(!leading.is_grammar_empty());
    assert!(!leading.is_adjacent());
    assert!(leading.has_ordinary_newline());
    assert_eq!(leading.indentation_after_newline(), Some(2));
    assert_eq!(leading.remaining_physical_parts(), 4);

    let prefix_only = Item::finish(
        physical_leading([(TriviaKind::YmQuotePrefix, "> ".into())]),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "x".into(),
        }),
        Some(vec![ForeignSplit::quote_prefix(0, 2)]),
        0,
    )
    .expect("prefix-only leading is carrier-backed");
    let prefix_only = prefix_only.leading_view();
    assert!(!prefix_only.has_ordinary_trivia());
    assert!(prefix_only.is_grammar_empty());
    assert!(prefix_only.is_adjacent());
    assert!(!prefix_only.has_ordinary_newline());
    assert_eq!(prefix_only.indentation_after_newline(), None);
}

#[test]
fn standalone_and_embedded_prefixes_validate_and_emit_exactly_once() {
    let origin = 50;
    let prefix = "> ";
    let whitespace = "  ";
    let comment = "/*a\n> b*/";
    let payload = "name";
    let embedded_offset = origin + prefix.len() + whitespace.len() + "/*a\n".len();
    let physical_length = prefix.len() + whitespace.len() + comment.len() + payload.len();
    let item = Item::finish(
        physical_leading([
            (TriviaKind::YmQuotePrefix, prefix.into()),
            (TriviaKind::Whitespace, whitespace.into()),
            (TriviaKind::BlockComment, comment.into()),
        ]),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: payload.into(),
        }),
        Some(vec![
            ForeignSplit::quote_prefix(origin, prefix.len()),
            ForeignSplit::quote_prefix(embedded_offset, "> ".len()),
        ]),
        origin,
    )
    .expect("standalone and embedded prefixes cover physical parts");
    assert_eq!(
        physical_length,
        prefix.len() + whitespace.len() + comment.len() + payload.len()
    );

    let green = emit_accepted_token_item(item);
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.to_string(),
        format!("{prefix}{whitespace}{comment}{payload}")
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::Whitespace, "  ".to_owned()),
            (SyntaxKind::BlockComment, "/*a\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::BlockComment, "b*/".to_owned()),
            (SyntaxKind::Identifier, "name".to_owned()),
        ]
    );
}

#[test]
fn standalone_prefix_requires_one_exact_matching_split() {
    let origin = 7;
    for splits in [
        vec![ForeignSplit::quote_prefix(origin, 1)],
        vec![
            ForeignSplit::quote_prefix(origin, 1),
            ForeignSplit::quote_prefix(origin + 1, 1),
        ],
        vec![ForeignSplit::quote_prefix(origin + 2, 1)],
    ] {
        let result = Item::finish(
            physical_leading([(TriviaKind::YmQuotePrefix, "> ".into())]),
            Payload::Token(Token {
                kind: TokenKind::Identifier,
                text: "x".into(),
            }),
            Some(splits),
            origin,
        );
        assert_eq!(result, Err(FragmentError::ForeignPartMismatch));
    }
}

#[test]
fn embedded_prefix_rejects_non_block_leading_trivia_parts() {
    for (kind, text) in [
        (TriviaKind::Whitespace, "  "),
        (TriviaKind::Newline, "\n"),
        (TriviaKind::LineComment, "// > "),
    ] {
        let result = Item::finish(
            PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
                vec![ordinary_trivia(kind, text)].into_boxed_slice(),
            )),
            Payload::Token(Token {
                kind: TokenKind::Identifier,
                text: "x".into(),
            }),
            Some(vec![ForeignSplit::quote_prefix(0, 1)]),
            0,
        );
        assert_eq!(
            result,
            Err(FragmentError::InvalidForeignPlacement),
            "{kind:?}"
        );
    }
}

#[test]
fn accepted_construction_invariant_failure_cannot_become_nonmatch() {
    fn accepted_path() -> Option<Item> {
        Some(
            Item::finish(
                PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
                    vec![ordinary_trivia(TriviaKind::Whitespace, " ")].into_boxed_slice(),
                )),
                Payload::Token(Token {
                    kind: TokenKind::Identifier,
                    text: "x".into(),
                }),
                Some(vec![ForeignSplit::quote_prefix(0, 1)]),
                0,
            )
            .expect("accepted Item construction invariants are internal failures"),
        )
    }

    assert!(std::panic::catch_unwind(accepted_path).is_err());
}

#[test]
fn fragmented_partial_then_remaining_then_payload_keep_exact_physical_order() {
    let comment = "/*a\n> b*/";
    let payload = "z\n> q";
    let item_origin = 20;
    let payload_origin = item_origin + comment.len() + "\n ".len();
    let mut item = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
            vec![
                ordinary_trivia(TriviaKind::BlockComment, comment),
                ordinary_trivia(TriviaKind::Newline, "\n"),
                ordinary_trivia(TriviaKind::Whitespace, " "),
            ]
            .into_boxed_slice(),
        )),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: payload.into(),
        }),
        Some(vec![
            ForeignSplit::quote_prefix(item_origin + "/*a\n".len(), 2),
            ForeignSplit::quote_prefix(payload_origin + "z\n".len(), 2),
        ]),
        item_origin,
    )
    .expect("embedded splits belong to the block comment and payload");

    let cut = item
        .leading_view()
        .cut_after_last_ordinary_newline()
        .expect("one standalone newline part");
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    item.emit_leading_prefix_with(&mut builder, cut, |_, _| {});
    assert_eq!(item.leading_view().remaining_physical_parts(), 1);
    item.emit_all_remaining_leading(&mut builder);
    item.emit_payload(&mut builder, SyntaxKind::Identifier);
    builder.finish_node();

    let root = SyntaxNode::new_root(builder.finish());
    assert_eq!(root.to_string(), format!("{comment}\n {payload}"));
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::BlockComment, "/*a\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::BlockComment, "b*/".to_owned()),
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "z\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::Identifier, "q".to_owned()),
        ]
    );
}

#[test]
fn accepted_core_emitter_splits_prefixes_inside_payload_text() {
    let origin = 31;
    let text = "name\n> tail";
    let item = Item::finish(
        PhysicalLeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: text.into(),
        }),
        Some(vec![ForeignSplit::quote_prefix(
            origin + "name\n".len(),
            "> ".len(),
        )]),
        origin,
    )
    .expect("embedded payload prefix stays valid");

    let green = emit_accepted_identifier(item);
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), text);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Identifier, "name\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::Identifier, "tail".to_owned()),
        ]
    );
}

#[test]
fn leading_only_end_emits_standalone_prefix_once() {
    let origin = 9;
    let item = Item::finish(
        physical_leading([
            (TriviaKind::YmQuotePrefix, "> ".into()),
            (TriviaKind::Newline, "\n".into()),
        ]),
        Payload::Eof,
        Some(vec![ForeignSplit::quote_prefix(origin, 2)]),
        origin,
    )
    .expect("leading-only prefix covers its physical part");

    let green = emit_accepted_end(item);
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), "> \n");
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::YmQuotePrefix, "> ".to_owned()),
            (SyntaxKind::Newline, "\n".to_owned()),
        ]
    );
}

#[test]
fn fenced_comment_uses_one_whole_item_carrier_and_one_builder() {
    let root = "文書🌱  \n/*α\r\n> > β\n> stop\n";
    let item_start = "文書🌱".len();
    let (item, remainder) = fenced_boundary_item(root, item_start, &active_fence(2));
    let accepted = "  \n/*α\r\n> > β\n";

    assert_eq!(remainder, "> stop\n");
    assert_eq!(
        remainder.as_ptr(),
        root[item_start + accepted.len()..].as_ptr()
    );
    let (green, _) = emit_accepted_boundary(item);
    assert_eq!(green.to_string(), accepted);
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Whitespace, "  ".to_owned()),
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::BlockComment, "/*α\r\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::BlockComment, "β\n".to_owned()),
        ]
    );
}

#[test]
fn fenced_comment_borrows_close_before_consuming_its_prefix() {
    let source = "/* outer\n> > body\r\n> > ``` \t\r\nfollowing";
    let accepted = "/* outer\n> > body\r\n";
    let close = "> > ``` \t\r\nfollowing";
    let (item, remainder) = fenced_boundary_item(source, 0, &active_fence(2));

    assert_eq!(remainder, close);
    assert_eq!(remainder.as_ptr(), source[accepted.len()..].as_ptr());
    let (green, pending) = emit_accepted_boundary(item);
    assert_eq!(green.to_string(), accepted);
    assert_eq!(
        pending.inspected(),
        &(accepted.len()..accepted.len() + "> > ``` \t\r\n".len())
    );
    let Boundary::BorrowedClose(BorrowedTarget::YumarkFence(facts)) = pending.kind() else {
        panic!("legal close must be borrowed")
    };
    let prefix = facts.prefix.as_ref().expect("close prefix facts");
    assert_eq!(
        &source[prefix.extent.clone()],
        "> > ",
        "close prefix is inspected but never recorded or consumed"
    );
    assert_eq!(&source[facts.marker.clone()], "```");
}

#[test]
fn fenced_comment_handoff_moves_the_complete_boundary_item_unchanged() {
    let root = "文書🌱  \n/* outer\n> > body\r\n> > ``` \t\r\nfollowing";
    let item_start = "文書🌱".len();
    let live_suffix = "> > ``` \t\r\nfollowing";
    let (item, remainder) = fenced_boundary_item(root, item_start, &active_fence(2));
    let (expected, expected_remainder) = fenced_boundary_item(root, item_start, &active_fence(2));

    assert_eq!(handoff(item), Err(Either::Left(expected)));
    assert_eq!(remainder, live_suffix);
    assert_eq!(expected_remainder, live_suffix);
    assert_eq!(
        remainder.as_ptr(),
        root[root.len() - live_suffix.len()..].as_ptr()
    );
}

#[test]
fn fenced_comment_returns_each_quote_transition_untouched() {
    for (line, depth, expected) in [
        ("> body\nnext", 2, QuoteTransitionKind::Reduced),
        ("> > > body\nnext", 2, QuoteTransitionKind::Greater),
        ("body\nnext", 2, QuoteTransitionKind::NonPrefix),
        (">>>\nnext", 3, QuoteTransitionKind::Explicit),
    ] {
        let source = format!("/* open\n{line}");
        let accepted = "/* open\n";
        let boundary_offset = accepted.len();
        let (item, remainder) = fenced_boundary_item(&source, 0, &active_fence(depth));

        assert_eq!(remainder, line, "{expected:?}");
        assert_eq!(remainder.as_ptr(), source[boundary_offset..].as_ptr());
        let (green, pending) = emit_accepted_boundary(item);
        assert_eq!(green.to_string(), accepted);
        let line_extent = line.find('\n').map_or(line.len(), |lf| lf + 1);
        assert_eq!(
            pending.inspected(),
            &(boundary_offset..boundary_offset + line_extent)
        );
        let Boundary::Stop(StopKind::YumarkFence(transition)) = pending.kind() else {
            panic!("transition must stop the cell")
        };
        assert_eq!(transition.kind, expected);
        assert_eq!(transition.line, boundary_offset);
    }
}

#[test]
fn fenced_comment_returns_physical_eof_with_partial_trivia() {
    let source = "/* open\n> > body";
    let (item, remainder) = fenced_boundary_item(source, 0, &active_fence(2));

    assert_eq!(remainder, "");
    assert_eq!(remainder.as_ptr(), source[source.len()..].as_ptr());
    let (green, pending) = emit_accepted_boundary(item);
    assert_eq!(green.to_string(), source);
    assert_eq!(pending.coordinate(), source.len());
    assert_eq!(pending.inspected(), &(source.len()..source.len()));
    assert_eq!(pending.kind(), &Boundary::EofAfterTrivia);
}

#[test]
fn fenced_comment_crlf_utf8_offsets_record_one_split_per_prefix() {
    let root = "外🌱/*α\r\n \t>\t>β\r\n> > γ\r\n> stop";
    let item_start = "外🌱".len();
    let accepted = "/*α\r\n \t>\t>β\r\n> > γ\r\n";
    let (item, remainder) = fenced_boundary_item(root, item_start, &active_fence(2));

    assert_eq!(remainder, "> stop");
    assert_eq!(
        remainder.as_ptr(),
        root[item_start + accepted.len()..].as_ptr()
    );
    let (green, _) = emit_accepted_boundary(item);
    assert_eq!(green.to_string(), accepted);
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        [" \t>\t>".to_owned(), "> > ".to_owned()]
    );
}

#[test]
fn fenced_comment_keeps_nested_depth_across_prefixes_until_boundary() {
    let source = "/* outer\n> > /* inner\n> > */ outer\n> > ```\nrest";
    let accepted = "/* outer\n> > /* inner\n> > */ outer\n";
    let (item, remainder) = fenced_boundary_item(source, 0, &active_fence(2));

    assert_eq!(remainder, "> > ```\nrest");
    assert_eq!(remainder.as_ptr(), source[accepted.len()..].as_ptr());
    let (green, pending) = emit_accepted_boundary(item);
    assert_eq!(green.to_string(), accepted);
    assert!(matches!(
        pending.kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
}

#[test]
fn fenced_comment_nonmatch_restores_source_and_preserves_sentinel_splits() {
    let source = "/x";
    let pointer = source.as_ptr();
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let sentinel = ForeignSplit::quote_prefix(900, 1);
    let mut foreign = Some(vec![sentinel]);
    let result = scan_block_comment_fenced_witness(
        In::new(&mut input, &mut recover, ()),
        0,
        &active_fence(2),
        &mut foreign,
    );

    assert_eq!(result, None);
    assert_eq!(input, source);
    assert_eq!(input.as_ptr(), pointer);
    assert_eq!(foreign, Some(vec![sentinel]));
}

#[test]
fn fenced_comment_can_complete_only_at_zero_nested_depth() {
    let source = "/* outer\n> > /* inner */ outer */tail";
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let mut foreign = None;
    let outcome = scan_block_comment_fenced_witness(
        In::new(&mut input, &mut recover, ()),
        0,
        &active_fence(2),
        &mut foreign,
    )
    .expect("complete fenced block comment");

    let FencedBlockComment::Complete(comment) = outcome else {
        panic!("balanced nesting must complete before ordinary tail source")
    };
    assert_eq!(input, "tail");
    assert_eq!(
        foreign,
        Some(vec![ForeignSplit::quote_prefix(
            "/* outer\n".len(),
            "> > ".len(),
        )])
    );
    let item = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
            vec![comment].into_boxed_slice(),
        )),
        Payload::Eof,
        foreign,
        0,
    )
    .expect("embedded prefix belongs to the accepted block-comment part");
    assert_eq!(
        SyntaxNode::new_root(emit_accepted_end(item)).to_string(),
        "/* outer\n> > /* inner */ outer */"
    );
}

#[test]
fn caller_owned_builder_finishes_after_source_drops() {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut exit = {
        let source = String::from("  αβ  ");
        let mut input = source.as_str();
        expr(In::new(&mut input, &mut recover, &mut builder))
    };
    let Some(Err(Either::Right(end))) = &mut exit else {
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
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("the next item is handed to the enclosing owner")
    };
    assert_eq!(
        emit_pending_leading_tokens(&mut item),
        [(SyntaxKind::Newline, "\n".to_owned())]
    );
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some("β"));
}

#[test]
fn handoff_owns_maximal_comment_trivia_without_source_borrow() {
    for (source, comment) in [
        ("a /*c*/]", "/*c*/"),
        (
            "a /* outer /* inner */ outer */]",
            "/* outer /* inner */ outer */",
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), "a");
        let Some(Err(Either::Left(mut item))) = exit else {
            panic!("the next item is handed to the enclosing owner")
        };
        assert_eq!(
            emit_pending_leading_tokens(&mut item),
            [
                (SyntaxKind::Whitespace, " ".to_owned()),
                (SyntaxKind::BlockComment, comment.to_owned()),
            ]
        );
        assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RBracket));
        assert_eq!(item.payload_view().spelling(), Some("]"));
    }
}

#[test]
fn comment_trivia_separates_ml_arguments() {
    for source in ["a /*c*/β", "a /* outer /* inner */ outer */β"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::MlArgument)
                .count(),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn block_comment_internal_newlines_do_not_form_layout_boundaries() {
    let source = "a /* outer\n inner */b";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::MlArgument)
            .count(),
        1
    );
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
    assert!(item.leading_view().is_grammar_empty());
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Unknown));
    assert_eq!(item.payload_view().spelling(), Some("\u{a0}"));
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
fn decimal_integer_core_keeps_its_direct_tail_chain() {
    let source = "123(a).field::name";
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
            SyntaxKind::IntegerLiteral,
            SyntaxKind::CallTail,
            SyntaxKind::FieldTail,
            SyntaxKind::PathTail,
        ]
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Integer, "123".to_owned()),
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Identifier, "a".to_owned()),
            (SyntaxKind::RParen, ")".to_owned()),
            (SyntaxKind::Dot, ".".to_owned()),
            (SyntaxKind::Identifier, "field".to_owned()),
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Identifier, "name".to_owned()),
        ]
    );
}
