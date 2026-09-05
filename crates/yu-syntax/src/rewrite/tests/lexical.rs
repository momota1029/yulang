use super::*;
use crate::rewrite::{
    driver::handoff,
    emit::emit_fragmented_item,
    item::{
        BorrowedTarget, Boundary, ForeignKind, ForeignSplit, Item, ItemTextPart, LeadingTrivia,
        Payload, PendingFragments, StopKind,
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
    let accepted_before_comment = leading
        .iter()
        .try_fold(0usize, |length, part| length.checked_add(part.text.len()))
        .expect("accepted trivia length");
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
    let physical_length = accepted_before_comment
        .checked_add(accepted.text.len())
        .expect("whole item length");
    leading.push(accepted);

    let fragments = PendingFragments::finish(foreign, item_origin, physical_length)
        .expect("one valid whole-item fragment carrier");
    let mut item = Item::plain(
        LeadingTrivia(leading.into_boxed_slice()),
        Payload::Boundary(pending),
    );
    if let Some(fragments) = fragments {
        item.with_fragments(fragments)
            .expect("carrier covers preceding trivia and comment");
    }
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

fn emit_accepted_fragmented_item(item: &Item) -> GreenNode {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = "";
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let mut i = In::new(&mut input, &mut recover, &mut builder);
    emit_fragmented_item(&mut i, item);
    builder.finish_node();
    builder.finish()
}

fn leading_text(item: &Item) -> String {
    item.leading.0.iter().map(|part| &*part.text).collect()
}

#[test]
fn ordinary_block_comment_scanner_remains_unsplit() {
    let source = "/* outer\n> > inner */name";
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let item = scan_statement_item(In::new(&mut input, &mut recover, ()), 0, 0)
        .expect("ordinary statement item");

    assert_eq!(input, "");
    assert_eq!(item.fragments(), None);
    assert_eq!(
        item.leading
            .0
            .iter()
            .map(|part| (part.kind, &*part.text))
            .collect::<Vec<_>>(),
        [(TriviaKind::BlockComment, "/* outer\n> > inner */")]
    );
    assert!(matches!(
        item.payload,
        Payload::Token(ref token)
            if token.kind == TokenKind::Identifier && &*token.text == "name"
    ));
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
    assert_eq!(leading_text(&item), accepted);
    assert_eq!(
        item.leading
            .0
            .iter()
            .map(|part| (part.kind, &*part.text))
            .collect::<Vec<_>>(),
        [
            (TriviaKind::Whitespace, "  "),
            (TriviaKind::Newline, "\n"),
            (TriviaKind::BlockComment, "/*α\r\n> > β\n"),
        ]
    );

    let fragments = item.fragments().expect("one accepted quote prefix");
    assert_eq!(
        fragments.physical(),
        &(item_start..item_start + accepted.len())
    );
    assert_eq!(
        fragments.foreign(),
        &[ForeignSplit::quote_prefix(
            item_start + "  \n/*α\r\n".len(),
            "> > ".len(),
        )]
    );
    assert_eq!(
        item.fragmented_parts()
            .expect("whole item fragments")
            .map(|part| (part.kind, part.text.to_owned()))
            .collect::<Vec<_>>(),
        [
            (ItemTextPart::LeadingTrivia(0), "  ".to_owned()),
            (ItemTextPart::LeadingTrivia(1), "\n".to_owned()),
            (ItemTextPart::LeadingTrivia(2), "/*α\r\n> > β\n".to_owned(),),
        ]
    );

    let green = emit_accepted_fragmented_item(&item);
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
    assert_eq!(leading_text(&item), accepted);
    let fragments = item
        .fragments()
        .expect("the earlier body prefix is accepted");
    assert_eq!(fragments.foreign().len(), 1);
    assert_eq!(
        fragments.foreign()[0],
        ForeignSplit::quote_prefix("/* outer\n".len(), "> > ".len())
    );
    assert_eq!(emit_accepted_fragmented_item(&item).to_string(), accepted);

    let Payload::Boundary(pending) = &item.payload else {
        panic!("fenced comment must return a typed close")
    };
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
        assert_eq!(leading_text(&item), accepted);
        assert_eq!(item.fragments(), None);
        let Payload::Boundary(pending) = &item.payload else {
            panic!("transition must remain typed")
        };
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
    assert_eq!(leading_text(&item), source);
    let Payload::Boundary(pending) = &item.payload else {
        panic!("unterminated comment must return EOF")
    };
    assert_eq!(pending.coordinate(), source.len());
    assert_eq!(pending.inspected(), &(source.len()..source.len()));
    assert_eq!(pending.kind(), &Boundary::EofAfterTrivia);
    assert_eq!(
        item.fragments()
            .expect("accepted body prefix")
            .foreign()
            .len(),
        1
    );
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
    let fragments = item.fragments().expect("two accepted prefixes");
    assert_eq!(
        fragments.foreign(),
        &[
            ForeignSplit::quote_prefix(item_start + "/*α\r\n".len(), " \t>\t>".len(),),
            ForeignSplit::quote_prefix(item_start + "/*α\r\n \t>\t>β\r\n".len(), "> > ".len(),),
        ]
    );
    assert!(
        fragments
            .foreign()
            .iter()
            .all(|split| split.kind == ForeignKind::YmQuotePrefix)
    );
}

#[test]
fn fenced_comment_keeps_nested_depth_across_prefixes_until_boundary() {
    let source = "/* outer\n> > /* inner\n> > */ outer\n> > ```\nrest";
    let accepted = "/* outer\n> > /* inner\n> > */ outer\n";
    let (item, remainder) = fenced_boundary_item(source, 0, &active_fence(2));

    assert_eq!(remainder, "> > ```\nrest");
    assert_eq!(remainder.as_ptr(), source[accepted.len()..].as_ptr());
    assert_eq!(leading_text(&item), accepted);
    assert_eq!(
        item.fragments().expect("two body prefixes").foreign().len(),
        2
    );
    assert!(matches!(
        item.payload,
        Payload::Boundary(ref pending)
            if matches!(
                pending.kind(),
                Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
            )
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
    assert_eq!(&*comment.text, "/* outer\n> > /* inner */ outer */");
    assert_eq!(input, "tail");
    assert_eq!(
        foreign,
        Some(vec![ForeignSplit::quote_prefix(
            "/* outer\n".len(),
            "> > ".len(),
        )])
    );
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
        ("a /*c*/]", "/*c*/"),
        (
            "a /* outer /* inner */ outer */]",
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
        assert_eq!(token.kind, TokenKind::RBracket);
        assert_eq!(&*token.text, "]");
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
