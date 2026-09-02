use chasa::{
    Back, ErrorSink, Input,
    error::std::{Expected, StdErr, StdSummary},
    input::IsCut,
    prelude::In,
};

use super::driver::{
    Gate3Envelope, commit_gate3_direct, parse_gate3_ast, probe_gate3_bridge_candidate,
    probe_gate3_bridge_candidate_direct,
};
use super::judge::{
    ActiveClose, ChunkContext, ChunkKind, DocumentMarker, DocumentMarkerKind, TerminatorKind,
    judge_block_close, judge_chunk, judge_document_marker, judge_line_document_extent,
};
use crate::{
    SyntaxKind, SyntaxNode,
    grammar::expression::probe_rejected_fixed_tail_recovery_episode_for_test,
    input::SourceInput,
    operator::{BindingPower, OperatorDeclaration, OperatorFixities, OperatorTable},
    session::{
        BracedStatementBlockRole, ConstructRole, DeclarationCompanionRole, DeclarationRole,
        Delimiter, DerivesRole, ExpectedSyntax, ExpressionRole, FullCstOutput, GrammarRole,
        IfExpressionRole, LineState, ParseLocal,
        ParseLocalValueSnapshot, Probe, PunctuationEvidence, RecoveryKind, RecoverySiteSpec,
        YumarkEnvelopeStop, YumarkEmbeddedOuterKind, YumarkEmbeddedRecoveryFact, YumarkFrame,
        YumarkInlineClose, YumarkOwner, YumarkSlot, YumarkSyntaxEvidence,
    },
};

#[test]
fn yumark_gate2_isolated_judges_and_transactions() {
    fn marker(source: &str, at_line_start: bool) -> (Option<DocumentMarker>, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i =
            In::new(&mut source_input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let marker = judge_document_marker(&mut i, at_line_start);
        assert_eq!(i.local.value_snapshot(), before, "marker state: {source:?}");
        let remainder = i.input.remainder();
        drop(i);
        assert!(sink.take_merged().is_none(), "marker sink: {source:?}");
        assert!(!cut, "marker cut: {source:?}");
        (marker, remainder)
    }

    for (source, at_line_start, expected, remainder) in [
        (
            "---\nnext",
            true,
            Some(DocumentMarker {
                kind: DocumentMarkerKind::BlockOpen,
                range: 0..3,
            }),
            "\nnext",
        ),
        (
            "--- \t\r\nnext",
            true,
            Some(DocumentMarker {
                kind: DocumentMarkerKind::BlockOpen,
                range: 0..3,
            }),
            " \t\r\nnext",
        ),
        (
            "--text",
            false,
            Some(DocumentMarker {
                kind: DocumentMarkerKind::Line,
                range: 0..2,
            }),
            "text",
        ),
        ("---", true, None, "---"),
        ("---x", true, None, "---x"),
        ("----", true, None, "----"),
        ("--- ", true, None, "--- "),
        ("---\r", true, None, "---\r"),
        ("---\n", false, None, "---\n"),
    ] {
        assert_eq!(marker(source, at_line_start), (expected, remainder));
    }

    for (source, expected_body, expected_end, expected_remainder) in [
        ("--", 2..2, 2..2, ""),
        ("--body\nnext", 2..6, 6..6, "\nnext"),
        ("--a\rb\r\nnext", 2..5, 5..5, "\r\nnext"),
    ] {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i =
            In::new(&mut source_input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let prefix = judge_document_marker(&mut i, true)
            .expect("line marker")
            .range;
        let before = i.local.value_snapshot();
        let extent = judge_line_document_extent(&mut i, prefix.clone());
        assert_eq!(
            i.local.value_snapshot(),
            before,
            "line extent state: {source:?}"
        );
        assert_eq!(extent.prefix, prefix);
        assert_eq!(extent.body, expected_body, "line body: {source:?}");
        assert_eq!(extent.end, expected_end, "line end: {source:?}");
        assert_eq!(i.input.remainder(), expected_remainder);
        drop(i);
        assert!(sink.take_merged().is_none());
        assert!(!cut);
    }

    fn block_close(
        source: &str,
        after_opening_line: bool,
        at_line_start: bool,
        indent_col: usize,
        base_col: usize,
    ) -> (Option<std::ops::Range<usize>>, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_yumark_frame(YumarkFrame::Document {
            base: base_col,
            envelope_stop: YumarkEnvelopeStop::BlockDocument,
        });
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i =
            In::new(&mut source_input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let close = judge_block_close(
            &mut i,
            after_opening_line,
            at_line_start,
            indent_col,
            base_col,
        );
        assert_eq!(i.local.value_snapshot(), before, "close state: {source:?}");
        let remainder = i.input.remainder();
        drop(i);
        assert!(sink.take_merged().is_none(), "close sink: {source:?}");
        assert!(!cut, "close cut: {source:?}");
        (close, remainder)
    }

    for (source, after_open, line_start, indent, base, expected, remainder) in [
        ("---\nnext", true, true, 2, 2, Some(0..3), "\nnext"),
        ("--- \t", true, true, 2, 2, Some(0..3), " \t"),
        ("---", false, true, 2, 2, None, "---"),
        ("---", true, false, 2, 2, None, "---"),
        ("---", true, true, 3, 2, None, "---"),
        ("---x", true, true, 2, 2, None, "---x"),
        ("----", true, true, 2, 2, None, "----"),
        ("--- x", true, true, 2, 2, None, "--- x"),
        ("---\r", true, true, 2, 2, None, "---\r"),
    ] {
        assert_eq!(
            block_close(source, after_open, line_start, indent, base),
            (expected, remainder)
        );
    }

    fn context(at_line_start: bool) -> ChunkContext {
        ChunkContext {
            at_line_start,
            indent_col: 0,
            base_col: 0,
            active_close: None,
        }
    }

    fn chunk(source: &str, context: ChunkContext) -> (ChunkKind, std::ops::Range<usize>, &str) {
        let mut source_input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.push_yumark_frame(YumarkFrame::Inline {
            owner: YumarkOwner::InlineGroup,
            close: YumarkInlineClose::RightBracket,
        });
        let before = local.value_snapshot();
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i =
            In::new(&mut source_input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let chunk = judge_chunk(&mut i, context);
        assert_eq!(i.local.value_snapshot(), before, "chunk state: {source:?}");
        let remainder = i.input.remainder();
        drop(i);
        assert!(sink.take_merged().is_none(), "chunk sink: {source:?}");
        assert!(!cut, "chunk cut: {source:?}");
        (chunk.kind, chunk.range, remainder)
    }

    for (source, facts, kind, range, remainder) in [
        ("", context(true), ChunkKind::Eof, 0..0, ""),
        (" \t\r\nx", context(true), ChunkKind::BlankLine, 0..4, "x"),
        ("\r\nx", context(false), ChunkKind::Newline, 0..2, "x"),
        (
            "###.tail",
            context(true),
            ChunkKind::SectionClose { level: 3 },
            0..4,
            "tail",
        ),
        (
            "## title",
            context(true),
            ChunkKind::Heading { level: 2 },
            0..2,
            " title",
        ),
        ("##\ttitle", context(true), ChunkKind::RawText, 0..8, ""),
        (
            "12. item",
            context(true),
            ChunkKind::OrderedList,
            0..4,
            "item",
        ),
        (
            "- item",
            context(true),
            ChunkKind::UnorderedList,
            0..2,
            "item",
        ),
        ("1.item", context(true), ChunkKind::RawText, 0..6, ""),
        ("-item", context(true), ChunkKind::RawText, 0..5, ""),
        (
            "``` \nbody",
            context(true),
            ChunkKind::RawFence,
            0..3,
            " \nbody",
        ),
        (
            "```raw\nbody",
            context(true),
            ChunkKind::RawFence,
            0..3,
            "raw\nbody",
        ),
        (
            "```yulang\r\nbody",
            context(true),
            ChunkKind::RawFence,
            0..3,
            "yulang\r\nbody",
        ),
        ("```", context(true), ChunkKind::RawText, 0..3, ""),
        ("```raw", context(true), ChunkKind::RawText, 0..6, ""),
        ("```raw\r", context(true), ChunkKind::RawText, 0..7, ""),
        (
            ">>> \nbody",
            context(true),
            ChunkKind::ExplicitQuote { depth: 3 },
            0..3,
            " \nbody",
        ),
        (
            ">>> text",
            context(true),
            ChunkKind::PrefixQuote { depth: 3 },
            0..4,
            "text",
        ),
        (
            ">>> \nbody",
            ChunkContext {
                indent_col: 1,
                base_col: 0,
                ..context(true)
            },
            ChunkKind::PrefixQuote { depth: 3 },
            0..4,
            "\nbody",
        ),
        (
            "> > text",
            context(true),
            ChunkKind::PrefixQuote { depth: 2 },
            0..4,
            "text",
        ),
        ("![doc]", context(false), ChunkKind::Image, 0..2, "doc]"),
        (
            "[doc]",
            context(false),
            ChunkKind::InlineGroup,
            0..1,
            "doc]",
        ),
        ("**bold", context(false), ChunkKind::Strong, 0..2, "bold"),
        ("*em", context(false), ChunkKind::Emphasis, 0..1, "em"),
        ("\\name", context(false), ChunkKind::Backslash, 0..1, "name"),
        (
            "\\℘name",
            context(false),
            ChunkKind::Backslash,
            0..1,
            "℘name",
        ),
        ("\\", context(false), ChunkKind::RawText, 0..1, ""),
        ("_", context(false), ChunkKind::RawText, 0..1, ""),
        ("abc_[x", context(false), ChunkKind::RawText, 0..4, "[x"),
        (
            "]tail",
            ChunkContext {
                active_close: Some(ActiveClose::Inline(YumarkInlineClose::RightBracket)),
                ..context(false)
            },
            ChunkKind::Terminator(TerminatorKind::Inline(YumarkInlineClose::RightBracket)),
            0..1,
            "tail",
        ),
        (
            "*tail",
            ChunkContext {
                active_close: Some(ActiveClose::Inline(YumarkInlineClose::Emphasis)),
                ..context(false)
            },
            ChunkKind::Terminator(TerminatorKind::Inline(YumarkInlineClose::Emphasis)),
            0..1,
            "tail",
        ),
        (
            "**tail",
            ChunkContext {
                active_close: Some(ActiveClose::Inline(YumarkInlineClose::Strong)),
                ..context(false)
            },
            ChunkKind::Terminator(TerminatorKind::Inline(YumarkInlineClose::Strong)),
            0..2,
            "tail",
        ),
        ("]tail", context(false), ChunkKind::RawText, 0..5, ""),
        (
            "}tail",
            ChunkContext {
                active_close: Some(ActiveClose::BracedBody),
                ..context(false)
            },
            ChunkKind::Terminator(TerminatorKind::BracedBody),
            0..1,
            "tail",
        ),
        ("}tail", context(false), ChunkKind::RawText, 0..5, ""),
        (
            "--- \nnext",
            ChunkContext {
                active_close: Some(ActiveClose::BlockDocument {
                    after_opening_line: true,
                }),
                ..context(true)
            },
            ChunkKind::Terminator(TerminatorKind::BlockDocument),
            0..3,
            " \nnext",
        ),
        (
            "```\nnext",
            ChunkContext {
                active_close: Some(ActiveClose::RawFence),
                ..context(true)
            },
            ChunkKind::Terminator(TerminatorKind::RawFence),
            0..3,
            "\nnext",
        ),
        (
            ">>>\nnext",
            ChunkContext {
                active_close: Some(ActiveClose::ExplicitQuote { depth: 3 }),
                ..context(true)
            },
            ChunkKind::Terminator(TerminatorKind::ExplicitQuote),
            0..3,
            "\nnext",
        ),
        (
            ">>>>\nnext",
            ChunkContext {
                active_close: Some(ActiveClose::ExplicitQuote { depth: 3 }),
                ..context(true)
            },
            ChunkKind::ExplicitQuote { depth: 4 },
            0..4,
            "\nnext",
        ),
        (
            "---x",
            ChunkContext {
                active_close: Some(ActiveClose::BlockDocument {
                    after_opening_line: true,
                }),
                ..context(true)
            },
            ChunkKind::RawText,
            0..4,
            "",
        ),
    ] {
        assert_eq!(chunk(source, facts), (kind, range, remainder), "{source:?}");
    }

    let mut source = SourceInput::new("abc");
    let mut local = ParseLocal::new();
    local.push_yumark_frame(YumarkFrame::Document {
        base: 0,
        envelope_stop: YumarkEnvelopeStop::BlockDocument,
    });
    let outer_snapshot = local.value_snapshot();
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let mut i = In::new(&mut source, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outer = i.checkpoint();
    i.input.next();
    i.local
        .push_yumark_frame(YumarkFrame::ImplicitSection { level: 1 });
    let nested_snapshot = i.local.value_snapshot();
    let nested_pos = i.pos();
    let nested = i.checkpoint();
    let nested_clone = nested.clone();
    i.input.next();
    i.local
        .replace_yumark_frame(YumarkFrame::List { indent: 2 });
    i.local.push_yumark_frame(YumarkFrame::BracedBody {
        owner: YumarkOwner::Command,
    });
    i.rollback(nested_clone);
    assert_eq!(i.pos(), nested_pos);
    assert_eq!(i.local.value_snapshot(), nested_snapshot);
    i.input.next();
    i.local
        .push_yumark_frame(YumarkFrame::PrefixQuote { depth: 2 });
    i.rollback(nested);
    assert_eq!(i.pos(), nested_pos);
    assert_eq!(i.local.value_snapshot(), nested_snapshot);
    i.rollback(outer);
    assert_eq!(i.pos(), 0);
    assert_eq!(i.local.value_snapshot(), outer_snapshot);
    drop(i);
    assert!(sink.take_merged().is_none());
    assert!(!cut);
}

#[test]
fn yumark_gate3_structural_driver_ast_direct_and_bridge_table() {
    fn ast(
        source: &str,
    ) -> (
        std::ops::Range<usize>,
        String,
        usize,
        usize,
        ParseLocalValueSnapshot,
    ) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = parse_gate3_ast(
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            &mut i,
        );
        let range = outcome.document.range.clone();
        let remainder = i.input.remainder().to_owned();
        let depth = i.local.yumark_frame_depth();
        let recoveries = outcome.recoveries.len();
        let state = i.local.value_snapshot();
        drop(i);
        assert!(sink.take_merged().is_none(), "AST sink: {source:?}");
        let _accepted_cut = cut;
        (range, remainder, depth, recoveries, state)
    }

    fn direct(
        source: &str,
    ) -> (
        std::ops::Range<usize>,
        String,
        usize,
        usize,
        ParseLocalValueSnapshot,
    ) {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        let recovery_count = outcome.output.committed_recoveries().len();
        let prefix = outcome.output.finish_prefix().to_string();
        assert_eq!(prefix, &source[..outcome.range.end]);
        assert_eq!(outcome.line, local.line());
        assert_eq!(outcome.frame_depth, 0);
        assert!(sink.take_merged().is_none(), "direct sink: {source:?}");
        let _accepted_cut = cut;
        let state = local.value_snapshot();
        (
            outcome.range,
            outcome.remainder.to_owned(),
            outcome.frame_depth,
            recovery_count,
            state,
        )
    }

    for source in [
        "text [nested *em*] **strong** ![image](raw) [apply]:f(1, (2)) \\ref;\n",
        "# heading\nparagraph\n## child\nchild text\n#.\n",
        "- first\n- second\n  - child\n    continuation\nmid\n",
        "- # text",
        "- - text",
        "- \nplain",
        "> quoted\n> continued\nplain\n",
        "> one\n>> two\n> three\nplain",
        "> quoted\n\nplain",
        "> - item\nplain",
        ">>>\ninside\n>>>\n",
        "```yulang\r\n\\cmd([{}])\r\n```\r\nafter",
        "```\r\nx\r\n```",
        "  ```raw\nbody\n```\n  ```\nafter",
        "a\r\n  b",
        "a\n  b",
        "a\rb",
        "\\ref(1, (2)) tail",
        "\\ref(1)\r\nx",
        "\\ref(\n  1,\n  2) tail",
        "\\ref(1\n# next",
        "\\ref(\n# next",
        "[group \\ref(1] tail",
        "\\ref(1 ] 2) tail",
        "\\ref(f(,a))",
        "\\ref(f(,a)) \\ref(@ a)",
        "\\ref(,\n# next",
        "\\ref(x[,a])",
        "[d]:f(x.)",
        "\\ref(if : x)",
        "\\ref({@ value})",
        "\\ref(x[,a]) [d]:f(x.) \\ref(if : x) \\ref({@ value})",
        "\\ref(,a)",
        "\\ref(@ a)",
        "\\ref(1{})",
        "\\ref(1 @\n  2)",
        "\\ref(1 @\r\n  2)",
        "\\ref(1 @\n# next",
        "\\ref(1 @\r\n# next",
        "- \\ref(1\n- next",
        "- item \\ref(1\nplain",
        "> \\ref(1\nplain",
        ">>>\r\n\\ref(1\r\n>>>\r\n",
        "\\ref(1\n---\n",
        "\\ref(1\n```\nraw\n```\n",
        "\\ref(1",
        "[doc]:apply(1, 2)",
        "![doc] tail",
        "\\name?; \\name!!",
        "> outer\n>> ```yulang\n>> \\ref(1) [doc]:apply(2)\n>> ```\n> after\n",
        ">>>\n```yulang\n\\ref(1) [doc]:apply(2)\n```\n>>>\n",
        "> outer\n>> ```yulang\n>> \\ref(1) [doc]:apply(2)\n>> ```\n> \\ref(3) [d]:apply(4)\nplain\n",
        ">>>\n```yulang\n\\ref(1) [doc]:apply(2)\n```\n\\ref(3) [d]:apply(4)\n>>>\r\n",
        "> ```\n> raw\nplain\n",
        "> # section\n> body\nplain\n",
        "> - item\n>   continued\nplain\n",
        "> # section\n>> nested\n> body\nplain\n",
        ">>>\n# section\nbody\n>>>\nafter\n",
        "> ```\nplain\n",
        "> ```\n>> ```\n",
        ">> ```\n> ```\n",
        "> ```\n>>>\n",
        "> outer\n>>>\nafter\n",
        ">>>\n>>> content\n>>>\n",
        ">>>>\n>>>\ninside\n>>>\t\r\n>>>> \n",
        "```\nraw\n``` \nnext",
        "```\r\nraw\r\n```\t\r\nnext",
    ] {
        let ast = ast(source);
        let direct = direct(source);
        assert_eq!(ast.0, direct.0, "range: {source:?}");
        assert_eq!(ast.1, direct.1, "remainder: {source:?}");
        assert_eq!(ast.2, direct.2, "frame depth: {source:?}");
        assert_eq!(ast.3, direct.3, "recovery count: {source:?}");
        let mut expected_direct_state = ast.4;
        expected_direct_state.next_diagnostic_id += direct.3 as u32;
        assert_eq!(
            expected_direct_state, direct.4,
            "full local state: {source:?}"
        );
    }

    let source = "\\ref(1\n# next";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert!(outcome.output.committed_recoveries().iter().any(|record| {
        record.kind == RecoveryKind::Missing
            && record.site.role
                == GrammarRole::Yumark(crate::session::YumarkRole {
                    owner: YumarkOwner::InlineReference,
                    slot: YumarkSlot::ClosingDelimiter,
                })
            && record.site.range == (6..6)
            && record.expectations[record.primary_expectation].expected
                == ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis))
    }));
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    let args = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmYulangArgs)
        .expect("Yumark args wrapper");
    assert_eq!(
        args.parent().map(|node| node.kind()),
        Some(SyntaxKind::YmInlineRef)
    );
    assert!(
        args.children()
            .any(|node| node.kind() == SyntaxKind::OperatorChain)
    );
    assert_eq!(
        args.children().map(|node| node.kind()).collect::<Vec<_>>(),
        vec![SyntaxKind::OperatorChain, SyntaxKind::Missing],
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::CallTail)
    );

    let source = "\\ref(@ a)";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert!(
        outcome
            .output
            .committed_recoveries()
            .iter()
            .any(|record| { matches!(record.site.role, GrammarRole::Expression(_)) })
    );
    assert!(
        !outcome
            .output
            .committed_recoveries()
            .iter()
            .any(|record| { matches!(record.site.role, GrammarRole::Yumark(_)) })
    );
    assert_eq!(outcome.output.finish_prefix().to_string(), source);

    let source = "\\ref(\n# next";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert!(outcome.output.committed_recoveries().iter().any(|record| {
        record.kind == RecoveryKind::Missing
            && matches!(record.site.role, GrammarRole::Yumark(_))
            && record.site.range == (5..5)
    }));

    let source = "[group \\ref(1] tail";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.output.committed_recoveries().len(), 1);
    let recovery = &outcome.output.committed_recoveries()[0];
    assert_eq!(recovery.kind, RecoveryKind::Missing);
    assert_eq!(
        recovery.site.role,
        GrammarRole::Yumark(crate::session::YumarkRole {
            owner: YumarkOwner::InlineReference,
            slot: YumarkSlot::ClosingDelimiter,
        })
    );
    assert_eq!(recovery.site.range, 13..13);
    assert_eq!(outcome.output.finish_prefix().to_string(), source);

    let source = "\\ref(1 ] 2) tail";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = parse_gate3_ast(
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        &mut i,
    );
    assert_eq!(
        outcome
            .recoveries
            .iter()
            .map(|record| {
                (
                    record.role,
                    record.range.clone(),
                    record.kind,
                    record.expected,
                    record.order,
                )
            })
            .collect::<Vec<_>>(),
        vec![
            (
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ArgumentList,
                    delimiter: Delimiter::Parenthesis,
                },
                7..8,
                RecoveryKind::Error,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis)),
                0,
            ),
            (
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ArgumentList,
                    delimiter: Delimiter::Parenthesis,
                },
                8..10,
                RecoveryKind::Error,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis)),
                1,
            ),
        ]
    );
    drop(i);
    assert!(sink.take_merged().is_none());

    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    let recoveries = outcome.output.committed_recoveries().to_vec();
    assert_eq!(recoveries.len(), 2);
    assert_eq!(
        recoveries
            .iter()
            .map(|record| (record.site.role, record.site.range.clone(), record.kind))
            .collect::<Vec<_>>(),
        vec![
            (
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ArgumentList,
                    delimiter: Delimiter::Parenthesis,
                },
                7..8,
                RecoveryKind::Error,
            ),
            (
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ArgumentList,
                    delimiter: Delimiter::Parenthesis,
                },
                8..10,
                RecoveryKind::Error,
            ),
        ]
    );
    assert!(recoveries.iter().all(|record| {
        record.expectations[record.primary_expectation].expected
            == ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis))
    }));
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    assert_eq!(root.to_string(), source);
    let args = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmYulangArgs)
        .expect("Yumark argument adapter");
    assert_eq!(
        args.children().map(|node| node.kind()).collect::<Vec<_>>(),
        vec![
            SyntaxKind::OperatorChain,
            SyntaxKind::Error,
            SyntaxKind::Error,
        ]
    );
    let close = args
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RParen)
        .expect("Yumark-owned outer close");
    assert_eq!(
        usize::from(close.text_range().start())..usize::from(close.text_range().end()),
        10..11
    );
    assert!(root.descendants().any(|node| {
        node.kind() == SyntaxKind::YmText
            && (usize::from(node.text_range().start())..usize::from(node.text_range().end()))
                == (11..16)
    }));

    for (source, role, range, kind, expected) in [
        (
            "\\ref(,a)",
            GrammarRole::Expression(ExpressionRole::CallArgument),
            5..5,
            RecoveryKind::Missing,
            ExpectedSyntax::Expression,
        ),
        (
            "\\ref(@ a)",
            GrammarRole::Expression(ExpressionRole::CallArgument),
            5..7,
            RecoveryKind::Error,
            ExpectedSyntax::Expression,
        ),
        (
            "\\ref(1{})",
            GrammarRole::Expression(ExpressionRole::CallArgumentSeparator),
            6..6,
            RecoveryKind::Missing,
            ExpectedSyntax::DelimitedSequenceSeparator,
        ),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let ast = parse_gate3_ast(
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            &mut i,
        );
        assert_eq!(ast.recoveries.len(), 1, "AST recovery: {source:?}");
        assert_eq!(
            (
                ast.recoveries[0].role,
                ast.recoveries[0].range.clone(),
                ast.recoveries[0].kind,
                ast.recoveries[0].expected,
                ast.recoveries[0].order,
            ),
            (role, range.clone(), kind, expected, 0),
            "AST fact: {source:?}",
        );
        drop(i);
        assert!(sink.take_merged().is_none(), "AST sink: {source:?}");

        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let direct = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(direct.output.committed_recoveries().len(), 1, "{source:?}");
        let recovery = &direct.output.committed_recoveries()[0];
        assert_eq!(
            (
                recovery.site.role,
                recovery.site.range.clone(),
                recovery.kind,
                recovery.expectations[recovery.primary_expectation].expected,
            ),
            (role, range, kind, expected),
            "direct fact: {source:?}",
        );
        let root = SyntaxNode::new_root(direct.output.finish_prefix());
        assert_eq!(root.to_string(), source);
        let close = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::YmYulangArgs)
            .and_then(|args| {
                args.children_with_tokens()
                    .filter_map(|element| element.into_token())
                    .find(|token| token.kind() == SyntaxKind::RParen)
            })
            .expect("Yumark-owned argument close");
        assert_eq!(
            usize::from(close.text_range().start())..usize::from(close.text_range().end()),
            source.len() - 1..source.len(),
            "Yumark close: {source:?}",
        );
        assert!(sink.take_merged().is_none(), "direct sink: {source:?}");
    }

    for (source, error_range, close_range, remainder, line) in [
        (
            "\\ref(1 @\n  2)",
            7..12,
            None,
            "",
            LineState {
                last_newline: Some((8, 9)),
                line_start: 9,
                line_indent: 2,
                at_line_start: false,
            },
        ),
        (
            "\\ref(1 @\r\n  2)",
            7..13,
            None,
            "",
            LineState {
                last_newline: Some((8, 10)),
                line_start: 10,
                line_indent: 2,
                at_line_start: false,
            },
        ),
        (
            "\\ref(1 @\n# next",
            7..8,
            Some(8..8),
            "",
            LineState {
                last_newline: Some((8, 9)),
                line_start: 9,
                line_indent: 0,
                at_line_start: false,
            },
        ),
        (
            "\\ref(1 @\r\n# next",
            7..8,
            Some(8..8),
            "",
            LineState {
                last_newline: Some((8, 10)),
                line_start: 10,
                line_indent: 0,
                at_line_start: false,
            },
        ),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        let facts = outcome.output.committed_recoveries();
        assert_eq!(
            facts[0].site.role,
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::ArgumentList,
                delimiter: Delimiter::Parenthesis,
            }
        );
        assert_eq!(facts[0].site.range, error_range, "{source:?}");
        assert_eq!(facts[0].kind, RecoveryKind::Error, "{source:?}");
        if let Some(close_range) = close_range {
            assert_eq!(facts.len(), 2, "{source:?}");
            assert_eq!(facts[1].site.range, close_range, "{source:?}");
            assert!(matches!(facts[1].site.role, GrammarRole::Yumark(_)));
        } else {
            assert_eq!(facts.len(), 1, "{source:?}");
        }
        assert_eq!(outcome.remainder, remainder, "{source:?}");
        assert_eq!(outcome.line, line, "{source:?}");
        assert_eq!(
            format!("{}{}", outcome.output.finish_prefix(), outcome.remainder),
            source,
            "{source:?}",
        );
    }

    for (source, missing_at, remainder) in [
        ("- \\ref(1\n- next", 8, ""),
        ("- item \\ref(1\nplain", 13, ""),
        ("> \\ref(1\nplain", 8, ""),
        (">>>\r\n\\ref(1\r\n>>>\r\n", 11, ""),
        ("\\ref(1\n---\n", 6, "---\n"),
        ("\\ref(1\n```\nraw\n```\n", 6, ""),
        ("\\ref(1", 6, ""),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        let yumark = outcome
            .output
            .committed_recoveries()
            .iter()
            .filter(|record| matches!(record.site.role, GrammarRole::Yumark(_)))
            .collect::<Vec<_>>();
        assert_eq!(yumark.len(), 1, "{source:?}");
        assert_eq!(yumark[0].kind, RecoveryKind::Missing, "{source:?}");
        assert_eq!(
            yumark[0].site.role,
            GrammarRole::Yumark(crate::session::YumarkRole {
                owner: YumarkOwner::InlineReference,
                slot: YumarkSlot::ClosingDelimiter,
            }),
            "{source:?}",
        );
        assert_eq!(yumark[0].site.range, missing_at..missing_at, "{source:?}");
        assert_eq!(
            yumark[0].expectations[yumark[0].primary_expectation].expected,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis)),
            "{source:?}",
        );
        assert_eq!(outcome.remainder, remainder, "{source:?}");
        assert_eq!(
            format!("{}{}", outcome.output.finish_prefix(), outcome.remainder),
            source,
            "{source:?}",
        );
    }

    for (source, raw_body, list_count, item_count) in
        [("- # text", "# text", 1, 1), ("- - text", "- text", 1, 1)]
    {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(
            outcome.range,
            0..source.len(),
            "same-line list range: {source:?}"
        );
        assert_eq!(
            outcome.remainder, "",
            "same-line list remainder: {source:?}"
        );
        assert_eq!(outcome.frame_depth, 0, "same-line list frames: {source:?}");
        assert_eq!(
            outcome.work.frame_pushes, outcome.work.frame_pops,
            "{source:?}"
        );
        assert!(
            outcome.output.committed_recoveries().is_empty(),
            "{source:?}"
        );
        assert_eq!(
            outcome.line,
            LineState {
                last_newline: None,
                line_start: 0,
                line_indent: 0,
                at_line_start: false,
            },
            "same-line list state: {source:?}",
        );
        assert!(
            sink.take_merged().is_none(),
            "same-line list sink: {source:?}"
        );
        let root = SyntaxNode::new_root(outcome.output.finish_prefix());
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::YmList)
                .count(),
            list_count,
            "same-line nested list: {source:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::YmListItem)
                .count(),
            item_count,
            "same-line item: {source:?}",
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::YmSection)
        );
        let text = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::YmText && node.to_string() == raw_body)
            .expect("same-line marker text");
        assert!(
            text.ancestors()
                .any(|node| node.kind() == SyntaxKind::YmListItemBody)
        );
    }

    let source = "- item \\ref(1\nplain";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.range, 0..source.len());
    assert_eq!(outcome.remainder, "");
    assert_eq!(outcome.frame_depth, 0);
    assert_eq!(outcome.work.frame_pushes, outcome.work.frame_pops);
    assert_eq!(
        outcome.line,
        LineState {
            last_newline: Some((13, 14)),
            line_start: 14,
            line_indent: 0,
            at_line_start: false,
        }
    );
    let recoveries = outcome.output.committed_recoveries();
    assert_eq!(recoveries.len(), 1);
    assert_eq!(recoveries[0].site.range, 13..13);
    assert_eq!(
        recoveries[0].site.role,
        GrammarRole::Yumark(crate::session::YumarkRole {
            owner: YumarkOwner::InlineReference,
            slot: YumarkSlot::ClosingDelimiter,
        })
    );
    assert!(sink.take_merged().is_none());
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    let reference = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmInlineRef)
        .expect("list-owned reference");
    assert!(
        reference
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::YmListItemBody)
    );
    let plain = root
        .descendants()
        .find(|node| {
            node.kind() == SyntaxKind::YmText
                && (usize::from(node.text_range().start())..usize::from(node.text_range().end()))
                    == (14..19)
        })
        .expect("dedented parent text");
    assert!(
        !plain
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::YmListItem)
    );

    let source = "- \nplain";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.range, 0..source.len());
    assert_eq!(outcome.remainder, "");
    assert_eq!(outcome.frame_depth, 0);
    assert_eq!(outcome.work.frame_pushes, outcome.work.frame_pops);
    assert!(outcome.output.committed_recoveries().is_empty());
    assert_eq!(
        outcome.line,
        LineState {
            last_newline: Some((2, 3)),
            line_start: 3,
            line_indent: 0,
            at_line_start: false,
        }
    );
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    assert_eq!(root.to_string(), source);
    let plain = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmText && node.to_string() == "plain")
        .expect("empty-item following text");
    assert!(
        !plain
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::YmListItem)
    );
    assert!(sink.take_merged().is_none());

    let source = "- first\n- second\n  - child\n    continuation\nmid\n";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.range, 0..source.len());
    assert_eq!(outcome.frame_depth, 0);
    assert_eq!(outcome.work.frame_pushes, outcome.work.frame_pops);
    assert!(outcome.output.committed_recoveries().is_empty());
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    assert_eq!(root.to_string(), source);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::YmList)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::YmListItem)
            .count(),
        3
    );
    let continuation = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmText && node.to_string().contains("continuation"))
        .expect("child continuation");
    assert!(
        continuation
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::YmListItem)
    );
    let middle = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmText && node.to_string() == "mid")
        .expect("middle-indent return");
    assert!(
        !middle
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::YmListItem)
    );
    assert!(sink.take_merged().is_none());

    let source = "> \\ref(1\nplain";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.range, 0..source.len());
    assert_eq!(outcome.remainder, "");
    assert_eq!(outcome.frame_depth, 0);
    assert_eq!(outcome.work.frame_pushes, outcome.work.frame_pops);
    assert_eq!(
        outcome.line,
        LineState {
            last_newline: Some((8, 9)),
            line_start: 9,
            line_indent: 0,
            at_line_start: false,
        }
    );
    let recoveries = outcome.output.committed_recoveries();
    assert_eq!(recoveries.len(), 1);
    assert_eq!(recoveries[0].site.range, 8..8);
    assert_eq!(
        recoveries[0].site.role,
        GrammarRole::Yumark(crate::session::YumarkRole {
            owner: YumarkOwner::InlineReference,
            slot: YumarkSlot::ClosingDelimiter,
        })
    );
    assert!(sink.take_merged().is_none());
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    let reference = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmInlineRef)
        .expect("quote-owned reference");
    assert!(
        reference
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::YmQuoteBlock)
    );
    let plain = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmText && node.to_string() == "plain")
        .expect("dequoted parent text");
    assert!(
        !plain
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::YmQuoteBlock)
    );

    for (source, quote_count, list_count) in [
        ("> one\n>> two\n> three\nplain", 2, 0),
        ("> quoted\n\nplain", 1, 0),
        ("> - item\nplain", 1, 1),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(outcome.range, 0..source.len(), "prefix range: {source:?}");
        assert_eq!(outcome.remainder, "", "prefix remainder: {source:?}");
        assert_eq!(outcome.frame_depth, 0, "prefix frames: {source:?}");
        assert_eq!(
            outcome.work.frame_pushes, outcome.work.frame_pops,
            "{source:?}"
        );
        assert!(
            outcome.output.committed_recoveries().is_empty(),
            "{source:?}"
        );
        let last_newline = source.rfind('\n').expect("prefix row newline");
        assert_eq!(
            outcome.line,
            LineState {
                last_newline: Some((last_newline, last_newline + 1)),
                line_start: last_newline + 1,
                line_indent: 0,
                at_line_start: false,
            },
            "prefix line: {source:?}",
        );
        assert!(sink.take_merged().is_none(), "prefix sink: {source:?}");
        let root = SyntaxNode::new_root(outcome.output.finish_prefix());
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::YmQuoteBlock)
                .count(),
            quote_count,
            "prefix nesting: {source:?}",
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::YmList)
                .count(),
            list_count,
            "quoted list: {source:?}",
        );
        let plain = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::YmText && node.to_string() == "plain")
            .expect("prefix parent text");
        assert!(
            !plain
                .ancestors()
                .any(|node| node.kind() == SyntaxKind::YmQuoteBlock)
        );
        if list_count == 1 {
            let item = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::YmText && node.to_string() == "item")
                .expect("quoted list item");
            assert!(
                item.ancestors()
                    .any(|node| node.kind() == SyntaxKind::YmQuoteBlock)
            );
        }
    }

    let source = ">>>\r\n\\ref(1\r\n>>> \t\r\n";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(
        outcome.line,
        LineState {
            last_newline: Some((18, 20)),
            line_start: 20,
            line_indent: 0,
            at_line_start: true,
        }
    );
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    let close = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| {
            token.kind() == SyntaxKind::YmQuoteFenceMarker
                && usize::from(token.text_range().start()) == 13
        })
        .expect("explicit quote close token");
    assert_eq!(
        close.parent().map(|node| node.kind()),
        Some(SyntaxKind::YmQuoteBlock)
    );
    let suffix_newline = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| {
            token.kind() == SyntaxKind::Newline && usize::from(token.text_range().start()) == 18
        })
        .expect("explicit quote close suffix newline");
    let suffix_document = suffix_newline.parent().expect("suffix document");
    assert_eq!(suffix_document.kind(), SyntaxKind::YmDoc);
    assert_eq!(
        suffix_document.parent().map(|node| node.kind()),
        Some(SyntaxKind::Root)
    );

    for (source, raw_line) in [
        (
            "> outer\n>> ```yulang\n>> \\ref(1) [doc]:apply(2)\n>> ```\n> \\ref(3) [d]:apply(4)\nplain\n",
            ">> \\ref(1) [doc]:apply(2)\n",
        ),
        (
            ">>>\n```yulang\n\\ref(1) [doc]:apply(2)\n```\n\\ref(3) [d]:apply(4)\n>>>\r\n",
            "\\ref(1) [doc]:apply(2)\n",
        ),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(
            outcome.range,
            0..source.len(),
            "quote/fence range: {source:?}"
        );
        assert_eq!(outcome.remainder, "", "quote/fence remainder: {source:?}");
        assert_eq!(outcome.frame_depth, 0, "quote/fence frames: {source:?}");
        assert_eq!(
            outcome.work.fence_bytes,
            raw_line.len(),
            "quote/fence work: {source:?}"
        );
        let last_newline = if source.ends_with("\r\n") {
            (source.len() - 2, source.len())
        } else {
            (source.len() - 1, source.len())
        };
        assert_eq!(
            outcome.line,
            LineState {
                last_newline: Some(last_newline),
                line_start: source.len(),
                line_indent: 0,
                at_line_start: true,
            },
            "quote/fence line: {source:?}",
        );
        assert!(sink.take_merged().is_none(), "quote/fence sink: {source:?}");
        let root = SyntaxNode::new_root(outcome.output.finish_prefix());
        assert_eq!(root.to_string(), source);
        let fence = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::YmCodeFence)
            .expect("nested raw fence");
        let info = fence
            .descendants()
            .find(|node| node.kind() == SyntaxKind::YmCodeFenceInfo)
            .expect("raw fence info");
        assert_eq!(info.to_string(), "yulang");
        let text = fence
            .children()
            .find(|node| node.kind() == SyntaxKind::YmCodeFenceText)
            .expect("one raw fence text node");
        assert_eq!(text.to_string(), raw_line);
        assert!(!fence.descendants().any(|node| {
            matches!(
                node.kind(),
                SyntaxKind::OperatorChain
                    | SyntaxKind::YmInlineRef
                    | SyntaxKind::YmInlineApply
                    | SyntaxKind::YmYulangArgs
                    | SyntaxKind::YmInlineApplyArgs
            )
        }));
        assert!(root.descendants().any(|node| {
            node.kind() == SyntaxKind::YmYulangArgs
                && usize::from(node.text_range().start()) > usize::from(fence.text_range().end())
                && node
                    .ancestors()
                    .any(|ancestor| ancestor.kind() == SyntaxKind::YmQuoteBlock)
        }));
        assert!(root.descendants().any(|node| {
            node.kind() == SyntaxKind::YmInlineApplyArgs
                && usize::from(node.text_range().start()) > usize::from(fence.text_range().end())
                && node
                    .ancestors()
                    .any(|ancestor| ancestor.kind() == SyntaxKind::YmQuoteBlock)
        }));
    }

    let source = "> ```\n> raw\nplain\n";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.range, 0..source.len());
    assert_eq!(outcome.remainder, "");
    assert_eq!(outcome.frame_depth, 0);
    assert_eq!(outcome.work.fence_bytes, "> raw\nplain\n".len());
    assert_eq!(
        outcome
            .output
            .committed_recoveries()
            .iter()
            .filter_map(|record| match record.site.role {
                GrammarRole::Yumark(role) => Some((
                    role.owner,
                    record.site.range.clone(),
                    record.kind,
                    record.expectations[record.primary_expectation].expected,
                )),
                _ => None,
            })
            .collect::<Vec<_>>(),
        vec![(
            YumarkOwner::CodeFence,
            source.len()..source.len(),
            RecoveryKind::Missing,
            ExpectedSyntax::Yumark(YumarkSyntaxEvidence::FenceMarker),
        )],
    );
    assert_eq!(outcome.output.finish_prefix().to_string(), source);

    for (source, raw) in [
        ("> ```\nplain\n", "plain\n"),
        ("> ```\n>> ```\n", ">> ```\n"),
        (">> ```\n> ```\n", "> ```\n"),
        ("> ```\n>>>\n", ">>>\n"),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(outcome.work.fence_bytes, raw.len(), "{source:?}");
        assert_eq!(
            outcome
                .output
                .committed_recoveries()
                .iter()
                .filter_map(|record| match record.site.role {
                    GrammarRole::Yumark(role) => Some((role.owner, record.site.range.clone())),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            vec![(YumarkOwner::CodeFence, source.len()..source.len())],
            "{source:?}",
        );
        let root = SyntaxNode::new_root(outcome.output.finish_prefix());
        let text = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::YmCodeFenceText)
            .expect("raw fence text");
        assert_eq!(text.to_string(), raw, "{source:?}");
        assert_eq!(outcome.line.line_start, source.len(), "{source:?}");
        assert!(sink.take_merged().is_none(), "{source:?}");
    }

    for (source, expected) in [
        (
            "\\ref(f(,a))",
            vec![(
                GrammarRole::Expression(ExpressionRole::CallArgument),
                7..7,
                RecoveryKind::Missing,
            )],
        ),
        (
            "\\ref(f(,a)) \\ref(@ a)",
            vec![
                (
                    GrammarRole::Expression(ExpressionRole::CallArgument),
                    7..7,
                    RecoveryKind::Missing,
                ),
                (
                    GrammarRole::Expression(ExpressionRole::CallArgument),
                    17..19,
                    RecoveryKind::Error,
                ),
            ],
        ),
        (
            "\\ref(,\n# next",
            vec![
                (
                    GrammarRole::Expression(ExpressionRole::CallArgument),
                    5..5,
                    RecoveryKind::Missing,
                ),
                (
                    GrammarRole::Yumark(crate::session::YumarkRole {
                        owner: YumarkOwner::InlineReference,
                        slot: YumarkSlot::ClosingDelimiter,
                    }),
                    6..6,
                    RecoveryKind::Missing,
                ),
            ],
        ),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let ast = parse_gate3_ast(
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            &mut i,
        );
        assert_eq!(
            ast.recoveries
                .iter()
                .map(|fact| (fact.role, fact.range.clone(), fact.kind))
                .collect::<Vec<_>>(),
            expected,
            "AST embedded recovery order: {source:?}",
        );
        assert_eq!(
            ast.recoveries
                .iter()
                .map(|fact| fact.order)
                .collect::<Vec<_>>(),
            (0..ast.recoveries.len()).collect::<Vec<_>>(),
            "AST global recovery order: {source:?}",
        );
        drop(i);
        assert!(sink.take_merged().is_none(), "AST sink: {source:?}");

        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let direct = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(
            direct
                .output
                .committed_recoveries()
                .iter()
                .map(|record| (record.site.role, record.site.range.clone(), record.kind))
                .collect::<Vec<_>>(),
            expected,
            "direct embedded recovery order: {source:?}",
        );
        let root = SyntaxNode::new_root(direct.output.finish_prefix());
        if source.starts_with("\\ref(f(") {
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::CallTail)
                    .count(),
                1,
                "only the nested canonical call owns CallTail: {source:?}",
            );
        }
        assert!(sink.take_merged().is_none(), "direct sink: {source:?}");
    }

    let mut local = ParseLocal::new();
    let floor = local.push_yumark_delimiter(Delimiter::Parenthesis);
    local.push_yumark_frame(YumarkFrame::EmbeddedYulang {
        owner: YumarkOwner::InlineReference,
        outer_kind: YumarkEmbeddedOuterKind::Paired(Delimiter::Parenthesis),
        delimiter_floor: floor,
    });
    let before = local.checkpoint();
    local.record_yumark_embedded_recovery(YumarkEmbeddedRecoveryFact {
        spec: RecoverySiteSpec {
            role: GrammarRole::Expression(ExpressionRole::CallArgument),
            expected: ExpectedSyntax::Expression,
        },
        range: 1..1,
        kind: RecoveryKind::Missing,
        unexpected: None,
    });
    let recorded = local.checkpoint();
    assert_eq!(local.drain_yumark_embedded_recoveries().len(), 1);
    local.rollback(recorded);
    assert_eq!(local.drain_yumark_embedded_recoveries().len(), 1);
    local.rollback(before);
    assert!(local.drain_yumark_embedded_recoveries().is_empty());
    assert!(matches!(
        local.pop_yumark_frame(),
        Some(YumarkFrame::EmbeddedYulang { .. })
    ));
    local.pop_yumark_delimiter(floor, Delimiter::Parenthesis);

    for source in [
        "> # section\n> body\nplain\n",
        "> - item\n>   continued\nplain\n",
        "> # section\n>> nested\n> body\nplain\n",
        ">>>\n# section\nbody\n>>>\nafter\n",
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(outcome.range, 0..source.len(), "{source:?}");
        assert_eq!(outcome.frame_depth, 0, "{source:?}");
        let root = SyntaxNode::new_root(outcome.output.finish_prefix());
        let quote = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::YmQuoteBlock)
            .expect("quote block");
        assert!(quote.descendants().any(|node| matches!(
            node.kind(),
            SyntaxKind::YmSection | SyntaxKind::YmList
        )));
        let trailing = source.rfind("plain").or_else(|| source.rfind("after"));
        if let Some(start) = trailing {
            assert!(root.descendants().any(|node| {
                node.kind() == SyntaxKind::YmText
                    && usize::from(node.text_range().start()) == start
                    && !node
                        .ancestors()
                        .any(|ancestor| ancestor.kind() == SyntaxKind::YmQuoteBlock)
            }));
        }
        assert!(sink.take_merged().is_none(), "{source:?}");
    }

    for (source, expected) in [
        (
            "\\ref(x[,a])",
            vec![(
                GrammarRole::Expression(ExpressionRole::IndexItem),
                7..7,
                RecoveryKind::Missing,
                ExpectedSyntax::Expression,
            )],
        ),
        (
            "[d]:f(x.)",
            vec![(
                GrammarRole::Expression(ExpressionRole::FieldName),
                8..8,
                RecoveryKind::Missing,
                ExpectedSyntax::Identifier,
            )],
        ),
        (
            "\\ref(if : x)",
            vec![(
                GrammarRole::IfExpression(IfExpressionRole::Condition),
                8..8,
                RecoveryKind::Missing,
                ExpectedSyntax::Expression,
            )],
        ),
        (
            "\\ref({@ value})",
            vec![(
                GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                6..8,
                RecoveryKind::Error,
                ExpectedSyntax::Statement,
            )],
        ),
        (
            "\\ref(x[,a]) [d]:f(x.) \\ref(if : x) \\ref({@ value})",
            vec![
                (
                    GrammarRole::Expression(ExpressionRole::IndexItem),
                    7..7,
                    RecoveryKind::Missing,
                    ExpectedSyntax::Expression,
                ),
                (
                    GrammarRole::Expression(ExpressionRole::FieldName),
                    20..20,
                    RecoveryKind::Missing,
                    ExpectedSyntax::Identifier,
                ),
                (
                    GrammarRole::IfExpression(IfExpressionRole::Condition),
                    30..30,
                    RecoveryKind::Missing,
                    ExpectedSyntax::Expression,
                ),
                (
                    GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                    41..43,
                    RecoveryKind::Error,
                    ExpectedSyntax::Statement,
                ),
            ],
        ),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let ast = parse_gate3_ast(
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            &mut i,
        );
        assert_eq!(
            ast.recoveries
                .iter()
                .map(|fact| {
                    (
                        fact.role,
                        fact.range.clone(),
                        fact.kind,
                        fact.expected,
                    )
                })
                .collect::<Vec<_>>(),
            expected,
            "AST transitive recovery: {source:?}",
        );
        assert_eq!(
            ast.recoveries
                .iter()
                .map(|fact| fact.order)
                .collect::<Vec<_>>(),
            (0..expected.len()).collect::<Vec<_>>(),
            "AST transitive order: {source:?}",
        );
        drop(i);
        assert!(sink.take_merged().is_none(), "AST sink: {source:?}");

        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let direct = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(
            direct
                .output
                .committed_recoveries()
                .iter()
                .map(|record| {
                    (
                        record.site.role,
                        record.site.range.clone(),
                        record.kind,
                        record.expectations[record.primary_expectation].expected,
                    )
                })
                .collect::<Vec<_>>(),
            expected,
            "direct transitive recovery: {source:?}",
        );
        assert_eq!(direct.output.finish_prefix().to_string(), source);
        assert!(sink.take_merged().is_none(), "direct sink: {source:?}");
    }

    for (source, role, range, kind, recovery_node, parent_kind) in [
        (
            "\\ref(x.)",
            GrammarRole::Expression(ExpressionRole::FieldName),
            7..7,
            RecoveryKind::Missing,
            SyntaxKind::Missing,
            SyntaxKind::FieldTail,
        ),
        (
            "\\ref(x::123)",
            GrammarRole::Expression(ExpressionRole::PathSegment),
            8..11,
            RecoveryKind::Error,
            SyntaxKind::Error,
            SyntaxKind::PathTail,
        ),
        (
            "\\ref(x:: 123)",
            GrammarRole::Expression(ExpressionRole::PathSegment),
            9..12,
            RecoveryKind::Error,
            SyntaxKind::Error,
            SyntaxKind::PathTail,
        ),
    ] {
        let mut ast_input = SourceInput::new(source);
        let mut ast_local = ParseLocal::new();
        ast_local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut ast_sink = chasa::LatestSink::new();
        let mut ast_cut = false;
        let mut i = In::new(
            &mut ast_input,
            &mut ast_sink,
            IsCut::new(&mut ast_cut),
        )
        .set_local(&mut ast_local);
        let ast = parse_gate3_ast(
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            &mut i,
        );
        assert_eq!(
            ast.recoveries
                .iter()
                .map(|fact| {
                    (
                        fact.role,
                        fact.range.clone(),
                        fact.kind,
                        fact.expected,
                        fact.order,
                    )
                })
                .collect::<Vec<_>>(),
            vec![(role, range.clone(), kind, ExpectedSyntax::Identifier, 0)],
            "E2 AST fact: {source:?}",
        );
        assert_eq!(i.input.remainder(), "", "E2 AST remainder: {source:?}");
        assert_eq!(i.local.yumark_frame_depth(), 0, "E2 AST frames: {source:?}");
        let ast_snapshot = i.local.value_snapshot();
        drop(i);
        assert!(ast_sink.take_merged().is_none(), "E2 AST sink: {source:?}");

        let mut direct_input = SourceInput::new(source);
        let mut direct_local = ParseLocal::new();
        direct_local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut direct_sink = chasa::LatestSink::new();
        let mut direct_cut = false;
        let i = In::new(
            &mut direct_input,
            &mut direct_sink,
            IsCut::new(&mut direct_cut),
        )
        .set_local(&mut direct_local);
        let direct = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(direct.range, 0..source.len(), "E2 direct range: {source:?}");
        assert_eq!(direct.remainder, "", "E2 direct remainder: {source:?}");
        assert_eq!(direct.frame_depth, 0, "E2 direct frames: {source:?}");
        let [record] = direct.output.committed_recoveries() else {
            panic!("one E2 direct recovery: {source:?}");
        };
        assert_eq!(
            (
                record.site.role,
                record.site.range.clone(),
                record.kind,
                record.expectations[record.primary_expectation].expected,
            ),
            (role, range.clone(), kind, ExpectedSyntax::Identifier),
            "E2 direct fact: {source:?}",
        );
        let mut expected_direct_snapshot = ast_snapshot;
        expected_direct_snapshot.next_diagnostic_id += 1;
        assert_eq!(
            direct_local.value_snapshot(),
            expected_direct_snapshot,
            "E2 AST/direct ParseLocal parity: {source:?}",
        );
        assert!(direct_sink.take_merged().is_none(), "E2 direct sink: {source:?}");
        let root = SyntaxNode::new_root(direct.output.finish_prefix());
        assert_eq!(root.to_string(), source, "E2 lossless prefix: {source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
                .map(|node| {
                    (
                        node.kind(),
                        usize::from(node.text_range().start())
                            ..usize::from(node.text_range().end()),
                        node.parent().map(|parent| parent.kind()),
                    )
                })
                .collect::<Vec<_>>(),
            vec![(recovery_node, range, Some(parent_kind))],
            "E2 direct recovery topology: {source:?}",
        );
        if source == "\\ref(x:: 123)" {
            let path = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::PathTail)
                .expect("spaced embedded E2 PathTail");
            assert_eq!(
                usize::from(path.text_range().start())..usize::from(path.text_range().end()),
                6..12,
            );
            assert_eq!(
                path.children_with_tokens()
                    .map(|element| {
                        (
                            element.kind(),
                            usize::from(element.text_range().start())
                                ..usize::from(element.text_range().end()),
                        )
                    })
                    .collect::<Vec<_>>(),
                vec![
                    (SyntaxKind::ColonColon, 6..8),
                    (SyntaxKind::Whitespace, 8..9),
                    (SyntaxKind::Error, 9..12),
                ],
                "post-separator trivia remains an immediate PathTail child",
            );
        }
    }

    let source = "@";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    let floor = local.push_yumark_delimiter(Delimiter::Parenthesis);
    local.push_yumark_frame(YumarkFrame::EmbeddedYulang {
        owner: YumarkOwner::InlineReference,
        outer_kind: YumarkEmbeddedOuterKind::Paired(Delimiter::Parenthesis),
        delimiter_floor: floor,
    });
    let retained_fact = YumarkEmbeddedRecoveryFact {
        spec: RecoverySiteSpec {
            role: GrammarRole::Expression(ExpressionRole::CallArgument),
            expected: ExpectedSyntax::Expression,
        },
        range: 0..0,
        kind: RecoveryKind::Missing,
        unexpected: None,
    };
    local.record_yumark_embedded_recovery(retained_fact.clone());
    let local_before = local.value_snapshot();
    let mut sink: chasa::LatestSink<usize, StdErr<char>> = chasa::LatestSink::new();
    <chasa::LatestSink<usize, StdErr<char>> as ErrorSink<usize>>::push(
        &mut sink,
        11..12,
        StdErr::Expected(Expected::new(97, "preseeded-fixed-tail", ())),
    );
    let sink_before = format!("{sink:?}");
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let mut committed = Probe::new(i).commit(FullCstOutput::new(source));
    committed.start_node(SyntaxKind::Root);
    assert!(!committed.probe(|probe| {
        probe_rejected_fixed_tail_recovery_episode_for_test(
            &OperatorTable::empty(),
            ExpressionRole::FieldName,
            probe.input(),
        )
    }));
    let (position, remainder, local_after, retained) = committed.probe(|probe| {
        let i = probe.input();
        (
            i.pos(),
            i.input.remainder().to_owned(),
            i.local.value_snapshot(),
            i.local.drain_yumark_embedded_recoveries(),
        )
    });
    committed.finish_node();
    let output = committed.into_output();
    assert_eq!(position, 0);
    assert_eq!(remainder, source);
    assert_eq!(local_after, local_before);
    assert_eq!(retained, vec![retained_fact]);
    assert!(output.committed_recoveries().is_empty());
    let root = SyntaxNode::new_root(output.finish_prefix());
    assert_eq!(root.to_string(), "");
    assert!(root.children().next().is_none());
    assert_eq!(format!("{sink:?}"), sink_before);
    assert_eq!(
        sink.take_merged(),
        Some(StdSummary {
            unexpected: None,
            expected: vec![Expected::new(97, "preseeded-fixed-tail", ())],
        }),
    );
    assert!(!cut);
    assert!(matches!(
        local.pop_yumark_frame(),
        Some(YumarkFrame::EmbeddedYulang { .. })
    ));
    local.pop_yumark_delimiter(floor, Delimiter::Parenthesis);

    for (source, range) in [
        ("> outer\n>>>\t\r\nafter\n", 8..11),
        (">>>\n>>> content\n>>>\n", 4..7),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        let mixed = outcome
            .output
            .committed_recoveries()
            .iter()
            .find(|record| {
                record.site.role
                    == GrammarRole::Yumark(crate::session::YumarkRole {
                        owner: YumarkOwner::Quote,
                        slot: YumarkSlot::QuoteForm,
                    })
            })
            .expect("mixed quote recovery");
        assert_eq!(mixed.site.range, range, "{source:?}");
        assert_eq!(mixed.kind, RecoveryKind::Error, "{source:?}");
        assert_eq!(
            mixed.expectations[mixed.primary_expectation].expected,
            ExpectedSyntax::Statement,
            "{source:?}",
        );
        let root = SyntaxNode::new_root(outcome.output.finish_prefix());
        assert_eq!(root.to_string(), source);
        let error = root
            .descendants()
            .find(|node| {
                node.kind() == SyntaxKind::Error
                    && usize::from(node.text_range().start()) == range.start
            })
            .expect("mixed quote Error node");
        assert_eq!(error.to_string(), &source[range.clone()], "{source:?}");
        assert_eq!(
            error.parent().map(|parent| parent.kind()),
            Some(SyntaxKind::YmDoc),
            "mixed quote suffix/content owner: {source:?}",
        );
        assert!(sink.take_merged().is_none(), "{source:?}");
    }

    let source = ">>>>\n>>>\ninside\n>>>\t\r\n>>>> \n";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    for (start, expected_parent) in [(20, SyntaxKind::YmDoc), (27, SyntaxKind::YmDoc)] {
        let newline = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| {
                token.kind() == SyntaxKind::Newline
                    && usize::from(token.text_range().start()) == start
            })
            .expect("quote close suffix newline");
        assert_eq!(newline.parent().map(|node| node.kind()), Some(expected_parent));
        assert!(!newline
            .ancestors()
            .any(|ancestor| ancestor.kind() == SyntaxKind::YmQuoteBlock
                && usize::from(ancestor.text_range().start()) == if start == 20 { 5 } else { 0 }));
    }
    assert!(sink.take_merged().is_none());

    for source in ["```\nraw\n``` \nnext", "```\r\nraw\r\n```\t\r\nnext"] {
        let close = source.rfind("```").expect("fence close");
        let newline = source[close..]
            .find('\n')
            .map(|offset| close + offset + 1)
            .expect("close suffix newline end");
        let newline_start = if source.as_bytes()[newline - 2] == b'\r' {
            newline - 2
        } else {
            newline - 1
        };
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        let root = SyntaxNode::new_root(outcome.output.finish_prefix());
        let token = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| {
                token.kind() == SyntaxKind::Newline
                    && usize::from(token.text_range().start()) == newline_start
            })
            .expect("fence close suffix newline");
        assert_eq!(token.parent().map(|node| node.kind()), Some(SyntaxKind::YmDoc));
        assert!(!token
            .ancestors()
            .any(|ancestor| ancestor.kind() == SyntaxKind::YmCodeFence));
        assert!(sink.take_merged().is_none(), "{source:?}");
    }

    let table = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "%%",
            OperatorFixities::new().with_infix(BindingPower::scalar(10), BindingPower::scalar(10)),
        ),
        OperatorDeclaration::new(
            "---",
            OperatorFixities::new().with_infix(BindingPower::scalar(10), BindingPower::scalar(10)),
        ),
    ])
    .unwrap();
    let source = "\\ref(1 --- 2);";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &table,
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert!(
        !outcome
            .output
            .committed_recoveries()
            .iter()
            .any(|record| matches!(record.site.role, GrammarRole::Yumark(_)))
    );
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::InfixOperatorUse)
    );
    let reference = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmInlineRef)
        .expect("reference wrapper");
    assert!(
        reference
            .children_with_tokens()
            .any(|child| child.kind() == SyntaxKind::Semicolon)
    );

    let source = "\\ref(1\n  ---\n  2)";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &table,
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert!(
        !outcome
            .output
            .committed_recoveries()
            .iter()
            .any(|record| { matches!(record.site.role, GrammarRole::Yumark(_)) })
    );
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::InfixOperatorUse)
    );

    let source = "[doc]:apply(1 %% 2)";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &table,
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert!(
        !outcome
            .output
            .committed_recoveries()
            .iter()
            .any(|record| { matches!(record.site.role, GrammarRole::Yumark(_)) })
    );
    let root = SyntaxNode::new_root(outcome.output.finish_prefix());
    let args = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::YmInlineApplyArgs)
        .expect("apply arguments");
    assert!(
        args.descendants()
            .any(|node| node.kind() == SyntaxKind::InfixOperatorUse)
    );

    for (source, expected) in [
        (
            "*text",
            ExpectedSyntax::Yumark(YumarkSyntaxEvidence::EmphasisMarker),
        ),
        (
            "```\nraw",
            ExpectedSyntax::Yumark(YumarkSyntaxEvidence::FenceMarker),
        ),
        (
            ">>>\nraw",
            ExpectedSyntax::Yumark(YumarkSyntaxEvidence::QuoteFenceMarker),
        ),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        let record = outcome
            .output
            .committed_recoveries()
            .iter()
            .find(|record| matches!(record.site.role, GrammarRole::Yumark(_)))
            .expect("typed Yumark close recovery");
        assert_eq!(record.kind, RecoveryKind::Missing, "{source:?}");
        assert_eq!(
            record.expectations[record.primary_expectation].expected, expected,
            "{source:?}",
        );
        assert_eq!(outcome.output.finish_prefix().to_string(), source);
    }

    let source = ">>>\n```\nraw";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(
        outcome
            .output
            .committed_recoveries()
            .iter()
            .filter_map(|record| match record.site.role {
                GrammarRole::Yumark(role) => Some((role.owner, record.site.range.clone())),
                _ => None,
            })
            .collect::<Vec<_>>(),
        vec![
            (YumarkOwner::CodeFence, 11..11),
            (YumarkOwner::Quote, 11..11)
        ],
    );
    assert_eq!(outcome.output.finish_prefix().to_string(), source);

    let paragraph_source = "x".repeat(4096);
    let mut input = SourceInput::new(&paragraph_source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        &paragraph_source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.work.paragraph_bytes, paragraph_source.len());
    assert_eq!(outcome.output.finish_prefix().to_string(), paragraph_source);

    for (source, expected_raw_bytes) in [("é文", "é文".len()), ("# heading\n", 0)] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(
            outcome.work.paragraph_bytes, expected_raw_bytes,
            "{source:?}"
        );
        assert_eq!(outcome.output.finish_prefix().to_string(), source);
    }

    let fence_source = format!("```\n{}\n```", "x".repeat(4096));
    let mut input = SourceInput::new(&fence_source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        &fence_source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.work.fence_bytes, 4097);
    assert_eq!(outcome.output.finish_prefix().to_string(), fence_source);

    let fence_source = "```\r\nx\r\n```";
    let mut input = SourceInput::new(fence_source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        fence_source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.work.fence_bytes, 3);
    assert_eq!(
        outcome.line,
        LineState {
            last_newline: Some((6, 8)),
            line_start: 8,
            line_indent: 0,
            at_line_start: false,
        }
    );
    assert_eq!(outcome.output.finish_prefix().to_string(), fence_source);

    let source = "# section\n- item\n  > quote\n#.";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(outcome.work.frame_pushes, outcome.work.frame_pops);
    assert_eq!(outcome.work.section_lookups, 1);
    assert_eq!(outcome.frame_depth, 0);

    let source = "a\r\n  b";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(
        outcome.line,
        LineState {
            last_newline: Some((1, 3)),
            line_start: 3,
            line_indent: 2,
            at_line_start: false,
        }
    );

    for (source, expected) in [
        (
            "a\n  b",
            LineState {
                last_newline: Some((1, 2)),
                line_start: 2,
                line_indent: 2,
                at_line_start: false,
            },
        ),
        (
            "a\rb",
            LineState {
                last_newline: None,
                line_start: 0,
                line_indent: 0,
                at_line_start: false,
            },
        ),
    ] {
        let mut input = SourceInput::new(source);
        let mut local = ParseLocal::new();
        local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut sink = chasa::LatestSink::new();
        let mut cut = false;
        let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
        let outcome = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(outcome.line, expected, "{source:?}");
        assert_eq!(outcome.output.finish_prefix().to_string(), source);
    }

    let source = "\\ref(1)\r\nx";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::BlockDocument,
        },
        i,
    );
    assert_eq!(
        outcome.line,
        LineState {
            last_newline: Some((7, 9)),
            line_start: 9,
            line_indent: 0,
            at_line_start: false,
        }
    );

    let source = "a\r\nouter";
    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = parse_gate3_ast(
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::LineDocument,
        },
        &mut i,
    );
    assert_eq!(outcome.document.range, 0..1);
    assert_eq!(i.input.remainder(), "\r\nouter");
    assert_eq!(
        i.local.line(),
        LineState {
            last_newline: None,
            line_start: 0,
            line_indent: 0,
            at_line_start: false,
        }
    );
    drop(i);
    assert!(sink.take_merged().is_none());

    let mut input = SourceInput::new(source);
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let outcome = commit_gate3_direct(
        source,
        &OperatorTable::empty(),
        Gate3Envelope {
            base_column: 0,
            stop: YumarkEnvelopeStop::LineDocument,
        },
        i,
    );
    assert_eq!(outcome.range, 0..1);
    assert_eq!(outcome.remainder, "\r\nouter");
    assert_eq!(
        outcome.line,
        LineState {
            last_newline: None,
            line_start: 0,
            line_indent: 0,
            at_line_start: false,
        }
    );
    assert_eq!(outcome.output.finish_prefix().to_string(), "a");

    let mut input = SourceInput::new("(\n# parent");
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let before = local.value_snapshot();
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    assert!(!probe_gate3_bridge_candidate(&mut i));
    assert_eq!(i.pos(), 0);
    assert_eq!(i.input.remainder(), "(\n# parent");
    assert_eq!(i.local.value_snapshot(), before);
    drop(i);
    assert!(sink.take_merged().is_none());
    assert!(!cut);

    let mut input = SourceInput::new("(\n# parent");
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let before = local.value_snapshot();
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let (accepted, output) = probe_gate3_bridge_candidate_direct("(\n# parent", i);
    assert!(!accepted);
    assert_eq!(input.remainder(), "(\n# parent");
    assert_eq!(local.value_snapshot(), before);
    assert_eq!(output.finish_prefix().to_string(), "");
    assert!(sink.take_merged().is_none());
    assert!(!cut);

    let mut input = SourceInput::new("(\nparent");
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let before = local.value_snapshot();
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let mut i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    assert!(probe_gate3_bridge_candidate(&mut i));
    assert_eq!(i.pos(), 0);
    assert_eq!(i.input.remainder(), "(\nparent");
    assert_eq!(i.local.value_snapshot(), before);
    drop(i);
    assert!(sink.take_merged().is_none());
    assert!(!cut);

    let mut input = SourceInput::new("(\nparent");
    let mut local = ParseLocal::new();
    local.set_line(LineState {
        at_line_start: true,
        ..LineState::default()
    });
    let before = local.value_snapshot();
    let mut sink = chasa::LatestSink::new();
    let mut cut = false;
    let i = In::new(&mut input, &mut sink, IsCut::new(&mut cut)).set_local(&mut local);
    let (accepted, output) = probe_gate3_bridge_candidate_direct("(\nparent", i);
    assert!(accepted);
    assert_eq!(input.remainder(), "(\nparent");
    assert_eq!(local.value_snapshot(), before);
    assert_eq!(output.finish_prefix().to_string(), "");
    assert!(sink.take_merged().is_none());
    assert!(!cut);
}

#[test]
fn gate3b_derives_via_target_episode() {
    let role = GrammarRole::Declaration(DeclarationRole::Derives(DerivesRole::ViaTarget));
    for (source, expected) in [
        (
            "\\ref({type T = Int derives Eq via})",
            Some((33..33, RecoveryKind::Missing, SyntaxKind::Missing)),
        ),
        (
            "\\ref({type T = Int derives Eq via @ key})",
            Some((34..36, RecoveryKind::Error, SyntaxKind::Error)),
        ),
        ("\\ref({type T = Int derives Eq via key})", None),
    ] {
        let mut ast_input = SourceInput::new(source);
        let mut ast_local = ParseLocal::new();
        ast_local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut ast_sink = chasa::LatestSink::new();
        let mut ast_cut = false;
        let mut i = In::new(
            &mut ast_input,
            &mut ast_sink,
            IsCut::new(&mut ast_cut),
        )
        .set_local(&mut ast_local);
        let ast = parse_gate3_ast(
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            &mut i,
        );
        assert_eq!(
            ast.document.range,
            0..source.len(),
            "AST range: {source:?}",
        );
        assert_eq!(i.input.remainder(), "", "AST remainder: {source:?}");
        assert_eq!(i.local.yumark_frame_depth(), 0, "AST frames: {source:?}");
        let expected_facts = expected
            .as_ref()
            .map(|(range, kind, _)| {
                vec![(
                    role,
                    range.clone(),
                    *kind,
                    ExpectedSyntax::Identifier,
                    0usize,
                )]
            })
            .unwrap_or_default();
        assert_eq!(
            ast.recoveries
                .iter()
                .map(|fact| {
                    (
                        fact.role,
                        fact.range.clone(),
                        fact.kind,
                        fact.expected,
                        fact.order,
                    )
                })
                .collect::<Vec<_>>(),
            expected_facts,
            "AST ViaTarget facts: {source:?}",
        );
        let ast_snapshot = i.local.value_snapshot();
        drop(i);
        assert!(ast_sink.take_merged().is_none(), "AST sink: {source:?}");

        let mut direct_input = SourceInput::new(source);
        let mut direct_local = ParseLocal::new();
        direct_local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut direct_sink = chasa::LatestSink::new();
        let mut direct_cut = false;
        let i = In::new(
            &mut direct_input,
            &mut direct_sink,
            IsCut::new(&mut direct_cut),
        )
        .set_local(&mut direct_local);
        let direct = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(direct.range, 0..source.len(), "direct range: {source:?}");
        assert_eq!(direct.remainder, "", "direct remainder: {source:?}");
        assert_eq!(direct.frame_depth, 0, "direct frames: {source:?}");
        assert_eq!(
            direct
                .output
                .committed_recoveries()
                .iter()
                .map(|record| {
                    (
                        record.site.role,
                        record.site.range.clone(),
                        record.kind,
                        record.expectations[record.primary_expectation].expected,
                    )
                })
                .collect::<Vec<_>>(),
            expected
                .as_ref()
                .map(|(range, kind, _)| {
                    vec![(role, range.clone(), *kind, ExpectedSyntax::Identifier)]
                })
                .unwrap_or_default(),
            "direct ViaTarget facts: {source:?}",
        );
        let mut expected_direct_snapshot = ast_snapshot;
        expected_direct_snapshot.next_diagnostic_id += if expected.is_some() { 1 } else { 0 };
        assert_eq!(
            direct_local.value_snapshot(),
            expected_direct_snapshot,
            "AST/direct state: {source:?}",
        );
        assert!(
            direct_sink.take_merged().is_none(),
            "direct sink: {source:?}"
        );
        let root = SyntaxNode::new_root(direct.output.finish_prefix());
        assert_eq!(root.to_string(), source, "lossless: {source:?}");
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::CallTail),
            "borrowed wrapper has no CallTail: {source:?}",
        );
        let clause = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::DerivesClause)
            .expect("embedded DerivesClause");
        let args = clause
            .ancestors()
            .find(|node| node.kind() == SyntaxKind::YmYulangArgs)
            .expect("DerivesClause remains inside borrowed Yumark arguments");
        assert_eq!(
            args.parent().map(|parent| parent.kind()),
            Some(SyntaxKind::YmInlineRef),
        );
        for kind in [
            SyntaxKind::TypeDeclaration,
            SyntaxKind::Statement,
            SyntaxKind::BracedStatementBlockExpression,
            SyntaxKind::OperatorChain,
        ] {
            assert!(
                clause.ancestors().any(|ancestor| ancestor.kind() == kind),
                "wrapper ancestor {kind:?}: {source:?}",
            );
        }
        let recovery_nodes = clause
            .children()
            .filter(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
            .collect::<Vec<_>>();
        match expected {
            Some((range, _, node_kind)) => {
                let [node] = recovery_nodes.as_slice() else {
                    panic!("one immediate ViaTarget recovery node: {source:?}");
                };
                assert_eq!(node.kind(), node_kind);
                assert_eq!(
                    usize::from(node.text_range().start())..usize::from(node.text_range().end()),
                    range,
                );
            }
            None => assert!(recovery_nodes.is_empty(), "clean ViaTarget: {source:?}"),
        }
        let close_brace = source.rfind('}').expect("braced statement close");
        let brace = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| {
                token.kind() == SyntaxKind::RBrace
                    && usize::from(token.text_range().start()) == close_brace
            })
            .expect("outer braced-statement close token");
        assert_eq!(
            brace.parent().map(|parent| parent.kind()),
            Some(SyntaxKind::BracedStatementBlockExpression),
        );
        let close_paren = source.rfind(')').expect("borrowed close");
        let paren = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| {
                token.kind() == SyntaxKind::RParen
                    && usize::from(token.text_range().start()) == close_paren
            })
            .expect("Yumark-owned borrowed close token");
        assert_eq!(
            paren.parent().map(|parent| parent.kind()),
            Some(SyntaxKind::YmYulangArgs),
        );
        if source.contains("@ key") {
            assert!(clause.descendants_with_tokens().any(|element| {
                element.into_token().is_some_and(|token| {
                    token.kind() == SyntaxKind::Identifier && token.text() == "key"
                })
            }));
        }
    }
}

#[test]
fn gate3b_declaration_companion_introducer_episode() {
    let role = GrammarRole::Declaration(DeclarationRole::Companion(
        DeclarationCompanionRole::Introducer,
    ));
    let primary = ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace));
    let auxiliary = ExpectedSyntax::Punctuation(PunctuationEvidence::Colon);
    for (source, expected) in [
        (
            "\\ref({type T = Int with})",
            Some((
                23..23,
                RecoveryKind::Missing,
                None,
                SyntaxKind::Missing,
            )),
        ),
        (
            "\\ref({type T = Int with :: item})",
            Some((
                24..25,
                RecoveryKind::Error,
                Some(crate::session::UnexpectedCategory::OtherCharacter),
                SyntaxKind::Error,
            )),
        ),
        (
            "\\ref({type T = Int with item})",
            Some((
                24..24,
                RecoveryKind::Missing,
                None,
                SyntaxKind::Missing,
            )),
        ),
        (
            "\\ref({type T = Int with\n})",
            Some((
                23..23,
                RecoveryKind::Missing,
                None,
                SyntaxKind::Missing,
            )),
        ),
        ("\\ref({type T = Int with: item})", None),
    ] {
        let mut ast_input = SourceInput::new(source);
        let mut ast_local = ParseLocal::new();
        ast_local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut ast_sink = chasa::LatestSink::new();
        let mut ast_cut = false;
        let mut i = In::new(
            &mut ast_input,
            &mut ast_sink,
            IsCut::new(&mut ast_cut),
        )
        .set_local(&mut ast_local);
        let ast = parse_gate3_ast(
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            &mut i,
        );
        assert_eq!(ast.document.range, 0..source.len(), "AST range: {source:?}");
        assert_eq!(i.input.remainder(), "", "AST remainder: {source:?}");
        assert_eq!(i.local.yumark_frame_depth(), 0, "AST frames: {source:?}");
        assert_eq!(
            ast.recoveries
                .iter()
                .map(|fact| {
                    (
                        fact.role,
                        fact.range.clone(),
                        fact.kind,
                        fact.expected,
                        fact.unexpected,
                        fact.order,
                    )
                })
                .collect::<Vec<_>>(),
            expected
                .as_ref()
                .map(|(range, kind, unexpected, _)| {
                    vec![(
                        role,
                        range.clone(),
                        *kind,
                        primary,
                        *unexpected,
                        0usize,
                    )]
                })
                .unwrap_or_default(),
            "AST D12a fact: {source:?}",
        );
        let ast_snapshot = i.local.value_snapshot();
        drop(i);
        assert!(ast_sink.take_merged().is_none(), "AST sink: {source:?}");

        let mut direct_input = SourceInput::new(source);
        let mut direct_local = ParseLocal::new();
        direct_local.set_line(LineState {
            at_line_start: true,
            ..LineState::default()
        });
        let mut direct_sink = chasa::LatestSink::new();
        let mut direct_cut = false;
        let i = In::new(
            &mut direct_input,
            &mut direct_sink,
            IsCut::new(&mut direct_cut),
        )
        .set_local(&mut direct_local);
        let direct = commit_gate3_direct(
            source,
            &OperatorTable::empty(),
            Gate3Envelope {
                base_column: 0,
                stop: YumarkEnvelopeStop::BlockDocument,
            },
            i,
        );
        assert_eq!(direct.range, 0..source.len(), "direct range: {source:?}");
        assert_eq!(direct.remainder, "", "direct remainder: {source:?}");
        assert_eq!(direct.frame_depth, 0, "direct frames: {source:?}");
        let records = direct.output.committed_recoveries();
        match expected.as_ref() {
            Some((range, kind, unexpected, _)) => {
                let [record] = records else {
                    panic!("one D12a direct record: {source:?}");
                };
                assert_eq!(record.id.0, ast_snapshot.next_diagnostic_id);
                assert_eq!(record.site.role, role);
                assert_eq!(record.site.range, *range);
                assert_eq!(record.kind, *kind);
                assert_eq!(
                    match record.unexpected.as_ref() {
                        [] => None,
                        [crate::session::UnexpectedSyntax::Token { category, .. }] => {
                            Some(*category)
                        }
                        unexpected => panic!(
                            "one D12a direct unexpected token: {source:?}: {unexpected:?}"
                        ),
                    },
                    *unexpected,
                    "D12a direct unexpected: {source:?}",
                );
                assert_eq!(record.primary_expectation, 0);
                assert_eq!(
                    record
                        .expectations
                        .iter()
                        .map(|expectation| expectation.expected)
                        .collect::<Vec<_>>(),
                    vec![primary, auxiliary],
                    "D12a primary/auxiliary order: {source:?}",
                );
                assert!(record.expectations.iter().all(|expectation| {
                    expectation.role == role && expectation.range == *range
                }));
            }
            None => assert!(records.is_empty(), "clean D12a direct records: {source:?}"),
        }
        let mut expected_direct_snapshot = ast_snapshot;
        expected_direct_snapshot.next_diagnostic_id += usize::from(expected.is_some()) as u32;
        assert_eq!(
            direct_local.value_snapshot(),
            expected_direct_snapshot,
            "D12a AST/direct state: {source:?}",
        );
        assert!(
            direct_sink.take_merged().is_none(),
            "direct sink: {source:?}",
        );
        let root = SyntaxNode::new_root(direct.output.finish_prefix());
        assert_eq!(root.to_string(), source, "lossless: {source:?}");
        let generic = root
            .descendants()
            .filter(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
            .collect::<Vec<_>>();
        match expected {
            Some((range, _, _, node_kind)) => {
                let [node] = generic.as_slice() else {
                    panic!("one D12a generic recovery node: {source:?}");
                };
                assert_eq!(node.kind(), node_kind);
                assert_eq!(
                    usize::from(node.text_range().start())..usize::from(node.text_range().end()),
                    range,
                );
                assert_eq!(
                    node.parent().map(|parent| parent.kind()),
                    Some(SyntaxKind::DeclarationCompanion),
                );
            }
            None => assert!(generic.is_empty(), "clean D12a topology: {source:?}"),
        }
        if source.contains("item") {
            let companion = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::DeclarationCompanion)
                .expect("embedded declaration companion");
            assert!(
                companion.descendants_with_tokens().any(|element| {
                    element.into_token().is_some_and(|token| {
                        token.kind() == SyntaxKind::Identifier && token.text() == "item"
                    })
                }),
                "D12a retries the valid body: {source:?}",
            );
        }
        let close_brace = source.rfind('}').expect("braced statement close");
        let brace = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| {
                token.kind() == SyntaxKind::RBrace
                    && usize::from(token.text_range().start()) == close_brace
            })
            .expect("outer braced-statement close token");
        assert_eq!(
            brace.parent().map(|parent| parent.kind()),
            Some(SyntaxKind::BracedStatementBlockExpression),
            "D12a outer brace owner: {source:?}",
        );
        let close_paren = source.rfind(')').expect("borrowed Yumark close");
        let paren = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| {
                token.kind() == SyntaxKind::RParen
                    && usize::from(token.text_range().start()) == close_paren
            })
            .expect("Yumark-owned borrowed close token");
        assert_eq!(
            paren.parent().map(|parent| parent.kind()),
            Some(SyntaxKind::YmYulangArgs),
            "D12a borrowed close owner: {source:?}",
        );
    }

}
