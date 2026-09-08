use super::*;

use crate::rewrite::{
    driver::Either,
    item::{BorrowedTarget, Boundary},
    yumark::{FenceOpener, FencePrefixPolicy},
};

fn syntax_root(green: GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green)
}

fn count(root: &SyntaxNode, kind: SyntaxKind) -> usize {
    root.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn identifier_texts(node: &SyntaxNode) -> Vec<String> {
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Identifier)
        .map(|token| token.text().to_owned())
        .collect()
}

fn active_fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    }
}

#[test]
fn declaration_variants_build_all_payloads_in_all_four_forms() {
    for (form, source) in [
        (
            VariantSequenceForm::Braced,
            "{Unit, From from Pair(Int) -> Out, Named{x: T}, Tuple(U, V), Pos T U}",
        ),
        (
            VariantSequenceForm::ColonIndented,
            ":\n  Unit\n  From from Pair(Int) -> Out\n  Named{x: T}\n  Tuple(U, V)\n  Pos T U",
        ),
        (
            VariantSequenceForm::EqualsInline,
            "= Unit | From from Pair(Int) -> Out | Named{x: T} | Tuple(U, V) | Pos T U",
        ),
        (
            VariantSequenceForm::EqualsIndented,
            "=\n  Unit\n  | From from Pair(Int) -> Out\n  | Named{x: T}\n  | Tuple(U, V)\n  | Pos T U",
        ),
    ] {
        let (green, exit, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{form:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::EnumVariant), 5, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::FromKw), 0, "tokens are not nodes");
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::FromKw)
                .count(),
            1,
            "{form:?}",
        );
        assert_eq!(count(&root, SyntaxKind::StructField), 3, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::TypeExpression), 8, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::Missing), 0, "{form:?}\n{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Error), 0, "{form:?}\n{root:#?}");
        assert!(exit.is_some());
    }
}

#[test]
fn declaration_variant_separator_clusters_keep_only_real_empty_slots() {
    for (form, source, variants, missing) in [
        (VariantSequenceForm::Braced, "{,A,,B,}", 4, 2),
        (
            VariantSequenceForm::ColonIndented,
            ":\n  | A\n  || B\n  |",
            3,
            1,
        ),
        (VariantSequenceForm::EqualsInline, "= | A || B |", 3, 1),
        (
            VariantSequenceForm::EqualsIndented,
            "=\n  | A\n  || B\n  |",
            3,
            1,
        ),
    ] {
        let (green, _, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{form:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::EnumVariant), variants, "{form:?}");
        assert_eq!(
            count(&root, SyntaxKind::Missing),
            missing,
            "{form:?}\n{root:#?}"
        );
    }
}

#[test]
fn declaration_variant_layout_separates_same_block_and_keeps_deeper_payloads() {
    for (form, source) in [
        (VariantSequenceForm::ColonIndented, ":\n  A T\n    U\n  B"),
        (VariantSequenceForm::EqualsIndented, "=\n  A T\n    U\n  B"),
        (VariantSequenceForm::Braced, "{\n  A T\n    U\n  B\n}"),
    ] {
        let (green, _, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{form:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::EnumVariant), 2, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::TypeExpression), 2, "{form:?}");
        assert_eq!(count(&root, SyntaxKind::Missing), 0, "{form:?}\n{root:#?}");
    }
}

#[test]
fn equals_inline_keeps_strictly_deeper_payload_lines_before_the_next_pipe() {
    let source = "= A T\n  U | B";
    let (green, _, _) = run_declaration_variant(
        source,
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);
    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "T", "U"]);
    assert_eq!(count(&variants[0], SyntaxKind::TypeExpression), 2);
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Error), 0, "{root:#?}");
}

#[test]
fn braced_pipe_recovers_inside_the_payload_instead_of_separating_variants() {
    let source = "{A T | U, B}";
    let (green, _, _) = run_declaration_variant(
        source,
        VariantSequenceForm::Braced,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);
    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "T", "U"]);
    assert_eq!(count(&variants[0], SyntaxKind::TypeExpression), 2);
    assert_eq!(count(&variants[0], SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
}

#[test]
fn declaration_variant_payload_recovery_stops_once_at_the_outer_pipe() {
    let (green, _, _) = run_declaration_variant(
        "= A from | B | C @ | D",
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "= A from | B | C @ | D");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::EnumVariant), 4, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::TypeExpression), 1, "{root:#?}");
}

#[test]
fn declaration_variant_outer_pipe_separates_all_non_braced_forms() {
    for (form, source) in [
        (VariantSequenceForm::ColonIndented, ":\n  A from T | B"),
        (VariantSequenceForm::EqualsInline, "= A from T | B"),
        (VariantSequenceForm::EqualsIndented, "=\n  A from T\n  | B"),
    ] {
        let (green, _, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{form:?}");
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::EnumVariant),
            2,
            "{form:?}\n{root:#?}"
        );
        assert_eq!(count(&root, SyntaxKind::Error), 0, "{form:?}\n{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Missing), 0, "{form:?}\n{root:#?}");
    }
}

#[test]
fn declaration_variant_outer_pipe_is_suspended_inside_nested_type_episodes() {
    for (source, groups) in [("= A from (T | U) | B", 1), ("= A from ((T | U)) | B", 2)] {
        let (green, _, _) = run_declaration_variant(
            source,
            VariantSequenceForm::EqualsInline,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), source);
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::EnumVariant), 2, "{root:#?}");
        assert_eq!(
            count(&root, SyntaxKind::ParenthesizedTypeGroup),
            groups,
            "{root:#?}"
        );
        assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Pipe)
                .count(),
            2,
        );
    }
}

#[test]
fn declaration_variant_contextual_pipe_stays_local_to_each_nested_type_owner() {
    for (source, owner) in [
        ("= A from (| T) | B", SyntaxKind::ParenthesizedTypeGroup),
        ("= A from (T | U) | B", SyntaxKind::ParenthesizedTypeGroup),
        ("= A from F(| T) | B", SyntaxKind::TypeCallTail),
        ("= A from F(T | U) | B", SyntaxKind::TypeCallTail),
        ("= A from [| T] -> X | B", SyntaxKind::BracketRow),
        ("= A from [T | U] -> X | B", SyntaxKind::BracketRow),
        ("= A from (T -> | U) | B", SyntaxKind::TypeArrowTail),
        ("= A from (T -> U | V) | B", SyntaxKind::TypeArrowTail),
        ("= A from (for 'a: | T) | B", SyntaxKind::ForallType),
        ("= A from (for 'a: T | U) | B", SyntaxKind::ForallType),
        ("= A from {x: | T} | B", SyntaxKind::NamedRecordType),
        ("= A from {x: T | U} | B", SyntaxKind::NamedRecordType),
        ("= A from '[| T] | B", SyntaxKind::EffectRowType),
        ("= A from '[T | U] | B", SyntaxKind::EffectRowType),
        (
            "= A from :{Tag | T} | B",
            SyntaxKind::PolymorphicVariantType,
        ),
        (
            "= A from :{Tag T | U} | B",
            SyntaxKind::PolymorphicVariantType,
        ),
        ("= A from (@ | T) | B", SyntaxKind::ParenthesizedTypeGroup),
    ] {
        let (green, _, _) = run_declaration_variant(
            source,
            VariantSequenceForm::EqualsInline,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::EnumVariant),
            2,
            "{source:?}\n{root:#?}"
        );
        assert!(
            root.descendants().any(|node| node.kind() == owner),
            "{source:?}\n{root:#?}"
        );
        assert!(
            count(&root, SyntaxKind::Error) >= 1,
            "{source:?}\n{root:#?}"
        );
        let bars = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.text() == "|")
            .collect::<Vec<_>>();
        assert_eq!(bars.len(), 2, "{source:?}\n{root:#?}");
        // T3 CallArgument Error retains payload boundaries with Unknown kind;
        // the current-Item owners retain the native Pipe kind instead.
        let inner_kind = if owner == SyntaxKind::TypeCallTail {
            SyntaxKind::Unknown
        } else {
            SyntaxKind::Pipe
        };
        assert_eq!(bars[0].kind(), inner_kind, "{source:?}\n{root:#?}");
        assert!(
            bars[0]
                .parent_ancestors()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}\n{root:#?}"
        );
        assert_eq!(bars[1].kind(), SyntaxKind::Pipe, "{source:?}\n{root:#?}");
        assert!(
            !bars[1]
                .parent_ancestors()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}\n{root:#?}"
        );
    }
}

#[test]
fn braced_variant_fields_keep_contextual_pipe_as_local_malformed_type_input() {
    for source in ["{A{x: | T}, B}", "{A{x: T | U}, B}"] {
        let (green, _, _) = run_declaration_variant(
            source,
            VariantSequenceForm::Braced,
            0,
            LineEntry::InLine,
            None,
        );
        assert_eq!(green.to_string(), source);
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::EnumVariant),
            2,
            "{source:?}\n{root:#?}"
        );
        assert!(
            count(&root, SyntaxKind::Error) >= 1,
            "{source:?}\n{root:#?}"
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Pipe)
                .count(),
            1,
            "{source:?}\n{root:#?}",
        );
    }
}

#[test]
fn malformed_named_payload_retry_keeps_pipe_lexical_and_converges_at_outer_comma() {
    let source = "{A{@ | x:T}, B}";
    let (green, exit, _) = run_declaration_variant(
        source,
        VariantSequenceForm::Braced,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));

    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "x", "T"]);
    assert_eq!(count(&variants[0], SyntaxKind::StructField), 2, "{root:#?}");
    assert_eq!(count(&variants[0], SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    let pipes = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Pipe)
        .collect::<Vec<_>>();
    assert_eq!(pipes.len(), 1, "{root:#?}");
    assert!(
        pipes[0]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::StructField),
        "{root:#?}",
    );
    assert!(
        pipes[0]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::Error),
        "{root:#?}",
    );
}

#[test]
fn type_apply_argument_keeps_local_pipe_lexical_before_outer_variant_pipe() {
    let source = "= A from F T::|U | B";
    let (green, _, _) = run_declaration_variant(
        source,
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);

    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "F", "T", "U"]);
    assert_eq!(count(&variants[0], SyntaxKind::TypeApplyArgument), 1);
    assert_eq!(count(&variants[0], SyntaxKind::TypePathTail), 1);
    assert_eq!(count(&variants[0], SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
    let pipes = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Pipe)
        .collect::<Vec<_>>();
    assert_eq!(pipes.len(), 2, "{root:#?}");
    assert!(
        pipes[0]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument),
        "{root:#?}",
    );
    assert!(
        pipes[0]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::Error),
        "{root:#?}",
    );
    assert!(
        !pipes[1]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::TypeExpression),
        "{root:#?}",
    );
}

#[test]
fn completed_type_path_returns_same_episode_pipe_to_variant_owner() {
    let source = "= A from T::U | B";
    let (green, _, _) = run_declaration_variant(
        source,
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), source);

    let root = syntax_root(green);
    let variants = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::EnumVariant)
        .collect::<Vec<_>>();
    assert_eq!(variants.len(), 2, "{root:#?}");
    assert_eq!(identifier_texts(&variants[0]), ["A", "T", "U"]);
    assert_eq!(count(&variants[0], SyntaxKind::TypePathTail), 1);
    assert_eq!(identifier_texts(&variants[1]), ["B"]);
    assert_eq!(count(&root, SyntaxKind::Error), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
    let pipes = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Pipe)
        .collect::<Vec<_>>();
    assert_eq!(pipes.len(), 1, "{root:#?}");
    assert!(
        !pipes[0]
            .parent_ancestors()
            .any(|node| node.kind() == SyntaxKind::TypeExpression),
        "{root:#?}",
    );
}

#[test]
fn declaration_variant_indented_dedent_remains_one_pending_item() {
    for (form, source, accepted) in [
        (VariantSequenceForm::ColonIndented, ":\n  A\nnext", ":\n  A"),
        (
            VariantSequenceForm::EqualsIndented,
            "=\n  A\r\nnext",
            "=\n  A",
        ),
        (VariantSequenceForm::EqualsInline, "= A\nnext", "= A"),
    ] {
        let (green, exit, _) = run_declaration_variant(source, form, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{form:?}");
        let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
            panic!("dedent must remain pending: {form:?}")
        };
        assert_eq!(item.payload_view().spelling(), Some("next"));
        assert_eq!(
            emit_pending_leading_text(&mut item),
            if source.contains("\r\n") {
                "\r\n"
            } else {
                "\n"
            },
            "{form:?}",
        );
    }
}

#[test]
fn declaration_variant_fields_borrow_outer_closes_after_local_missing_close() {
    let (green, exit, _) = run_declaration_variant(
        "{A(T}",
        VariantSequenceForm::Braced,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "{A(T}");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::EnumVariant), 1);
    assert_eq!(count(&root, SyntaxKind::StructField), 1);
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));

    let (green, exit, _) = run_declaration_variant(
        "= A{x:T)",
        VariantSequenceForm::EqualsInline,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "= A{x:T");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
        panic!("outer close must remain the exact pending Item")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RParen));
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
}

#[test]
fn declaration_variant_hands_raw_close_and_fence_boundary_up_exactly() {
    let (green, exit, _) = run_declaration_variant(
        "= A}",
        VariantSequenceForm::EqualsInline,
        91,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "= A");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
        panic!("caller close must stay pending")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RBrace));

    let fence = active_fence();
    let accepted = "> > = A";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let origin = 700;
    let (green, exit, remainder) = run_declaration_variant(
        &source,
        VariantSequenceForm::EqualsInline,
        origin,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) = exit
    else {
        panic!("fence close must stay pending with its line-entry fact")
    };
    let boundary = item.payload_view();
    assert!(boundary.is_boundary());
    let (leading, pending) = emit_terminal_leading_text(item);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
    let root = syntax_root(green);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        1,
    );
}

#[test]
fn shared_field_extraction_preserves_struct_named_and_tuple_shapes() {
    for (source, fields) in [
        ("struct S{x:T, y:U}", 2),
        ("struct S(T, U)", 2),
        ("struct S{x:T] y:U}", 2),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::StructField), fields, "{source:?}");
    }
}
