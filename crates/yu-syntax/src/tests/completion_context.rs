use crate::{
    ExpectedSyntax, GrammarSlotRole, Sigil, SigilContext, SyntaxEnvironment, SyntaxKind,
    SyntaxNode, cursor_context, parse_file, scan_header,
};
use std::sync::Arc;

fn parse_root(source: &str) -> SyntaxNode {
    let source: Arc<str> = source.into();
    let header = Arc::new(scan_header(source.clone()));
    let file = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    file.source_root().syntax().clone()
}

#[test]
fn mapped_prefix_slots_are_lossless() {
    for (source, owner, role, expected) in [
        (
            "x.",
            SyntaxKind::FieldTail,
            GrammarSlotRole::Name,
            ExpectedSyntax::Identifier,
        ),
        (
            "std::foo::",
            SyntaxKind::PathTail,
            GrammarSlotRole::Name,
            ExpectedSyntax::Identifier,
        ),
        (
            "use std::",
            SyntaxKind::UsePath,
            GrammarSlotRole::Name,
            ExpectedSyntax::Identifier,
        ),
        (
            "infix (+) 50 51 = add\n1 +",
            SyntaxKind::OperatorChain,
            GrammarSlotRole::Item,
            ExpectedSyntax::Expression,
        ),
        (
            "for x in",
            SyntaxKind::ForIterable,
            GrammarSlotRole::Item,
            ExpectedSyntax::Expression,
        ),
        (
            "my ",
            SyntaxKind::Pattern,
            GrammarSlotRole::Head,
            ExpectedSyntax::Pattern,
        ),
        (
            "type T = ",
            SyntaxKind::TypeExpression,
            GrammarSlotRole::Item,
            ExpectedSyntax::TypeExpression,
        ),
        (
            "case x:",
            SyntaxKind::Pattern,
            GrammarSlotRole::Head,
            ExpectedSyntax::Pattern,
        ),
        (
            "catch x:",
            SyntaxKind::Pattern,
            GrammarSlotRole::Head,
            ExpectedSyntax::Pattern,
        ),
        (
            "catch x: err ->",
            SyntaxKind::CatchArm,
            GrammarSlotRole::Body,
            ExpectedSyntax::Expression,
        ),
        (
            "\"%{x",
            SyntaxKind::StringInterpolation,
            GrammarSlotRole::Close,
            ExpectedSyntax::ClosingBrace,
        ),
        (
            "x if",
            SyntaxKind::Condition,
            GrammarSlotRole::Condition,
            ExpectedSyntax::Condition,
        ),
    ] {
        let root = parse_root(source);
        assert_eq!(root.to_string(), source);
        let facts = crate::structural_diagnostic::collect(&root);
        assert!(
            facts
                .iter()
                .any(|fact| fact.range() == &(source.len()..source.len())
                    && fact
                        .identity()
                        .slot()
                        .is_some_and(|s| s.owner() == owner && s.role() == role)
                    && fact.expectations() == Some([expected].as_slice())),
            "{source:?}: {facts:?}"
        );
    }
}

#[test]
fn cursor_positions_and_utf8_boundaries() {
    for source in ["", "  ", "x. ", "\"hello\"", "α β"] {
        let root = parse_root(source);
        assert_eq!(root.to_string(), source);
        for offset in 0..=source.len() {
            assert_eq!(
                cursor_context(&root, offset).is_some(),
                source.is_char_boundary(offset)
            );
        }
        assert!(cursor_context(&root, source.len() + 1).is_none());
    }
    let whitespace = parse_root("  ");
    let ctx = cursor_context(&whitespace, 1).unwrap();
    assert_eq!(ctx.left.unwrap().text(), "  ");
    assert_eq!(ctx.right.unwrap().text(), "  ");
    let empty = parse_root("");
    let ctx = cursor_context(&empty, 0).unwrap();
    assert_eq!(ctx.node.kind(), SyntaxKind::Root);
    assert!(ctx.left.is_none() && ctx.right.is_none());
    let root = parse_root("x.");
    let ctx = cursor_context(&root, 2).unwrap();
    assert_eq!(ctx.node.kind(), SyntaxKind::Missing);
    assert_eq!(ctx.expected, Some(ExpectedSyntax::Identifier));
    assert_eq!(ctx.left.unwrap().text(), ".");
    assert!(ctx.right.is_none());
    let root = parse_root("α β");
    let ctx = cursor_context(&root, 2).unwrap();
    assert_eq!(ctx.left.unwrap().text(), "α");
    assert_eq!(ctx.right.unwrap().text(), " ");
    let root = parse_root("\"hello\"");
    let ctx = cursor_context(&root, 3).unwrap();
    assert_eq!(ctx.left.unwrap().text(), "hello");
    assert_eq!(ctx.right.unwrap().text(), "hello");
}

#[test]
fn eof_ambiguous_text_current_recovery_is_pinned() {
    for source in ["---", "1 +"] {
        let root = parse_root(source);
        assert_eq!(root.to_string(), source);
        let facts = crate::structural_diagnostic::collect(&root);
        let start = if source == "---" { 0 } else { 2 };
        assert!(
            facts
                .iter()
                .any(|f| f.range() == &(start..source.len()) && f.identity().slot().is_none()),
            "{source:?}: {facts:?}"
        );
    }
}

#[test]
fn partial_sigils_retain_error_text_at_eof_and_line_end() {
    for prefix in ["my '", "type T = '", "$", "&"] {
        for suffix in ["", "\n"] {
            let source = format!("{prefix}{suffix}");
            let root = parse_root(&source);
            assert_eq!(root.to_string(), source);
            let marker = prefix.len() - 1;
            let facts = crate::structural_diagnostic::collect(&root);
            assert!(
                facts
                    .iter()
                    .any(|f| f.range().start <= marker && f.range().end > marker),
                "{source:?}: {facts:?}"
            );
        }
    }
}

#[test]
fn arm_and_interpolation_intermediate_slots() {
    for (source, at, owner, role, expected) in [
        (
            "case x:\n",
            7,
            SyntaxKind::CaseArm,
            GrammarSlotRole::Head,
            ExpectedSyntax::Pattern,
        ),
        (
            "case x: a",
            9,
            SyntaxKind::CaseArm,
            GrammarSlotRole::BodyIntroducer,
            ExpectedSyntax::Arrow,
        ),
        (
            "case x: a ->",
            12,
            SyntaxKind::CaseArm,
            GrammarSlotRole::Body,
            ExpectedSyntax::Expression,
        ),
        (
            "catch e: op,",
            12,
            SyntaxKind::Pattern,
            GrammarSlotRole::Head,
            ExpectedSyntax::Pattern,
        ),
        (
            "catch e: op, k ->",
            17,
            SyntaxKind::CatchArm,
            GrammarSlotRole::Body,
            ExpectedSyntax::Expression,
        ),
        (
            "\"%",
            2,
            SyntaxKind::StringInterpolation,
            GrammarSlotRole::BodyIntroducer,
            ExpectedSyntax::OpeningBrace,
        ),
        (
            "\"%{",
            3,
            SyntaxKind::StringInterpolationBody,
            GrammarSlotRole::ExpressionBody,
            ExpectedSyntax::Statement,
        ),
        (
            "\"%{x",
            4,
            SyntaxKind::StringInterpolation,
            GrammarSlotRole::Close,
            ExpectedSyntax::ClosingBrace,
        ),
        (
            "\"%{my ",
            6,
            SyntaxKind::Pattern,
            GrammarSlotRole::Head,
            ExpectedSyntax::Pattern,
        ),
    ] {
        let root = parse_root(source);
        assert_eq!(root.to_string(), source);
        let context = cursor_context(&root, at).unwrap();
        assert!(
            context.slots.iter().any(|s| s.range == (at..at)
                && s.slot.owner() == owner
                && s.slot.role() == role
                && s.expected == expected),
            "{source:?}: {context:#?}"
        );
    }
}

#[test]
fn coincident_slots_are_all_returned_in_stable_order() {
    let root = parse_root("\"%{");
    let slots = cursor_context(&root, 3).unwrap().slots;
    assert_eq!(
        slots
            .iter()
            .map(|s| (s.slot.owner(), s.expected))
            .collect::<Vec<_>>(),
        [
            (
                SyntaxKind::StringInterpolation,
                ExpectedSyntax::ClosingBrace
            ),
            (SyntaxKind::StringLiteral, ExpectedSyntax::Terminator),
            (
                SyntaxKind::StringInterpolationBody,
                ExpectedSyntax::Statement
            ),
        ]
    );
    let root = parse_root("\"%{my ");
    let slots = cursor_context(&root, 6).unwrap().slots;
    assert_eq!(
        slots
            .iter()
            .map(|s| (s.slot.owner(), s.expected))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Pattern, ExpectedSyntax::Pattern),
            (
                SyntaxKind::StringInterpolation,
                ExpectedSyntax::ClosingBrace
            ),
            (SyntaxKind::StringLiteral, ExpectedSyntax::Terminator),
        ]
    );
    assert!(
        cursor_context(&parse_root("\"%{}\""), 3)
            .unwrap()
            .slots
            .is_empty()
    );
}

#[test]
fn sigils_derive_context_from_error_tokens_without_reparsing() {
    for (prefix, sigil, kind) in [
        ("my '", Sigil::Apostrophe, SigilContext::BindingPattern),
        (
            "type T = '",
            Sigil::Apostrophe,
            SigilContext::TypeRightHandSide,
        ),
        ("$", Sigil::Dollar, SigilContext::Unknown),
        ("&", Sigil::Ampersand, SigilContext::Unknown),
    ] {
        for suffix in ["", "  next", "\nmy next = 0"] {
            let source = format!("{prefix}{suffix}");
            let root = parse_root(&source);
            assert_eq!(root.to_string(), source);
            let partial = cursor_context(&root, prefix.len())
                .unwrap()
                .partial_sigil
                .unwrap();
            assert_eq!(
                (partial.sigil, partial.context, partial.range),
                (sigil, kind, prefix.len() - 1..prefix.len()),
                "{source:?}"
            );
        }
    }
    assert!(
        cursor_context(&parse_root("abc"), 3)
            .unwrap()
            .partial_sigil
            .is_none()
    );
}

#[allow(dead_code)]
#[path = "../../examples/support/nesting_cases.rs"]
mod nesting_cases;

#[test]
fn deep_cursor_context_worker() {
    if std::env::var_os("YULANG_T19_CURSOR_CHILD").is_none() {
        return;
    }
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let source = "(".repeat(4096);
            let root = parse_root(&source);
            assert!(cursor_context(&root, source.len()).is_some());
            for &kind in nesting_cases::KINDS {
                let source = nesting_cases::source(kind, 1024, false);
                let parsed = nesting_cases::parse(&source);
                let root = parsed.source_root();
                for offset in [0, source.len() / 2, source.len()] {
                    if source.is_char_boundary(offset) {
                        assert!(
                            cursor_context(root.syntax(), offset).is_some(),
                            "{kind} at {offset}"
                        );
                    }
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn deep_cursor_context_is_bounded_and_stack_safe() {
    use std::time::{Duration, Instant};
    let mut child = std::process::Command::new(std::env::current_exe().unwrap())
        .args([
            "--exact",
            "tests::completion_context::deep_cursor_context_worker",
        ])
        .env("YULANG_T19_CURSOR_CHILD", "1")
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(status.success(), "cursor child: {status}");
            break;
        }
        if Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("cursor child exceeded 60 seconds");
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}
