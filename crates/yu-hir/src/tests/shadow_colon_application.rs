//! LocalSource formation only; no handler or typed Call judgment.
use super::*;
use crate::shadow::{LocalSourceForm, lower_module_with_local_source};

fn lower(text: &str) -> Result<HirModule, HirAvailabilityError> {
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("colon-application", "source.yu"))),
        &parsed(text),
        SemanticImports::empty(),
    )
}

#[test]
fn shadow_colon_application_retains_nested_ml_argument_and_source_identity() {
    let text = "my test run_io cb = run_io: cb 1";
    let parsed = parsed(text);
    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("colon-application", "source.yu"))),
        &parsed,
        SemanticImports::empty(),
    )
    .unwrap();
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("binding")
    };
    let source = hir
        .local_source(binding.definition_root())
        .unwrap()
        .unwrap();
    let keys = crate::shadow::source_keys(&parsed);
    let colon = source
        .expressions()
        .iter()
        .find(|expression| {
            matches!(
                expression.form,
                LocalSourceForm::Apply {
                    source_form: SyntaxKind::ColonApplicationTail,
                    ..
                }
            )
        })
        .unwrap();
    let LocalSourceForm::Apply {
        callee, argument, ..
    } = &colon.form
    else {
        unreachable!()
    };
    let target = source.expression(callee).unwrap();
    assert!(
        matches!(&target.form, LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "run_io")
    );
    assert_eq!(&text[target.range.clone()], "run_io");
    assert_eq!(&text[colon.range.clone()], ": cb 1");
    let nested = source.expression(argument).unwrap();
    let LocalSourceForm::Apply {
        callee,
        argument,
        source_form,
    } = &nested.form
    else {
        panic!("nested cb 1 application")
    };
    assert_eq!(*source_form, SyntaxKind::MlArgument);
    assert!(
        matches!(&source.expression(callee).unwrap().form, LocalSourceForm::Name { spelling, .. } if spelling.as_ref() == "cb")
    );
    assert!(
        matches!(&source.expression(argument).unwrap().form, LocalSourceForm::Integer(spelling) if spelling.as_ref() == "1")
    );
    assert_eq!(&text[nested.range.clone()], "1");
    assert_eq!(
        source
            .expressions()
            .iter()
            .filter(|expression| matches!(expression.form, LocalSourceForm::Apply { .. }))
            .count(),
        2
    );
    for (expression, kind) in [
        (colon, SyntaxKind::ColonApplicationTail),
        (nested, SyntaxKind::MlArgument),
    ] {
        let node = keys
            .iter()
            .find(|(_, key)| **key == expression.source)
            .unwrap()
            .0;
        assert_eq!(node.kind(), kind);
        assert_eq!(range_of(node), expression.range);
        assert!(hir.owns_occurrence(&expression.occurrence));
    }
    assert_ne!(colon.occurrence, nested.occurrence);
    assert_ne!(colon.source, nested.source);
}

#[test]
fn shadow_colon_application_preserves_ml_call_and_empty_call_tails() {
    for (text, kind, unit) in [
        ("my test f x = f x", SyntaxKind::MlArgument, false),
        ("my test f x = f(x)", SyntaxKind::CallTail, false),
        ("my test f = f()", SyntaxKind::CallTail, true),
    ] {
        let hir = lower(text).unwrap();
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let source = hir
            .local_source(binding.definition_root())
            .unwrap()
            .unwrap();
        let calls = source
            .expressions()
            .iter()
            .filter(|expression| matches!(expression.form, LocalSourceForm::Apply { .. }))
            .collect::<Vec<_>>();
        let [call] = calls.as_slice() else {
            panic!("one application")
        };
        let LocalSourceForm::Apply {
            argument,
            source_form,
            ..
        } = &call.form
        else {
            unreachable!()
        };
        assert_eq!(*source_form, kind);
        assert_eq!(
            matches!(
                source.expression(argument).unwrap().form,
                LocalSourceForm::Unit
            ),
            unit
        );
    }
}

#[test]
fn shadow_colon_application_recovery_and_indented_body_remain_unsupported() {
    for text in [
        "my test f = f:",
        "my test f x = f: , x",
        "my test f x = f:\n  x",
    ] {
        assert!(
            matches!(lower(text), Err(HirAvailabilityError::StructuralProjection)),
            "{text:?}"
        );
    }
}

#[test]
fn shadow_colon_application_multiple_direct_arguments_remain_unsupported() {
    // RootStatement owns this sequence: it is outside the one-argument tail.
    let parsed = parsed("my test f x = f: x, x");
    let root = SyntaxNode::new_root(parsed.green().clone());
    let tail = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .unwrap();
    let argument = crate::module::local_source::inline_colon_argument(&tail).unwrap();
    assert_eq!(tail.children().count(), 1);
    assert!(
        !tail
            .children_with_tokens()
            .any(|element| element.kind() == SyntaxKind::Comma)
    );
    // Construct a malformed colon-owned multiargument CST from the same parsed
    // argument. This directly exercises LocalSource's guard without assuming
    // outer sequence ownership or requiring a comma token in the parsed CST.
    let green = tail.green().into_owned();
    let length = green.children().count();
    let multiple = SyntaxNode::new_root(green.splice_children(
        0..length,
        [
            argument.green().into_owned().into(),
            argument.green().into_owned().into(),
        ],
    ));
    assert_eq!(multiple.children().count(), 2);
    assert!(matches!(
        crate::module::local_source::inline_colon_argument(&multiple),
        Err(HirAvailabilityError::StructuralProjection)
    ));
}

#[test]
fn shadow_colon_application_outer_sequences_keep_their_suffix() {
    for text in ["my test f x y = f: x, y", "my test f x y = (f: x, y)"] {
        let parsed = parsed(text);
        let root = SyntaxNode::new_root(parsed.green().clone());
        let tail = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .unwrap();
        let source = parsed.source();
        let tail_source = &source[tail.text_range()];
        assert_eq!(tail.children().count(), 1, "{text:?}");
        assert!(tail_source.starts_with(": x"), "{text:?}: {tail_source:?}");
        assert!(
            source[u32::from(tail.text_range().end()) as usize..].starts_with(", y"),
            "outer sequence begins after colon tail: {text:?}"
        );
        assert!(
            !tail
                .children_with_tokens()
                .any(|element| element.kind() == SyntaxKind::Comma),
            "{text:?}"
        );
        assert!(crate::module::local_source::inline_colon_argument(&tail).is_ok());
    }
    assert!(matches!(
        lower("my test f x y = (f: x, y)"),
        Err(HirAvailabilityError::StructuralProjection)
    ));
}
