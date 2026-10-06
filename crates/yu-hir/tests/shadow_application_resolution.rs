#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_hir::{
    FileId, FileKey, HirErrorKind, HirItem, HirModule, ModuleIdentity, NameResolution,
    ResolvedExpr, SemanticImports, lower_module,
    shadow::{
        ShadowArtifact, SourceIdentityError, lower_module_with_shadow_applications,
        lower_module_with_source_identity,
    },
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, SyntaxKind, parse_file, scan_header};

fn parsed(source: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    parse_file(source, header, Arc::new(SyntaxEnvironment::empty()))
}

fn identity() -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new("test", "shadow-application.yu")))
}

fn value(module: &HirModule, index: usize) -> &ResolvedExpr {
    let expression = match &module.items()[index] {
        HirItem::Binding(binding) => binding.value(),
        HirItem::Expression(expression) => expression,
        _ => panic!("expression item"),
    };
    match expression {
        ResolvedExpr::Lambda { body, .. } => body,
        expression => expression,
    }
}

fn shadow(parsed: &ParsedFile) -> HirModule {
    lower_module_with_shadow_applications(identity(), parsed, SemanticImports::empty()).unwrap()
}

fn assert_normal_paths_unchanged(parsed: &ParsedFile, application_index: usize) {
    let ordinary = lower_module(identity(), parsed, SemanticImports::empty()).unwrap();
    let identity_only =
        lower_module_with_source_identity(identity(), parsed, SemanticImports::empty()).unwrap();
    assert_eq!(ordinary, identity_only);
    assert_eq!(ordinary.diagnostics(), identity_only.diagnostics());
    assert!(matches!(
        value(&ordinary, application_index),
        ResolvedExpr::Error { .. }
    ));
    assert!(
        ordinary
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.kind() == HirErrorKind::UnsupportedExpression)
    );
}

#[test]
fn leaf_applications_retain_distinct_occurrences_and_exact_source_nodes() {
    for (source, index, form, tail_range, callee_range, argument_range) in [
        (
            "my invoke f = f 1",
            0,
            SyntaxKind::MlArgument,
            16..17,
            14..15,
            16..17,
        ),
        (
            "my invoke x = x(x)",
            0,
            SyntaxKind::CallTail,
            15..18,
            14..15,
            16..17,
        ),
        (
            "my f = 1; f 1",
            1,
            SyntaxKind::MlArgument,
            12..13,
            10..11,
            12..13,
        ),
        (
            "my invoke x = 1 x",
            0,
            SyntaxKind::MlArgument,
            16..17,
            14..15,
            16..17,
        ),
    ] {
        let parsed = parsed(source);
        assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
        assert_normal_paths_unchanged(&parsed, index);
        let hir = shadow(&parsed);
        let artifact = ShadowArtifact::from_parsed(parsed).unwrap();
        let ResolvedExpr::Apply {
            occurrence,
            source_form,
            callee,
            argument,
            errors,
            ..
        } = value(&hir, index)
        else {
            panic!("one structural Apply: {source}")
        };
        assert_eq!(*source_form, form);
        assert_eq!(errors.len(), 1);
        assert_eq!(
            hir.errors()[errors[0].index() as usize].kind(),
            HirErrorKind::UnsupportedExpression
        );
        assert_ne!(occurrence, callee.occurrence());
        assert_ne!(occurrence, argument.occurrence());
        assert_ne!(callee.occurrence(), argument.occurrence());
        for (expression, kind, range) in [
            (value(&hir, index), form, tail_range),
            (
                callee.as_ref(),
                if source.contains("= 1 x") {
                    SyntaxKind::IntegerLiteral
                } else {
                    SyntaxKind::IdentifierExpression
                },
                callee_range,
            ),
            (
                argument.as_ref(),
                if form == SyntaxKind::CallTail || source.contains("= 1 x") {
                    SyntaxKind::IdentifierExpression
                } else {
                    SyntaxKind::IntegerLiteral
                },
                argument_range,
            ),
        ] {
            assert!(hir.owns_occurrence(expression.occurrence()));
            let position = artifact
                .occurrence_source_position(&hir, expression.occurrence())
                .unwrap();
            assert_eq!(artifact.position(&position).unwrap().kind(), kind);
            assert_eq!(*artifact.position(&position).unwrap().range(), range);
        }
        if let ResolvedExpr::Name { resolution, .. } = callee.as_ref() {
            assert!(matches!(
                resolution,
                NameResolution::Parameter(_) | NameResolution::Resolved(_)
            ));
        }
    }
}

#[test]
fn both_operand_resolution_errors_remain_explicit_and_scopes_do_not_escape() {
    let parsed = parsed("my invoke x = missing absent; x 1");
    assert_normal_paths_unchanged(&parsed, 0);
    let hir = shadow(&parsed);
    for index in [0, 1] {
        let ResolvedExpr::Apply { callee, errors, .. } = value(&hir, index) else {
            panic!("structural Apply")
        };
        assert!(matches!(
            callee.as_ref(),
            ResolvedExpr::Name {
                resolution: NameResolution::Unresolved,
                ..
            }
        ));
        assert_eq!(errors.len(), if index == 0 { 3 } else { 2 });
    }
    assert_eq!(
        hir.diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.kind() == HirErrorKind::UnresolvedName)
            .map(|diagnostic| diagnostic.range().clone())
            .collect::<Vec<_>>(),
        [14..21, 22..28, 30..31]
    );
}

#[test]
fn nested_argument_application_retains_each_call_and_operand_identity() {
    let parsed = parsed("my invoke f = f(f 1)");
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    assert_normal_paths_unchanged(&parsed, 0);
    let hir = shadow(&parsed);
    let artifact = ShadowArtifact::from_parsed(parsed).unwrap();
    let outer = value(&hir, 0);
    let ResolvedExpr::Apply {
        callee,
        argument,
        errors,
        ..
    } = outer
    else {
        panic!("outer structural application")
    };
    let ResolvedExpr::Apply {
        callee: inner_callee,
        argument: inner_argument,
        errors: inner_errors,
        ..
    } = argument.as_ref()
    else {
        panic!("nested structural application")
    };
    assert_eq!(errors.len(), 2);
    assert_eq!(inner_errors.len(), 1);
    for error in errors.iter().chain(inner_errors.iter()) {
        assert_eq!(
            hir.errors()[error.index() as usize].kind(),
            HirErrorKind::UnsupportedExpression
        );
    }
    let expressions = [
        outer,
        callee.as_ref(),
        argument.as_ref(),
        inner_callee.as_ref(),
        inner_argument.as_ref(),
    ];
    for (index, expression) in expressions.iter().enumerate() {
        assert!(hir.owns_occurrence(expression.occurrence()));
        for other in &expressions[..index] {
            assert_ne!(expression.occurrence(), other.occurrence());
        }
    }
    for (expression, kind, range) in [
        (outer, SyntaxKind::CallTail, 15..20),
        (callee.as_ref(), SyntaxKind::IdentifierExpression, 14..15),
        (argument.as_ref(), SyntaxKind::MlArgument, 18..19),
        (
            inner_callee.as_ref(),
            SyntaxKind::IdentifierExpression,
            16..17,
        ),
        (inner_argument.as_ref(), SyntaxKind::IntegerLiteral, 18..19),
    ] {
        let position = artifact
            .occurrence_source_position(&hir, expression.occurrence())
            .unwrap();
        assert_eq!(artifact.position(&position).unwrap().kind(), kind);
        assert_eq!(*artifact.position(&position).unwrap().range(), range);
    }
    let (
        ResolvedExpr::Name {
            resolution: outer_resolution,
            ..
        },
        ResolvedExpr::Name {
            resolution: inner_resolution,
            ..
        },
    ) = (callee.as_ref(), inner_callee.as_ref())
    else {
        panic!("resolved callee names")
    };
    assert!(matches!(outer_resolution, NameResolution::Parameter(_)));
    assert_eq!(outer_resolution, inner_resolution);
    assert_eq!(
        hir.diagnostics()
            .iter()
            .filter(|diagnostic| diagnostic.kind() == HirErrorKind::UnsupportedExpression)
            .count(),
        2
    );
}

#[test]
fn nested_callee_trivia_preserves_parameter_resolution() {
    for source in [
        "my invoke f = f( f 1)",
        "my invoke f = f( /* callee */ f 1)",
    ] {
        let parsed = parsed(source);
        assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
        assert_normal_paths_unchanged(&parsed, 0);
        let hir = shadow(&parsed);
        let ResolvedExpr::Apply {
            callee, argument, ..
        } = value(&hir, 0)
        else {
            panic!("outer structural application: {source}")
        };
        let ResolvedExpr::Apply {
            callee: inner_callee,
            ..
        } = argument.as_ref()
        else {
            panic!("nested structural application: {source}")
        };
        let (
            ResolvedExpr::Name {
                resolution: outer_resolution,
                ..
            },
            ResolvedExpr::Name {
                resolution: inner_resolution,
                ..
            },
        ) = (callee.as_ref(), inner_callee.as_ref())
        else {
            panic!("resolved callee names: {source}")
        };
        assert!(matches!(outer_resolution, NameResolution::Parameter(_)));
        assert_eq!(outer_resolution, inner_resolution, "{source}");
        assert_eq!(
            hir.diagnostics()
                .iter()
                .filter(|diagnostic| diagnostic.kind() == HirErrorKind::UnsupportedExpression)
                .count(),
            2,
            "{source}"
        );
        assert!(
            hir.diagnostics()
                .iter()
                .all(|diagnostic| diagnostic.kind() != HirErrorKind::UnresolvedName),
            "{source}"
        );
    }
}

#[test]
fn grouped_nested_argument_retains_exact_source_structure() {
    assert_grouped_nested_source_structure(
        "my invoke f = f (f 1)",
        21,
        SyntaxKind::MlArgument,
        19..20,
    );
    assert_grouped_nested_source_structure(
        "my invoke f = f (f(1,))",
        23,
        SyntaxKind::CallTail,
        18..22,
    );
}

fn assert_grouped_nested_source_structure(
    source: &str,
    group_end: usize,
    inner_kind: SyntaxKind,
    inner_range: std::ops::Range<usize>,
) {
    let parsed = parsed(source);
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    assert_normal_paths_unchanged(&parsed, 0);
    let hir = shadow(&parsed);
    let artifact = ShadowArtifact::from_parsed(parsed).unwrap();
    let outer = value(&hir, 0);
    let ResolvedExpr::Apply {
        callee,
        argument,
        errors,
        ..
    } = outer
    else {
        panic!("outer structural application");
    };
    let ResolvedExpr::Group { inner, .. } = argument.as_ref() else {
        panic!("one retained Group argument");
    };
    let ResolvedExpr::Apply {
        callee: inner_callee,
        errors: inner_errors,
        ..
    } = inner.as_ref()
    else {
        panic!("inner structural application");
    };
    assert_eq!(errors.len(), 2);
    assert_eq!(inner_errors.len(), 1);
    for error in errors {
        assert_eq!(
            hir.errors()[error.index() as usize].kind(),
            HirErrorKind::UnsupportedExpression
        );
    }
    for (expression, kind, range) in [
        (outer, SyntaxKind::MlArgument, 16..group_end),
        (
            argument.as_ref(),
            SyntaxKind::ParenthesizedExpression,
            16..group_end,
        ),
        (inner.as_ref(), inner_kind, inner_range),
        (callee.as_ref(), SyntaxKind::IdentifierExpression, 14..15),
        (
            inner_callee.as_ref(),
            SyntaxKind::IdentifierExpression,
            17..18,
        ),
    ] {
        let position = artifact
            .occurrence_source_position(&hir, expression.occurrence())
            .unwrap();
        assert_eq!(artifact.position(&position).unwrap().kind(), kind);
        assert_eq!(*artifact.position(&position).unwrap().range(), range);
    }
    let expressions = [
        outer,
        argument.as_ref(),
        inner.as_ref(),
        callee.as_ref(),
        inner_callee.as_ref(),
    ];
    for (index, expression) in expressions.iter().enumerate() {
        assert!(hir.owns_occurrence(expression.occurrence()));
        for other in &expressions[..index] {
            assert_ne!(expression.occurrence(), other.occurrence());
        }
    }
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("binding");
    };
    for expression in [callee.as_ref(), inner_callee.as_ref()] {
        let ResolvedExpr::Name {
            resolution: NameResolution::Parameter(parameter),
            ..
        } = expression
        else {
            panic!("callee resolves to formal parameter");
        };
        assert_eq!(parameter, binding.parameters()[0].id());
    }
}

#[test]
fn unsupported_applications_are_rejected_atomically() {
    for source in [
        "my invoke f = f 1 2",
        "my invoke f = (f) 1",
        "my invoke f = f (1)",
        "my invoke f = f(1, 2)",
        "my invoke f = f 1 as Int",
        "my invoke f = { f 1 }",
        "my invoke f = f[1] 2",
        "my invoke f = f(f(f 1))",
        "my invoke f = f (f (f 1))",
        "my invoke f = f (f 1, 2)",
        "my invoke f = f (f 1,)",
        "my invoke f = f(f 1 2)",
        "my invoke f = f((f) 1)",
        "my invoke f = f(f (1))",
        "my invoke f = f(f 1, 2)",
        "my invoke f = f(f 1 as Int)",
        "my invoke f = f({ f 1 })",
        "my invoke f = f(f[1] 2)",
    ] {
        let parsed = parsed(source);
        if source == "my invoke f = f (f 1,)" {
            assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        }
        let hir = shadow(&parsed);
        assert!(
            matches!(value(&hir, 0), ResolvedExpr::Error { .. }),
            "{source}"
        );
        let ResolvedExpr::Error { occurrence, .. } = value(&hir, 0) else {
            unreachable!("unsupported shape remains an Error")
        };
        let artifact = ShadowArtifact::from_parsed(parsed.clone()).unwrap();
        assert_eq!(
            artifact.occurrence_source_position(&hir, occurrence),
            Err(SourceIdentityError::MissingSource),
            "unsupported shapes publish no partial source identity: {source}"
        );
        let ordinary = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
        assert_eq!(hir, ordinary, "{source}");
        assert_eq!(hir.diagnostics(), ordinary.diagnostics(), "{source}");
    }
}

#[test]
fn malformed_grouped_application_does_not_publish_shadow_structure() {
    let parsed = parsed("my invoke f = f (f 1");
    assert!(!parsed.syntax_diagnostics().unwrap().is_empty());
    let ordinary = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
    let identity_only =
        lower_module_with_source_identity(identity(), &parsed, SemanticImports::empty()).unwrap();
    assert_eq!(ordinary, identity_only);
    assert!(matches!(value(&ordinary, 0), ResolvedExpr::Error { .. }));
    let shadow = shadow(&parsed);
    assert!(matches!(value(&shadow, 0), ResolvedExpr::Error { .. }));
    assert_eq!(shadow.diagnostics(), ordinary.diagnostics());
}
