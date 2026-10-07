#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_hir::{
    FileId, FileKey, HirItem, HirModule, ModuleIdentity, ResolvedExpr, SemanticImports,
    lower_module,
    shadow::{
        ResolvedCallInventoryError, ShadowArtifact, lower_module_with_shadow_applications,
        lower_module_with_shadow_local_binding,
    },
};
use yu_syntax::{ParsedFile, SourceText, SyntaxEnvironment, parse_file, scan_header};

fn parsed(source: &str) -> ParsedFile {
    let source: Arc<SourceText> = Arc::from(source);
    parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    )
}
fn identity() -> ModuleIdentity {
    ModuleIdentity::source_root(FileId::new(FileKey::new("test", "inventory.yu")))
}
fn binding(hir: &HirModule) -> &yu_hir::HirBinding {
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("binding")
    };
    binding
}
fn collect<'a>(expr: &'a ResolvedExpr, calls: &mut Vec<&'a ResolvedExpr>) {
    match expr {
        ResolvedExpr::Apply {
            callee, argument, ..
        } => {
            calls.push(expr);
            collect(callee, calls);
            collect(argument, calls);
        }
        ResolvedExpr::Lambda { body, .. } => collect(body, calls),
        ResolvedExpr::Group { inner, .. } => collect(inner, calls),
        _ => {}
    }
}
#[test]
fn direct_nested_and_left_associated_rows_borrow_existing_identities_in_source_order() {
    for (source, expected_count) in [
        ("my call f = f 1", 1),
        ("my call f = f(f 1)", 2),
        ("my call f = f 1 2", 2),
    ] {
        let parsed = parsed(source);
        let hir =
            lower_module_with_shadow_applications(identity(), &parsed, SemanticImports::empty())
                .unwrap();
        let root = binding(&hir).definition_root();
        let rows = hir.shadow_resolved_call_inventory(root).unwrap();
        let mut expected = Vec::new();
        collect(binding(&hir).value(), &mut expected);
        expected.sort_by_key(|expr| (expr.range().start, expr.range().end));
        assert_eq!(rows.len(), expected_count, "{source}");
        assert_eq!(rows.len(), expected.len());
        for (row, expr) in rows.iter().zip(expected) {
            let ResolvedExpr::Apply {
                occurrence,
                callee,
                argument,
                source_form,
                errors,
                ..
            } = expr
            else {
                unreachable!()
            };
            assert!(std::ptr::eq(row.occurrence, occurrence));
            assert!(std::ptr::eq(row.callee, callee.occurrence()));
            assert!(std::ptr::eq(row.argument, argument.occurrence()));
            assert_eq!(row.source_form, *source_form);
            assert!(std::ptr::eq(row.errors.as_ptr(), errors.as_ptr()));
            assert!(
                errors
                    .iter()
                    .any(|id| hir.errors().iter().any(|error| error.id() == *id
                        && error.kind() == yu_hir::HirErrorKind::UnsupportedExpression))
            );
        }
        let ordinary = lower_module(identity(), &parsed, SemanticImports::empty()).unwrap();
        let mut ordinary_calls = Vec::new();
        collect(binding(&ordinary).value(), &mut ordinary_calls);
        assert!(ordinary_calls.is_empty());
        assert_eq!(
            ordinary
                .shadow_resolved_call_inventory(binding(&ordinary).definition_root())
                .unwrap_err(),
            ResolvedCallInventoryError::UnsupportedProjection
        );
    }
}
#[test]
fn captured_local_initializer_is_owned_by_exact_root() {
    let parsed = parsed("my apply f = { my step x = f x; step }; my other g = g 2");
    let artifact = Arc::new(ShadowArtifact::from_parsed(parsed.clone()).unwrap());
    let hir = lower_module_with_shadow_local_binding(
        identity(),
        &parsed,
        SemanticImports::empty(),
        artifact,
    )
    .unwrap();
    let root = binding(&hir).definition_root();
    let rows = hir.shadow_resolved_call_inventory(root).unwrap();
    let local = hir.shadow_local_binding(root).unwrap().unwrap();
    let ResolvedExpr::Lambda { body, .. } = &local.initializer else {
        panic!("lambda")
    };
    assert_eq!(rows.len(), 1);
    assert!(std::ptr::eq(rows[0].occurrence, body.occurrence()));

    let HirItem::Binding(other) = &hir.items()[1] else {
        panic!("second top-level binding")
    };
    let other_rows = hir
        .shadow_resolved_call_inventory(other.definition_root())
        .unwrap();
    assert_eq!(other_rows.len(), 1);
    assert_ne!(rows[0].occurrence, other_rows[0].occurrence);
}
#[test]
fn foreign_artifact_root_is_rejected() {
    let parsed = parsed("my call f = f 1");
    let first =
        lower_module_with_shadow_applications(identity(), &parsed, SemanticImports::empty())
            .unwrap();
    let second =
        lower_module_with_shadow_applications(identity(), &parsed, SemanticImports::empty())
            .unwrap();
    assert_eq!(
        first
            .shadow_resolved_call_inventory(binding(&second).definition_root())
            .unwrap_err(),
        ResolvedCallInventoryError::ForeignRoot
    );
}
