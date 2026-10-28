#![cfg(feature = "shadow")]

use std::sync::Arc;
use yu_hir::{FileId, FileKey, HirErrorKind, HirModule, HirVisibility, ModuleIdentity, SemanticImports};
use yu_hir::shadow::{lower_module_with_local_source, LocalSourceForm, SourceAnnotationValue, SourceOperationResolution};
use yu_syntax::{parse_file, scan_header, SourceText, SyntaxEnvironment};

fn lower(text: &str) -> Result<HirModule, yu_hir::HirAvailabilityError> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(source.clone(), Arc::new(scan_header(source)), Arc::new(SyntaxEnvironment::empty()));
    lower_module_with_local_source(ModuleIdentity::source_root(FileId::new(FileKey::new("test", "operation.yu"))), &parsed, SemanticImports::empty())
}
fn operation(module: &HirModule) -> &yu_hir::shadow::LocalSourceExpr {
    module.items().iter().filter_map(|item| match item {
        yu_hir::HirItem::Binding(binding) => Some(binding),
        _ => None,
    }).find_map(|binding| {
        let source = module.local_source(binding.definition_root()).unwrap()?;
        source.expressions().iter().find(|expr| matches!(expr.form, LocalSourceForm::Operation { .. }))
    }).unwrap()
}

#[test]
fn retains_actual_body_signature_and_path_use_provenance() {
    let module = lower("act tick:\n    our next: () -> int\nmy run = tick::next()").unwrap();
    let family = &module.source_effect_declarations()[0];
    let member = &family.operations[0];
    assert_eq!(member.id.family, family.id);
    assert_eq!(member.spelling.as_ref(), "next");
    assert_eq!(member.visibility, HirVisibility::Our);
    let SourceAnnotationValue::Function { argument, result } = &member.signature.value else { panic!("function signature"); };
    assert!(matches!(argument.value, SourceAnnotationValue::Unit));
    assert!(matches!(result.value, SourceAnnotationValue::Int));
    assert!(result.effects.is_none());
    let use_expr = operation(&module);
    assert_ne!(use_expr.source, member.id.declaration);
    assert_ne!(use_expr.source, member.signature_position);
    assert_eq!(use_expr.range, 47..53);
    let LocalSourceForm::Operation { resolution: SourceOperationResolution::Resolved(resolved) } = &use_expr.form else { panic!("resolved operation"); };
    assert!(Arc::ptr_eq(resolved, member));
}

#[test]
fn resolves_later_family_rows_without_mutating_original_signature() {
    let module = lower("act tick:\n    our next: () -> [later]int\nact later;\nmy run = tick::next").unwrap();
    let families = module.source_effect_declarations();
    let SourceAnnotationValue::Function { result, .. } = &families[0].operations[0].signature.value else { panic!("function"); };
    assert_eq!(result.effects.as_ref().unwrap().concrete, vec![families[1].id.clone()]);
}

#[test]
fn preserves_private_missing_and_duplicate_failures() {
    for (text, expected) in [
        ("my act tick:\n    my next: () -> int\nmy run = tick::next", "private"),
        ("act tick;\nmy run = tick::missing", "missing"),
        ("act tick:\n    our next: () -> int\n    pub next: () -> int\nmy run = tick::next", "duplicate"),
        ("act tick;\nact tick;\nmy run = tick::next", "duplicate"),
    ] {
        let module = lower(text).unwrap();
        let LocalSourceForm::Operation { resolution } = &operation(&module).form else { unreachable!(); };
        match expected {
            "private" => assert!(matches!(resolution, SourceOperationResolution::Private)),
            "missing" => assert!(matches!(resolution, SourceOperationResolution::Unresolved)),
            _ => {
                assert!(matches!(resolution, SourceOperationResolution::Ambiguous));
                let duplicates: Vec<_> = module.errors().iter().filter(|error| error.kind() == HirErrorKind::DuplicateDefinition).collect();
                assert!(!duplicates.is_empty());
                assert!(duplicates.iter().all(|error| module.source_effect_declarations().iter().all(|family| !family.placeholder_errors.contains(&error.id()))));
            }
        }
    }
    let module = lower("my act tick:\n    pub next: () -> int\nmy run = tick::next").unwrap();
    assert!(matches!(operation(&module).form, LocalSourceForm::Operation { resolution: SourceOperationResolution::Resolved(_) }));
}

#[test]
fn rejects_unsupported_body_members_and_preserves_unrelated_errors() {
    for text in [
        "act tick:\n    our next: int",
        "act tick:\n    our next: () -> int = 1",
        "act tick:\n    our next x: () -> int",
        "act tick 'a;",
        "act tick:\n    our next: () -> [unknown]int",
        "act tick:\n    our next: () -> ['a | 'b]int",
        "act tick:\n    our next: () -> int\nmy run = tick.next",
    ] { assert!(lower(text).is_err(), "{text}"); }
    let module = lower("act tick;\nmy value = missing").unwrap();
    assert!(module.errors().iter().any(|error| error.kind() == HirErrorKind::UnresolvedName));
}
