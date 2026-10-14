#![cfg(feature = "shadow")]
use std::sync::Arc;
use yu_hir::shadow::{LocalSource, LocalSourceForm, LocalSourceResolution, LocalSourceScope, LocalSourceCatchValuePattern, lower_module_with_local_source};
use yu_hir::{FileId, FileKey, HirAvailabilityError, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};
fn lower(text: &str) -> Result<HirModule, HirAvailabilityError> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("test", "catch.yu"))),
        &parsed,
        SemanticImports::empty(),
    )
}
fn sources(module: &HirModule) -> Vec<&LocalSource> {
    module
        .items()
        .iter()
        .filter_map(|item| {
            let HirItem::Binding(binding) = item else {
                return None;
            };
            module.local_source(binding.definition_root()).unwrap()
        })
        .collect()
}

#[test]
fn normal_arms_have_distinct_owned_binders_and_original_scrutinee() {
    let module = lower("my x = 1; my result = catch x { x -> x, x -> x, _ -> 2 }").unwrap();
    let source = sources(&module)[1];
    let expression = source.expression(source.body()).unwrap();
    let LocalSourceForm::Catch { scrutinee, arms } = &expression.form else { panic!("Catch"); };
    assert_eq!(arms.len(), 3);
    assert!(matches!(source.expression(scrutinee).unwrap().form, LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }), "scrutinee: {:?}", source.expression(scrutinee).unwrap());
    let mut ids = Vec::new();
    for arm in &arms[..2] {
        let LocalSourceCatchValuePattern::Binder(binder) = &arm.value_pattern else { panic!("binder"); };
        assert_eq!(binder.id.owner(), source.definition_root());
        assert_eq!(binder.id.arm_source(), &arm.source);
        let body = source.expression(&arm.body).unwrap();
        assert!(matches!(&body.form, LocalSourceForm::Name { resolution: LocalSourceResolution::CatchBinder(id), .. } if id == &binder.id));
        assert!(matches!(&body.scope, LocalSourceScope::CatchArm { catch, arm: position } if catch == source.body() && position == &arm.source));
        ids.push(binder.id.clone());
    }
    assert_ne!(ids[0], ids[1]);
    assert!(matches!(arms[2].value_pattern, LocalSourceCatchValuePattern::Wildcard));
    assert!(source.bindings().is_empty());
    assert!(source.expressions().iter().all(|expr| module.owns_occurrence(&expr.occurrence)));
}

#[test]
fn nested_shadowing_and_sibling_scopes_restore_outer_resolution() {
    let module = lower("my x = 1; my result = { my y = catch x { x -> catch x { x -> x }, _ -> x }; x }").unwrap();
    let source = sources(&module)[1];
    let catches: Vec<_> = source.expressions().iter().filter_map(|expr| match &expr.form {
        LocalSourceForm::Catch { arms, .. } => Some(arms), _ => None,
    }).collect();
    assert_eq!(catches.len(), 2);
    let LocalSourceCatchValuePattern::Binder(outer) = &catches[0][0].value_pattern else { panic!("outer binder"); };
    let LocalSourceCatchValuePattern::Binder(inner) = &catches[1][0].value_pattern else { panic!("inner binder"); };
    assert_ne!(outer.id, inner.id);
    assert!(matches!(source.expression(&catches[0][1].body).unwrap().form, LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }));
    let LocalSourceForm::Block { final_expression, .. } = &source.expression(source.body()).unwrap().form else { panic!("block"); };
    assert!(matches!(source.expression(final_expression).unwrap().form, LocalSourceForm::Name { resolution: LocalSourceResolution::ModuleDef(_), .. }));
}

#[test]
fn unfinished_handler_forms_are_private_unavailable() {
    for text in ["my result = catch 1 { 1 -> 2 }", "my result = catch 1 { x if true -> x }", "my result = catch 1 { op x, k -> x }"] {
        let formed = lower(text);
        assert!(formed.is_err() || sources(formed.as_ref().unwrap()).is_empty(), "{text}");
    }
}
