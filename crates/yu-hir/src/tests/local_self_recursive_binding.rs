use super::*;
use crate::shadow::{LocalSourceForm, LocalSourceResolution, lower_module_with_local_source};

fn module(text: &str) -> HirModule {
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("local-self-recursion", "source.yu"))),
        &parsed(text), SemanticImports::empty(),
    ).unwrap()
}

#[test]
fn self_and_later_sibling_keep_the_same_local_identity() {
    let hir = module("my outer = { my loop x = loop x; my later = loop; later }");
    let HirItem::Binding(binding) = &hir.items()[0] else { panic!("binding"); };
    let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
    let local = &source.bindings()[0];
    let uses: Vec<_> = source.expressions().iter().filter_map(|expression| match &expression.form {
        LocalSourceForm::Name { spelling, resolution } if spelling.as_ref() == "loop" => Some(resolution),
        _ => None,
    }).collect();
    assert_eq!(uses.len(), 2);
    assert!(uses.iter().all(|resolution| matches!(resolution, LocalSourceResolution::Local(id) if id == &local.id)));
}

#[test]
fn parameter_shadows_self_and_local_self_shadows_outer_binding() {
    for text in [
        "my loop x = x; my outer = { my loop x = loop x; loop }",
        "my outer = { my loop loop = loop; loop }",
    ] {
        let hir = module(text);
        let HirItem::Binding(binding) = hir.items().last().unwrap() else { panic!("binding"); };
        let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
        let local = &source.bindings()[0];
        let uses: Vec<_> = source.expressions().iter().filter_map(|expression| match &expression.form {
            LocalSourceForm::Name { spelling, resolution } if spelling.as_ref() == "loop" => Some(resolution),
            _ => None,
        }).collect();
        assert_eq!(uses.len(), 2);
        assert_eq!(uses.iter().filter(|resolution| matches!(resolution, LocalSourceResolution::Local(id) if id == &local.id)).count(), if text.contains("loop loop") { 1 } else { 2 });
        if text.contains("loop loop") {
            assert!(uses.iter().any(|resolution| matches!(resolution, LocalSourceResolution::Parameter(id) if id == &local.parameters[0].id)));
        }
    }
}

#[test]
fn earlier_sibling_and_plain_value_self_initialization_remain_unresolved() {
    for text in [
        "my outer = { my earlier x = future x; my future x = x; future }",
        "my outer = { my value = value; value }",
    ] {
        let hir = module(text);
        let HirItem::Binding(binding) = &hir.items()[0] else { panic!("binding"); };
        let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
        assert!(source.expressions().iter().any(|expression| matches!(expression.form,
            LocalSourceForm::Name { resolution: LocalSourceResolution::Unresolved, .. })));
    }
}

#[test]
fn nested_helper_resolves_active_outer_self() {
    let hir = module("my outer = { my loop x = { my helper y = loop y; helper x }; loop }");
    let HirItem::Binding(binding) = &hir.items()[0] else { panic!("binding"); };
    let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
    let local = source.bindings().iter().find(|local| local.spelling.as_ref() == "loop").unwrap();
    let uses: Vec<_> = source.expressions().iter().filter_map(|expression| match &expression.form {
        LocalSourceForm::Name { spelling, resolution } if spelling.as_ref() == "loop" => Some(resolution),
        _ => None,
    }).collect();
    assert_eq!(uses.len(), 2);
    assert!(uses.iter().all(|resolution| matches!(resolution, LocalSourceResolution::Local(id) if id == &local.id)));
}
