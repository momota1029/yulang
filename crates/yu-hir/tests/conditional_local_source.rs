#![cfg(feature = "shadow")]

use std::collections::HashSet;
use std::sync::Arc;
use yu_hir::shadow::{
    LocalSource, LocalSourceForm, LocalSourceResolution, SourceAnnotationValue,
    lower_module_with_local_source,
};
use yu_hir::{
    FileId, FileKey, HirAvailabilityError, HirErrorKind, HirItem, HirModule, ModuleIdentity,
    SemanticImports,
};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn lower(text: &str) -> Result<HirModule, HirAvailabilityError> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("test", "conditional.yu"))),
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
fn ordered_arms_retain_every_condition_and_body_even_for_constants() {
    let text = "my value = if true: 1 elsif false: 2 else: \"str\"";
    let module = lower(text).unwrap();
    let source = sources(&module)[0];
    let expression = source.expression(source.body()).unwrap();
    let LocalSourceForm::If { arms, else_branch } = &expression.form else {
        panic!("conditional");
    };
    assert_eq!(arms.len(), 2);
    for ((condition, body), (boolean, integer)) in arms.iter().zip([(true, "1"), (false, "2")]) {
        assert!(
            matches!(source.expression(condition).unwrap().form, LocalSourceForm::Boolean(value) if value == boolean)
        );
        assert!(
            matches!(&source.expression(body).unwrap().form, LocalSourceForm::Integer(value) if value.as_ref() == integer)
        );
    }
    assert!(
        matches!(&source.expression(else_branch).unwrap().form, LocalSourceForm::String(value) if value.as_ref() == "\"str\"")
    );
    assert_eq!(source.expressions().len(), 6);
    let mut occurrences = HashSet::new();
    let mut positions = HashSet::new();
    for child in source.expressions() {
        assert!(module.owns_occurrence(&child.occurrence));
        assert!(occurrences.insert(child.occurrence.clone()));
        assert!(positions.insert(child.source.clone()));
        assert!(!text[child.range.clone()].is_empty());
    }
    assert!(
        !module
            .errors()
            .iter()
            .any(|error| error.kind() == HirErrorKind::UnresolvedName)
    );
}

#[test]
fn lexical_boolean_names_shadow_primitives_and_primitives_precede_module_names() {
    for name in ["true", "false"] {
        let module = lower(&format!("my value {name} = {name}")).unwrap();
        assert!(sources(&module)[0].expressions().iter().any(|expr| matches!(&expr.form,
            LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(_) } if spelling.as_ref() == name)));
        let module = lower(&format!("my value = {{ my {name} = 1; {name} }}")).unwrap();
        assert!(sources(&module)[0].expressions().iter().any(|expr| matches!(&expr.form,
            LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Local(_) } if spelling.as_ref() == name)));
        let module = lower(&format!("my {name} = 1\nmy value = {name}")).unwrap();
        let source = sources(&module)[1];
        assert!(
            matches!(source.expression(source.body()).unwrap().form, LocalSourceForm::Boolean(value) if value == (name == "true"))
        );
        assert!(
            !module
                .errors()
                .iter()
                .any(|error| error.kind() == HirErrorKind::UnresolvedName)
        );
    }
}

#[test]
fn sibling_branches_do_not_share_local_bindings() {
    let module = lower("my value = if true: ({ my true = 1; true }) else: ({true})").unwrap();
    let source = sources(&module)[0];
    assert_eq!(source.bindings().len(), 1);
    assert_eq!(
        source
            .expressions()
            .iter()
            .filter(|expr| matches!(
                &expr.form,
                LocalSourceForm::Name {
                    resolution: LocalSourceResolution::Local(_),
                    ..
                }
            ))
            .count(),
        1
    );
    assert_eq!(
        source
            .expressions()
            .iter()
            .filter(|expr| matches!(expr.form, LocalSourceForm::Boolean(true)))
            .count(),
        2
    );
}

#[test]
fn indented_arm_bodies_reuse_statement_block_projection() {
    let module = lower("my value = if true:\n    my x = 1\n    x\nelse:\n    \"str\"").unwrap();
    let source = sources(&module)[0];
    assert_eq!(source.bindings().len(), 1);
    assert_eq!(
        source
            .expressions()
            .iter()
            .filter(|expr| matches!(expr.form, LocalSourceForm::Block { .. }))
            .count(),
        2
    );
}

#[test]
fn missing_else_and_interpolated_strings_are_explicitly_unsupported() {
    for text in [
        "my value = if true: 1",
        "my value = \"%{unknown}\"",
        "my value = if true: 1 else: \"%{unknown}\"",
    ] {
        assert!(
            matches!(lower(text), Err(HirAvailabilityError::StructuralProjection)),
            "{text}"
        );
    }
}

#[test]
fn bool_and_str_annotations_work_standalone_and_in_arrow_heads() {
    for (text, boolean) in [
        ("my value: bool = true", true),
        ("my value: str = \"str\"", false),
    ] {
        let module = lower(text).unwrap();
        let annotation = sources(&module)[0].annotation().unwrap();
        assert!(if boolean {
            matches!(annotation.ty.value, SourceAnnotationValue::Bool)
        } else {
            matches!(annotation.ty.value, SourceAnnotationValue::Str)
        });
        assert!(annotation.ty.effects.is_none());
    }
    let module = lower("my value: bool -> str = 1").unwrap();
    let SourceAnnotationValue::Function { argument, result } =
        &sources(&module)[0].annotation().unwrap().ty.value
    else {
        panic!("function");
    };
    assert!(matches!(argument.value, SourceAnnotationValue::Bool));
    assert!(matches!(result.value, SourceAnnotationValue::Str));
    assert!(argument.effects.is_none() && result.effects.is_none());
}
