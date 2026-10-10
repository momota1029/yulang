use super::*;
use crate::shadow::{LocalSourceForm, SourceAnnotationValue, lower_module_with_local_source};

#[test]
fn primitive_formals_retain_actual_identifier_and_annotation_nodes() {
    let text = "my choose (x:int) (y:()) = { my local (z:int) = z; x }";
    let parsed = parsed(text);
    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("formal-annotations", "source.yu"))),
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
    let mut parameters = Vec::new();
    for expression in source.expressions() {
        if let LocalSourceForm::Lambda { parameter, .. } = &expression.form {
            let annotation = parameter.annotation.as_ref().unwrap();
            assert_eq!(&annotation.owner, binding.definition_root());
            assert_ne!(parameter.source, annotation.position);
            let identifier = keys
                .iter()
                .find(|(_, key)| **key == parameter.source)
                .unwrap()
                .0;
            assert_eq!(identifier.kind(), SyntaxKind::IdentifierPattern);
            assert_eq!(identifier.to_string(), parameter.spelling.as_ref());
            let node = keys
                .iter()
                .find(|(_, key)| **key == annotation.position)
                .unwrap()
                .0;
            assert_eq!(node.kind(), SyntaxKind::PatternTypeAnnotation);
            let range = crate::range_of(node);
            assert_eq!(
                &text[range],
                if parameter.spelling.as_ref() == "y" {
                    ":()"
                } else {
                    ":int"
                }
            );
            assert!(matches!(
                annotation.ty.value,
                SourceAnnotationValue::Int | SourceAnnotationValue::Unit
            ));
            parameters.push(parameter);
        }
    }
    assert_eq!(parameters.len(), 3);
    assert_ne!(parameters[0].id, parameters[1].id);
    assert_ne!(parameters[1].id, parameters[2].id);
    for parameter in source.bindings()[0].parameters.iter() {
        assert!(parameters.iter().any(|p| p.id == parameter.id
            && p.annotation.as_ref().unwrap().position
                == parameter.annotation.as_ref().unwrap().position));
    }
}

#[test]
fn whole_local_primitives_retain_the_actual_annotation_owner_and_position() {
    let text = "my outer = { my local:int = 1; my unit:() = (); local }";
    let parsed = parsed(text);
    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("local-annotations", "source.yu"))),
        &parsed, SemanticImports::empty(),
    ).unwrap();
    let HirItem::Binding(binding) = &hir.items()[0] else { panic!("binding") };
    let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
    let keys = crate::shadow::source_keys(&parsed);
    assert_eq!(source.bindings().len(), 2);
    for local in source.bindings() {
        let annotation = local.annotation.as_ref().unwrap();
        assert_eq!(&annotation.owner, binding.definition_root());
        assert_ne!(annotation.position, local.binder_source);
        let node = keys.iter().find(|(_, key)| **key == annotation.position).unwrap().0;
        assert_eq!(node.kind(), SyntaxKind::PatternTypeAnnotation);
        assert_eq!(&text[crate::range_of(node)], if local.spelling.as_ref() == "local" { ":int" } else { ":()" });
        assert!(matches!(annotation.ty.value, SourceAnnotationValue::Int | SourceAnnotationValue::Unit));
    }
    assert_ne!(source.bindings()[0].annotation.as_ref().unwrap().position, source.bindings()[1].annotation.as_ref().unwrap().position);
}
