use super::*;
use crate::shadow::{lower_module_with_local_source, LocalSourceForm, SourceAnnotationValue};

#[test]
fn primitive_formals_retain_actual_identifier_and_annotation_nodes() {
    let text = "my choose (x:int) (y:()) = { my local (z:int) = z; x }";
    let parsed = parsed(text);
    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("formal-annotations", "source.yu"))),
        &parsed, SemanticImports::empty()).unwrap();
    let HirItem::Binding(binding) = &hir.items()[0] else { panic!("binding") };
    let source = hir.local_source(binding.definition_root()).unwrap().unwrap();
    let keys = crate::shadow::source_keys(&parsed);
    let mut parameters = Vec::new();
    for expression in source.expressions() {
        if let LocalSourceForm::Lambda { parameter, .. } = &expression.form {
            let annotation = parameter.annotation.as_ref().unwrap();
            assert_eq!(&annotation.owner, binding.definition_root());
            assert_ne!(parameter.source, annotation.position);
            let identifier = keys.iter().find(|(_, key)| **key == parameter.source).unwrap().0;
            assert_eq!(identifier.kind(), SyntaxKind::IdentifierPattern);
            assert_eq!(identifier.to_string(), parameter.spelling.as_ref());
            let node = keys.iter().find(|(_, key)| **key == annotation.position).unwrap().0;
            assert_eq!(node.kind(), SyntaxKind::PatternTypeAnnotation);
            let range = crate::range_of(node);
            assert_eq!(&text[range], if parameter.spelling.as_ref() == "y" { ":()" } else { ":int" });
            assert!(matches!(annotation.ty.value, SourceAnnotationValue::Int | SourceAnnotationValue::Unit));
            parameters.push(parameter);
        }
    }
    assert_eq!(parameters.len(), 3);
    assert_ne!(parameters[0].id, parameters[1].id);
    assert_ne!(parameters[1].id, parameters[2].id);
    for parameter in source.bindings()[0].parameters.iter() {
        assert!(parameters.iter().any(|p| p.id == parameter.id && p.annotation.as_ref().unwrap().position == parameter.annotation.as_ref().unwrap().position));
    }
}
