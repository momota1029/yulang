use super::*;
use crate::shadow::*;
use yu_syntax::SyntaxKind;

const SOURCE: &str = "my f x = x.field\nrole R: my member x = x\nimpl T: D: my member x = x";

#[test]
fn pending_method_and_role_impl_projection_preserves_parse_owned_structure() {
    let artifact = ShadowArtifact::from_parsed(parsed(SOURCE)).unwrap();
    let fields = artifact.pending_field_tail_sources().unwrap();
    assert_eq!(fields.len(), 1);
    let field = &fields[0];
    assert_eq!(
        artifact.position(field.tail()).unwrap().kind(),
        SyntaxKind::FieldTail
    );
    assert_eq!(
        artifact.position(field.expression()).unwrap().kind(),
        SyntaxKind::OperatorChain
    );
    let receiver_prefix = field.receiver_prefix(&artifact).unwrap();
    assert_eq!(
        artifact
            .position(receiver_prefix.last().unwrap())
            .unwrap()
            .kind(),
        SyntaxKind::IdentifierExpression
    );
    let member = artifact.position(field.member()).unwrap();
    assert_eq!(member.kind(), SyntaxKind::Identifier);
    assert_eq!(&artifact.source()[member.range().clone()], "field");
    assert_eq!(artifact.position(field.tail()).unwrap().range(), &(10..16));

    let declarations = artifact.pending_role_impl_sources();
    assert_eq!(declarations.len(), 2);
    assert_eq!(declarations[0].kind(), SyntaxKind::RoleDeclaration);
    assert_eq!(declarations[1].kind(), SyntaxKind::ImplDeclaration);
    for declaration in declarations {
        let position = artifact.position(declaration.position()).unwrap();
        assert_eq!(position.kind(), declaration.kind());
        let parent = position.parent().expect("declaration parent retained");
        assert!(artifact.position(parent).is_ok());
    }
}

#[test]
fn chained_field_tails_keep_the_entire_preceding_raw_receiver_prefix() {
    let artifact = ShadowArtifact::from_parsed(parsed("my f x = x.first.second")).unwrap();
    let fields = artifact.pending_field_tail_sources().unwrap();
    assert_eq!(fields.len(), 2);
    assert!(
        fields[0].receiver_prefix(&artifact).unwrap().len()
            < fields[1].receiver_prefix(&artifact).unwrap().len()
    );
    for field in fields {
        assert!(artifact.position(field.tail()).is_ok());
        assert!(artifact.position(field.expression()).is_ok());
        assert!(
            field
                .receiver_prefix(&artifact)
                .unwrap()
                .iter()
                .all(|position| artifact.position(position).is_ok())
        );
        assert!(artifact.position(field.member()).is_ok());
    }
}

#[test]
fn association_bridge_uses_constructor_owned_receiver_and_parse_owned_declarations() {
    let source = "my f x = x.first.second\nrole R: my member x = x\nrole R: my member y = y\nimpl T: D: my member x = x";
    let artifact = ShadowArtifact::from_parsed(parsed(source)).unwrap();
    let keys = source_keys(artifact.parsed());

    artifact.with_associated_method_role_sources(|fields, declarations| {
        assert_eq!(fields.len(), 2);
        assert_eq!(declarations.len(), 3);
        assert!(fields[0].source().tail() != fields[1].source().tail());
        assert!(
            artifact.position(fields[0].source().tail()).unwrap().range().start
                < artifact.position(fields[1].source().tail()).unwrap().range().start
        );

        let HirExpr::Value { kind: SyntaxKind::IdentifierExpression, range: first_range, .. } = fields[0].receiver() else {
            panic!("first FieldTail receiver must be its association-produced left child");
        };
        let HirExpr::Value { kind: SyntaxKind::FieldTail, range: second_range, .. } = fields[1].receiver() else {
            panic!("second FieldTail receiver must include the first associated tail");
        };
        let AssociationProvenance::Node { source: first_source, .. } = fields[0].receiver_provenance() else { unreachable!() };
        let AssociationProvenance::Node { source: second_source, .. } = fields[1].receiver_provenance() else { unreachable!() };
        assert_eq!(first_source.kind(), SyntaxKind::IdentifierExpression);
        assert_eq!(second_source.kind(), SyntaxKind::FieldTail);
        assert_eq!(first_range, &range_of(first_source));
        let second_source_range = range_of(second_source);
        assert_eq!(second_range.start, first_range.start);
        assert_eq!(second_range.end, second_source_range.end);
        let HirExpr::Value { children: second_children, .. } = fields[1].receiver() else { unreachable!() };
        assert!(std::ptr::eq(
            second_children.first().expect("continuation child zero"),
            fields[0].receiver(),
        ));
        let second_source_key = keys.get(second_source).unwrap();
        assert_eq!(
            artifact.source_position(second_source_key).unwrap(),
            fields[0].source().tail().clone(),
        );

        for (index, declaration) in declarations.iter().enumerate() {
            let retained = declaration.source();
            let key = keys.get(declaration.node()).unwrap();
            assert_eq!(artifact.source_position(key).unwrap(), retained.position().clone());
            assert_eq!(declaration.node().kind(), retained.kind());
            assert_eq!(retained.kind(), [SyntaxKind::RoleDeclaration, SyntaxKind::RoleDeclaration, SyntaxKind::ImplDeclaration][index]);
        }
    }).unwrap();
}
