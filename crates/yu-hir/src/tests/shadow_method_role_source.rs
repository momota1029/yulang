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
