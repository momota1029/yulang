use super::*;
use crate::shadow::*;
use yu_syntax::SyntaxKind;

#[test]
fn associated_receivers_join_constructor_nodes_in_source_order_without_cloning() {
    let artifact = ShadowArtifact::from_parsed(parsed("my f x = x.first.second")).unwrap();
    let fields = artifact.pending_field_tail_sources().unwrap();
    assert_eq!(fields.len(), 2);

    let mut observed = Vec::new();
    artifact
        .visit_associated_member_receivers(|field, receiver| {
            let member = artifact.position(field.member()).unwrap();
            let spelling = &artifact.source()[member.range().clone()];
            let kind = match receiver {
                HirExpr::Value { kind, .. } | HirExpr::Error { kind, .. } => *kind,
                HirExpr::Apply { .. } => SyntaxKind::OperatorChain,
            };
            observed.push((spelling.to_owned(), kind));
        })
        .unwrap();

    assert_eq!(observed.len(), 2);
    assert_eq!(observed[0].0, "first");
    assert_eq!(observed[0].1, SyntaxKind::IdentifierExpression);
    assert_eq!(observed[1].0, "second");
    assert_eq!(observed[1].1, SyntaxKind::FieldTail);
}

#[test]
fn role_and_impl_nodes_resolve_to_their_exact_same_parse_occurrences() {
    let artifact = ShadowArtifact::from_parsed(parsed(
        "role R: my member x = x\nrole R: my member y = y\nimpl T: D: my member z = z",
    ))
    .unwrap();
    let declarations = artifact.pending_role_impl_sources();
    assert_eq!(declarations.len(), 3);

    let mut seen = Vec::new();
    artifact
        .visit_role_impl_nodes(|declaration, node| {
            assert_eq!(node.kind(), declaration.kind());
            assert_eq!(
                artifact.position(declaration.position()).unwrap().range(),
                &range_of(node),
            );
            seen.push((declaration.kind(), node.text().to_string()));
        })
        .unwrap();

    assert_eq!(seen.len(), 3);
    assert_eq!(seen[0].0, SyntaxKind::RoleDeclaration);
    assert!(seen[0].1.starts_with("role R"));
    assert_eq!(seen[1].0, SyntaxKind::RoleDeclaration);
    assert!(seen[1].1.starts_with("role R"));
    assert_eq!(seen[2].0, SyntaxKind::ImplDeclaration);
    assert!(seen[2].1.starts_with("impl T"));
    assert_ne!(declarations[0].position(), declarations[1].position());
}

#[test]
fn operator_receiver_comes_from_association_child_zero() {
    let artifact = ShadowArtifact::from_parsed(parsed(
        "infix (<+>) 40 41 = left\nmy f a b = a <+> b.field",
    ))
    .unwrap();
    let mut receivers = Vec::new();
    artifact
        .visit_associated_member_receivers(|_, receiver| {
            receivers.push(receiver.range().clone());
        })
        .unwrap();

    assert_eq!(receivers.len(), 1);
    assert_eq!(&artifact.source()[receivers[0].clone()], "b");
}
