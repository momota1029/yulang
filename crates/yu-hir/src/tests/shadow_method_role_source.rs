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

#[test]
fn exact_role_impl_member_source_reaches_original_occurrences() {
    let source = "role SecondInt {\n    my second: int -> int -> int\n}\nimpl int: SecondInt {\n    my second self selected = selected\n}\nmy answer = SecondInt::second 1 2";
    assert_eq!(source.len(), 148);
    assert!(!source.ends_with('\n'));

    let parsed_file = parsed(source);
    let artifact = ShadowArtifact::from_parsed(parsed_file).unwrap();
    assert_eq!(artifact.source(), source);
    let keys = source_keys(artifact.parsed());
    let source_node = |kind: SyntaxKind, range: std::ops::Range<usize>| {
        let matches = keys
            .iter()
            .filter(|(node, _)| {
                let text_range = node.text_range();
                node.kind() == kind
                    && usize::from(text_range.start()) == range.start
                    && usize::from(text_range.end()) == range.end
            })
            .map(|(node, key)| (node.clone(), key.clone()))
            .collect::<Vec<_>>();
        assert_eq!(matches.len(), 1, "{kind:?} at {range:?}");
        matches.into_iter().next().unwrap()
    };

    let (member, member_key) = source_node(SyntaxKind::BindingStatement, 78..112);
    let (impl_node, impl_key) = source_node(SyntaxKind::ImplDeclaration, 52..114);
    let (header, header_key) = source_node(SyntaxKind::BindingHeader, 78..103);
    let (target, target_key) = source_node(SyntaxKind::Pattern, 81..101);
    let (head, head_key) = source_node(SyntaxKind::IdentifierPattern, 81..87);
    let (self_tail, self_tail_key) =
        source_node(SyntaxKind::PatternMlApplicationTail, 88..92);
    let (self_pattern, self_pattern_key) = source_node(SyntaxKind::Pattern, 88..92);
    let (self_id, self_id_key) = source_node(SyntaxKind::IdentifierPattern, 88..92);
    let (selected_tail, selected_tail_key) =
        source_node(SyntaxKind::PatternMlApplicationTail, 93..101);
    let (selected_pattern, selected_pattern_key) =
        source_node(SyntaxKind::Pattern, 93..101);
    let (formal_selected, formal_selected_key) =
        source_node(SyntaxKind::IdentifierPattern, 93..101);
    let (body, body_key) = source_node(SyntaxKind::BindingBody, 103..112);
    let (body_chain, body_chain_key) = source_node(SyntaxKind::OperatorChain, 104..112);
    let (body_selected, body_selected_key) =
        source_node(SyntaxKind::IdentifierExpression, 104..112);

    assert_eq!(member.parent().unwrap().kind(), SyntaxKind::Statement);
    assert_eq!(header.parent().as_ref(), Some(&member));
    assert_eq!(target.parent().as_ref(), Some(&header));
    assert_eq!(head.parent().as_ref(), Some(&target));
    assert_eq!(self_tail.parent().as_ref(), Some(&target));
    assert_eq!(selected_tail.parent().as_ref(), Some(&target));
    assert_eq!(self_pattern.parent().as_ref(), Some(&self_tail));
    assert_eq!(self_id.parent().as_ref(), Some(&self_pattern));
    assert_eq!(selected_pattern.parent().as_ref(), Some(&selected_tail));
    assert_eq!(formal_selected.parent().as_ref(), Some(&selected_pattern));
    assert_eq!(body.parent().as_ref(), Some(&member));
    assert_eq!(body_chain.parent().as_ref(), Some(&body));
    assert_eq!(body_selected.parent().as_ref(), Some(&body_chain));
    let mut ancestor = Some(member.clone());
    let mut member_reaches_impl = false;
    while let Some(node) = ancestor {
        let Some(key) = keys.get(&node) else {
            panic!("member ancestor must belong to the original parse");
        };
        assert!(artifact.parsed().owns_source_key(key));
        if key == &impl_key {
            assert_eq!(node, impl_node);
            member_reaches_impl = true;
            break;
        }
        ancestor = node.parent();
    }
    assert!(member_reaches_impl, "member must reach its implementation declaration");
    assert_eq!(
        target.children().map(|child| child.kind()).collect::<Vec<_>>(),
        vec![
            SyntaxKind::IdentifierPattern,
            SyntaxKind::PatternMlApplicationTail,
            SyntaxKind::PatternMlApplicationTail,
        ]
    );

    let pending_declarations = artifact.pending_role_impl_sources();
    assert_eq!(pending_declarations.len(), 2);
    artifact
        .with_associated_method_role_sources(|fields, declarations| {
            assert!(fields.is_empty());
            assert_eq!(declarations.len(), 2);
            for (index, (declaration, (expected_kind, expected_range))) in declarations
                .iter()
                .zip([
                    (SyntaxKind::RoleDeclaration, 0..51),
                    (SyntaxKind::ImplDeclaration, 52..114),
                ])
                .enumerate()
            {
                let retained = declaration.source();
                assert_eq!(retained.kind(), expected_kind);
                assert_eq!(declaration.node().kind(), expected_kind);
                assert_eq!(retained.position(), pending_declarations[index].position());
                let key = keys.get(declaration.node()).unwrap();
                assert!(artifact.parsed().owns_source_key(key));
                assert_eq!(
                    artifact.source_position(key).unwrap(),
                    retained.position().clone()
                );
                let position = artifact.position(retained.position()).unwrap();
                assert_eq!(position.kind(), expected_kind);
                assert_eq!(position.range(), &expected_range);
                let parent = position.parent().unwrap();
                assert_eq!(artifact.position(parent).unwrap().kind(), SyntaxKind::Root);
                assert_eq!(
                    declaration.node().parent().unwrap().kind(),
                    SyntaxKind::Root
                );
                if expected_kind == SyntaxKind::ImplDeclaration {
                    let associated_key = keys.get(declaration.node()).unwrap();
                    assert_eq!(associated_key, &impl_key);
                    assert_eq!(declaration.node(), &impl_node);
                    assert!(artifact.parsed().owns_source_key(associated_key));
                    assert!(member_reaches_impl);
                }
            }
        })
        .unwrap();

    fn assert_retained_subtree_matches_original(
        artifact: &ShadowArtifact,
        keys: &std::collections::HashMap<yu_syntax::SyntaxNode, yu_syntax::SourceNodeKey>,
        node: &yu_syntax::SyntaxNode,
        parent: Option<&crate::shadow::PositionId>,
        ordinal: usize,
    ) -> crate::shadow::PositionId {
        let key = keys.get(node).expect("original subtree node has a parse key");
        assert!(artifact.parsed().owns_source_key(key));
        let id = artifact.source_position(key).unwrap();
        let position = artifact.position(&id).unwrap();
        assert!(position.is_node());
        assert_eq!(position.kind(), node.kind());
        assert_eq!(
            position.range(),
            &(usize::from(node.text_range().start())..usize::from(node.text_range().end()))
        );
        assert_eq!(position.parent(), parent);
        assert_eq!(position.ordinal(), ordinal);

        let raw_children = node.children_with_tokens().collect::<Vec<_>>();
        let retained_children = position.children();
        assert_eq!(retained_children.len(), raw_children.len());
        for (child_ordinal, (raw_child, retained_id)) in
            raw_children.iter().zip(retained_children).enumerate()
        {
            let retained_child = artifact.position(retained_id).unwrap();
            assert_eq!(retained_child.parent(), Some(&id));
            assert_eq!(retained_child.ordinal(), child_ordinal);
            assert_eq!(retained_child.kind(), raw_child.kind());
            assert_eq!(
                retained_child.range(),
                &(usize::from(raw_child.text_range().start())
                    ..usize::from(raw_child.text_range().end()))
            );
            assert_eq!(retained_child.is_node(), raw_child.as_node().is_some());
            if let Some(child_node) = raw_child.as_node() {
                let child_id = assert_retained_subtree_matches_original(
                    artifact,
                    keys,
                    child_node,
                    Some(&id),
                    child_ordinal,
                );
                assert_eq!(&child_id, retained_id);
            }
        }
        id
    }

    let impl_parent = impl_node
        .parent()
        .expect("implementation declaration has original syntax parent");
    let impl_parent_key = keys
        .get(&impl_parent)
        .expect("implementation parent belongs to the original parse");
    assert!(artifact.parsed().owns_source_key(impl_parent_key));
    let retained_impl_parent = artifact.source_position(impl_parent_key).unwrap();
    let impl_ordinal = impl_parent
        .children_with_tokens()
        .position(|child| child.as_node() == Some(&impl_node))
        .expect("implementation declaration has an original raw child slot");
    assert_retained_subtree_matches_original(
        &artifact,
        &keys,
        &impl_node,
        Some(&retained_impl_parent),
        impl_ordinal,
    );

    for (node, key, kind, range, spelling) in [
        (&member, &member_key, SyntaxKind::BindingStatement, 78..112, "my second self selected = selected"),
        (&header, &header_key, SyntaxKind::BindingHeader, 78..103, "my second self selected ="),
        (&target, &target_key, SyntaxKind::Pattern, 81..101, "second self selected"),
        (&head, &head_key, SyntaxKind::IdentifierPattern, 81..87, "second"),
        (&self_tail, &self_tail_key, SyntaxKind::PatternMlApplicationTail, 88..92, "self"),
        (&self_pattern, &self_pattern_key, SyntaxKind::Pattern, 88..92, "self"),
        (&self_id, &self_id_key, SyntaxKind::IdentifierPattern, 88..92, "self"),
        (&selected_tail, &selected_tail_key, SyntaxKind::PatternMlApplicationTail, 93..101, "selected"),
        (&selected_pattern, &selected_pattern_key, SyntaxKind::Pattern, 93..101, "selected"),
        (&formal_selected, &formal_selected_key, SyntaxKind::IdentifierPattern, 93..101, "selected"),
        (&body, &body_key, SyntaxKind::BindingBody, 103..112, " selected"),
        (&body_chain, &body_chain_key, SyntaxKind::OperatorChain, 104..112, "selected"),
        (&body_selected, &body_selected_key, SyntaxKind::IdentifierExpression, 104..112, "selected"),
    ] {
        assert!(artifact.parsed().owns_source_key(key));
        assert_eq!(node.kind(), kind);
        assert_eq!(&artifact.source()[range.clone()], spelling);
        let retained = artifact.source_position(key).unwrap();
        let position = artifact.position(&retained).unwrap();
        assert_eq!(position.kind(), kind);
        assert_eq!(position.range(), &range);
    }

    let formal_position = artifact.source_position(&formal_selected_key).unwrap();
    let body_position = artifact.source_position(&body_selected_key).unwrap();
    assert_ne!(formal_selected, body_selected);
    assert_ne!(formal_selected_key, body_selected_key);
    assert_ne!(formal_position, body_position);
}
