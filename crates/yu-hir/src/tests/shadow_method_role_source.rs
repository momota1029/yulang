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

#[test]
fn qualified_member_head_routes_through_operation_namespace_without_target_join() {
    use crate::{FileId, FileKey, ModuleIdentity, SemanticImports};

    let source = "role SecondInt {\n    my second: int -> int -> int\n}\nimpl int: SecondInt {\n    my second self selected = selected\n}\nmy answer = SecondInt::second 1 2";
    assert_eq!(source.len(), 148);
    assert!(!source.ends_with('\n'));

    let parsed_file = parsed(source);
    let artifact = ShadowArtifact::from_parsed(parsed_file.clone()).unwrap();
    let keys = source_keys(&parsed_file);
    let source_node = |kind: SyntaxKind, predicate: &dyn Fn(&str) -> bool| {
        let matches = keys
            .iter()
            .filter(|(node, _)| {
                let range = node.text_range();
                node.kind() == kind
                    && predicate(
                        &source[usize::from(range.start())..usize::from(range.end())],
                    )
            })
            .map(|(node, key)| (node.clone(), key.clone()))
            .collect::<Vec<_>>();
        assert_eq!(matches.len(), 1, "expected one original {kind:?} source");
        matches.into_iter().next().unwrap()
    };

    let (_, answer_key) = source_node(SyntaxKind::BindingStatement, &|text| {
        text.starts_with("my answer")
    });
    let (path_tail, path_key) = source_node(SyntaxKind::PathTail, &|text| text.contains("::second"));
    assert_eq!(artifact.position(&artifact.source_position(&path_key).unwrap()).unwrap().kind(), SyntaxKind::PathTail);
    assert!(parsed_file.owns_source_key(&answer_key));
    assert!(parsed_file.owns_source_key(&path_key));

    let hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("test", "r128-role-impl.yu"))),
        &parsed_file,
        SemanticImports::empty(),
    )
    .unwrap();
    let answer = hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "answer" => Some(binding),
            _ => None,
        })
        .expect("the original answer binding is admitted as a HIR item");
    let root = SourceRootId::Definition(answer.definition_root().clone());
    assert!(hir.owns_source_root(&root));
    assert_eq!(hir.source_root_source_key(&root).unwrap(), Some(&answer_key));
    let local = hir
        .local_source_for(&root)
        .unwrap()
        .expect("answer's ordinary LocalSource carrier is available");
    assert_eq!(local.source_root(), &root);

    let outer = local.expression(local.body()).unwrap();
    let LocalSourceForm::Apply {
        callee: inner_index,
        argument: outer_argument_index,
        source_form: outer_form,
    } = &outer.form
    else {
        panic!("the second ordinary application edge is retained");
    };
    assert_eq!(*outer_form, SyntaxKind::MlArgument);
    let outer_argument = local.expression(outer_argument_index).unwrap();
    assert!(matches!(&outer_argument.form, LocalSourceForm::Integer(text) if text.as_ref() == "2"));
    let (outer_tail, outer_tail_key) = source_node(SyntaxKind::MlArgument, &|text| text.trim() == "2");
    assert_eq!(outer.source, outer_tail_key);
    assert_eq!(artifact.position(&artifact.source_position(&outer.source).unwrap()).unwrap().kind(), SyntaxKind::MlArgument);
    let (_, two_key) = source_node(SyntaxKind::IntegerLiteral, &|text| text == "2");
    assert_eq!(outer_argument.source, two_key);
    assert_eq!(artifact.position(&artifact.source_position(&outer_argument.source).unwrap()).unwrap().kind(), SyntaxKind::IntegerLiteral);
    assert!(parsed_file.owns_source_key(&outer_tail_key));
    assert_eq!(outer_tail.kind(), SyntaxKind::MlArgument);

    let inner = local.expression(inner_index).unwrap();
    let LocalSourceForm::Apply {
        callee: operation_index,
        argument: inner_argument_index,
        source_form: inner_form,
    } = &inner.form
    else {
        panic!("the first ordinary application edge is retained");
    };
    assert_eq!(*inner_form, SyntaxKind::MlArgument);
    let inner_argument = local.expression(inner_argument_index).unwrap();
    assert!(matches!(&inner_argument.form, LocalSourceForm::Integer(text) if text.as_ref() == "1"));
    let (_, inner_tail_key) = source_node(SyntaxKind::MlArgument, &|text| text.trim() == "1");
    assert_eq!(inner.source, inner_tail_key);
    assert_eq!(artifact.position(&artifact.source_position(&inner.source).unwrap()).unwrap().kind(), SyntaxKind::MlArgument);
    let (one, one_key) = source_node(SyntaxKind::IntegerLiteral, &|text| text == "1");
    assert_eq!(inner_argument.source, one_key);
    assert_eq!(artifact.source_position(&inner_argument.source).unwrap(), artifact.source_position(&one_key).unwrap());
    assert_eq!(artifact.position(&artifact.source_position(&inner_argument.source).unwrap()).unwrap().kind(), SyntaxKind::IntegerLiteral);
    assert!(parsed_file.owns_source_key(&inner_tail_key));
    assert_eq!(one.kind(), SyntaxKind::IntegerLiteral);

    let operation = local.expression(operation_index).unwrap();
    let LocalSourceForm::Operation { resolution } = &operation.form else {
        panic!("the qualified head is carried as a source operation");
    };
    assert!(matches!(resolution, SourceOperationResolution::Unresolved));
    assert_eq!(operation.source, path_key);
    assert_eq!(path_tail.kind(), SyntaxKind::PathTail);
    assert_eq!(artifact.position(&artifact.source_position(&operation.source).unwrap()).unwrap().kind(), SyntaxKind::PathTail);
    assert!(parsed_file.owns_source_key(&operation.source));

    let act_source = "act SecondInt:\n    our second: int -> int -> int\nmy answer = SecondInt::second 1 2";
    let act_parsed = parsed(act_source);
    let act_hir = lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("test", "r128-act.yu"))),
        &act_parsed,
        SemanticImports::empty(),
    )
    .unwrap();
    let act_answer = act_hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == "answer" => Some(binding),
            _ => None,
        })
        .expect("the independently parsed Act control retains its answer binding");
    let act_root = SourceRootId::Definition(act_answer.definition_root().clone());
    let act_local = act_hir.local_source_for(&act_root).unwrap().unwrap();
    let act_outer = act_local.expression(act_local.body()).unwrap();
    let LocalSourceForm::Apply { callee: act_inner_index, .. } = &act_outer.form else {
        panic!("Act control's second application edge remains structurally ordinary");
    };
    let act_inner = act_local.expression(act_inner_index).unwrap();
    let LocalSourceForm::Apply { callee: act_operation_index, .. } = &act_inner.form else {
        panic!("Act control's first application edge remains structurally ordinary");
    };
    let act_operation = act_local.expression(act_operation_index).unwrap();
    let LocalSourceForm::Operation { resolution: act_resolution } = &act_operation.form else {
        panic!("Act control's qualified head uses the operation carrier");
    };
    assert!(matches!(act_resolution, SourceOperationResolution::Resolved(_)));
    assert!(act_hir.owns_source_root(&act_root));
}

#[test]
fn member_annotations_stay_on_their_original_formal() {
    const SOURCES: [(&str, Option<&str>); 3] = [
        (
            "role SecondInt {\n    my second: int -> int -> int\n}\nimpl int: SecondInt {\n    my second self selected = selected\n}\nmy answer = SecondInt::second 1 2",
            None,
        ),
        (
            "role SecondInt {\n    my second: int -> int -> int\n}\nimpl int: SecondInt {\n    my second self (selected:int) = selected\n}\nmy answer = SecondInt::second 1 2",
            Some("int"),
        ),
        (
            "role SecondInt {\n    my second: int -> int -> int\n}\nimpl int: SecondInt {\n    my second self (selected:[] int) = selected\n}\nmy answer = SecondInt::second 1 2",
            Some("[] int"),
        ),
    ];

    for (source, expected_annotation) in SOURCES {
        assert!(!source.ends_with('\n'));
        let parsed_file = parsed(source);
        assert!(parsed_file.syntax_diagnostics().unwrap().is_empty(), "{source}");
        let artifact = ShadowArtifact::from_parsed(parsed_file).unwrap();
        assert_eq!(artifact.source(), source);
        let keys = source_keys(artifact.parsed());
        let range_of = |node: &yu_syntax::SyntaxNode| {
            usize::from(node.text_range().start())..usize::from(node.text_range().end())
        };
        let node_text = |node: &yu_syntax::SyntaxNode| {
            &source[range_of(node)]
        };
        let retained_position = |node: &yu_syntax::SyntaxNode| {
            let key = keys.get(node).expect("original syntax node has a source key");
            assert!(artifact.parsed().owns_source_key(key));
            let id = artifact.source_position(key).unwrap();
            let retained = artifact.position(&id).unwrap();
            assert_eq!(retained.kind(), node.kind());
            assert_eq!(retained.range(), &range_of(node));
            id
        };
        let retained_descends_from = |child: &PositionId, parent: &PositionId| {
            let mut ancestor = artifact.position(child).unwrap().parent().cloned();
            while let Some(position) = ancestor {
                if &position == parent {
                    return true;
                }
                ancestor = artifact.position(&position).unwrap().parent().cloned();
            }
            false
        };

        let member_matches = keys
            .keys()
            .filter(|node| {
                node.kind() == SyntaxKind::BindingStatement
                    && node_text(node).starts_with("my second self")
            })
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(member_matches.len(), 1);
        let member = &member_matches[0];
        let member_key = keys.get(member).unwrap();
        assert!(artifact.parsed().owns_source_key(member_key));
        let member_position = retained_position(member);

        let impl_matches = keys
            .keys()
            .filter(|node| {
                node.kind() == SyntaxKind::ImplDeclaration
                    && node_text(node).starts_with("impl int: SecondInt")
            })
            .cloned()
            .collect::<Vec<_>>();
        assert_eq!(impl_matches.len(), 1);
        let impl_node = &impl_matches[0];
        let impl_key = keys.get(impl_node).unwrap();
        assert!(artifact.parsed().owns_source_key(impl_key));

        let mut ancestor = Some(member.clone());
        let mut found_impl = false;
        while let Some(node) = ancestor {
            let key = keys.get(&node).expect("member ancestry remains in this parse");
            assert!(artifact.parsed().owns_source_key(key));
            if node == *impl_node {
                found_impl = true;
                break;
            }
            ancestor = node.parent();
        }
        assert!(found_impl, "member must descend from its original impl node");

        let header = member
            .children()
            .find(|node| node.kind() == SyntaxKind::BindingHeader)
            .expect("member retains its original BindingHeader");
        let target = header
            .children()
            .find(|node| node.kind() == SyntaxKind::Pattern)
            .expect("member header retains its target Pattern");
        let binders = target.children().collect::<Vec<_>>();
        assert_eq!(binders.len(), 3);
        let binder_positions = binders.iter().map(&retained_position).collect::<Vec<_>>();
        for binder in &binders {
            let binder_position = retained_position(binder);
            assert!(retained_descends_from(&binder_position, &member_position), "retained binder remains under its member");
        }
        let binder_names = binders
            .iter()
            .map(|binder| {
                let identifier = if binder.kind() == SyntaxKind::IdentifierPattern {
                    binder.clone()
                } else {
                    binder
                        .descendants()
                        .find(|node| node.kind() == SyntaxKind::IdentifierPattern)
                        .expect("application tail retains its original formal pattern")
                };
                let range = range_of(&identifier);
                assert!(keys.contains_key(&identifier));
                assert!(artifact
                    .parsed()
                    .owns_source_key(keys.get(&identifier).unwrap()));
                source[range].to_owned()
            })
            .collect::<Vec<_>>();
        assert_eq!(binder_names, ["second", "self", "selected"]);

        let annotation_count = |node: &yu_syntax::SyntaxNode| {
            node.descendants()
                .filter(|descendant| descendant.kind() == SyntaxKind::PatternTypeAnnotation)
                .count()
        };
        assert_eq!(annotation_count(&binders[0]), 0, "second has no own annotation");
        assert_eq!(annotation_count(&binders[1]), 0, "self has no own annotation");
        let selected_annotations = binders[2]
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .collect::<Vec<_>>();
        match expected_annotation {
            None => assert!(selected_annotations.is_empty()),
            Some(annotation_text) => {
                assert_eq!(selected_annotations.len(), 1);
                let annotation = &selected_annotations[0];
                let annotation_position = retained_position(annotation);
                assert!(retained_descends_from(&annotation_position, &binder_positions[2]), "annotation remains owned by selected formal");
                let range = range_of(annotation);
                assert!(keys.contains_key(annotation));
                assert!(artifact
                    .parsed()
                    .owns_source_key(keys.get(annotation).unwrap()));
                let actual = &source[range];
                assert!(actual.contains(annotation_text), "{actual}");
                let bracket_rows = annotation
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::BracketRow)
                    .collect::<Vec<_>>();
                if annotation_text == "[] int" {
                    assert_eq!(bracket_rows.len(), 1, "the empty outer row is syntax-owned here");
                    assert_eq!(node_text(&bracket_rows[0]), "[]");
                    let row_position = retained_position(&bracket_rows[0]);
                    assert!(retained_descends_from(&row_position, &annotation_position), "row remains under its annotation");
                } else {
                    assert!(bracket_rows.is_empty(), "ordinary int has no explicit row");
                }
                assert!(node_text(&binders[2]).contains("selected"));
            }
        }

        let body = member
            .children()
            .find(|node| node.kind() == SyntaxKind::BindingBody)
            .expect("member retains its original body");
        let body_position = retained_position(&body);
        assert!(retained_descends_from(&body_position, &member_position));
        let body_selected = body
            .descendants()
            .find(|node| {
                node.kind() == SyntaxKind::IdentifierExpression
                    && node_text(node) == "selected"
            })
            .expect("body occurrence remains distinct from the formal");
        let formal_selected = binders[2]
            .descendants()
            .find(|node| {
                node.kind() == SyntaxKind::IdentifierPattern
                    && node_text(node) == "selected"
            })
            .expect("selected formal is retained under the third binder");
        assert_ne!(formal_selected, body_selected);
        assert_ne!(range_of(&formal_selected), range_of(&body_selected));
        let formal_key = keys.get(&formal_selected).unwrap();
        let body_key = keys.get(&body_selected).unwrap();
        assert_ne!(formal_key, body_key);
        assert!(artifact.parsed().owns_source_key(formal_key));
        assert!(artifact.parsed().owns_source_key(body_key));
        let formal_position = retained_position(&formal_selected);
        let body_selected_position = retained_position(&body_selected);
        assert_ne!(formal_position, body_selected_position);
        assert!(retained_descends_from(&formal_position, &binder_positions[2]), "formal identifier remains under its binder");
        assert!(retained_descends_from(&body_selected_position, &body_position), "body occurrence remains under the body");

        let pending = artifact.pending_role_impl_sources();
        assert_eq!(pending.len(), 2);
        assert_eq!(pending[0].kind(), SyntaxKind::RoleDeclaration);
        assert_eq!(pending[1].kind(), SyntaxKind::ImplDeclaration);
        for declaration in &pending {
            let position = artifact.position(declaration.position()).unwrap();
            assert_eq!(position.kind(), declaration.kind());
            assert!(position.parent().is_some());
        }

        artifact
            .with_associated_method_role_sources(|fields, declarations| {
                assert!(fields.is_empty());
                assert_eq!(declarations.len(), 2);
                for (declaration, expected_kind) in declarations.iter().zip([
                    SyntaxKind::RoleDeclaration,
                    SyntaxKind::ImplDeclaration,
                ]) {
                    assert_eq!(declaration.node().kind(), expected_kind);
                    assert_eq!(declaration.source().kind(), expected_kind);
                    let key = keys.get(declaration.node()).unwrap();
                    assert!(artifact.parsed().owns_source_key(key));
                    assert_eq!(
                        artifact.source_position(key).unwrap(),
                        declaration.source().position().clone()
                    );
                }
                // These declaration APIs retain original Role/Impl nodes; the
                // binder order and selected's own annotation are read from the
                // member subtree above, not returned as declaration metadata.
            })
            .unwrap();
    }
}
