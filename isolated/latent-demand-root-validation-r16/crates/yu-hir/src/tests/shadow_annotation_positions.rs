//! Raw-CST consumer of the sole immutable shadow artifact.
use super::*;
use crate::shadow::*;

fn from_source(source: &str) -> Result<ShadowArtifact, ShadowError> {
    ShadowArtifact::from_parsed(parsed(source))
}

fn syntax_path(artifact: &ShadowArtifact, id: &PositionId) -> Vec<usize> {
    let mut path = Vec::new();
    let mut position = artifact.position(id).unwrap();
    while let Some(parent) = position.parent() {
        path.push(position.ordinal());
        position = artifact.position(parent).unwrap();
    }
    path.reverse();
    path
}

fn assert_whole_tree(artifact: &ShadowArtifact) {
    let root = SyntaxNode::new_root(artifact.parsed().green().clone());
    let mut nodes = vec![(artifact.root(), root, Vec::new(), None)];
    while let Some((id, raw, path, parent)) = nodes.pop() {
        let retained = artifact.position(&id).unwrap();
        assert_eq!(retained.kind(), raw.kind());
        assert!(retained.is_node());
        assert_eq!(*retained.range(), range_of(&raw));
        assert_eq!(syntax_path(artifact, &id), path);
        assert_eq!(retained.parent(), parent.as_ref());
        assert_eq!(
            &artifact.source()[retained.range().clone()],
            raw.to_string()
        );
        let children = raw.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(retained.children().len(), children.len());
        for (ordinal, (id_child, child)) in retained.children().iter().zip(children).enumerate() {
            let mut child_path = path.clone();
            child_path.push(ordinal);
            if let Some(node) = child.as_node() {
                nodes.push((id_child.clone(), node.clone(), child_path, Some(id.clone())));
            } else {
                let token = child.into_token().unwrap();
                let retained = artifact.position(id_child).unwrap();
                assert!(!retained.is_node());
                assert_eq!(retained.kind(), token.kind());
                assert_eq!(*retained.range(), range_of_token(&token));
                assert_eq!(syntax_path(artifact, id_child), child_path);
                assert_eq!(retained.parent(), Some(&id));
                assert_eq!(retained.ordinal(), ordinal);
                assert!(retained.children().is_empty());
                assert_eq!(&artifact.source()[retained.range().clone()], token.text());
            }
        }
    }
    assert_eq!(*artifact.positions()[0].range(), 0..artifact.source().len());
    let leaves = artifact
        .positions()
        .iter()
        .filter(|p| !p.is_node())
        .map(|p| &artifact.source()[p.range().clone()])
        .collect::<String>();
    assert_eq!(leaves, artifact.source());
}

#[test]
fn shadow_annotation_positions_preserves_whole_tree_and_distinct_row_owners() {
    let source = "my x: [e] F [io] -> U = f (g x)";
    assert!(parsed(source).syntax_diagnostics().unwrap().is_empty());
    let artifact = from_source(source).unwrap();
    assert_whole_tree(&artifact);
    assert_eq!(artifact.annotations().len(), 1);
    assert_eq!(
        artifact.annotations()[0].correspondence(),
        &Correspondence::PendingTypedPortAndProfile
    );
    let annotation = artifact
        .position(artifact.annotations()[0].position())
        .unwrap();
    assert_eq!(annotation.kind(), SyntaxKind::PatternTypeAnnotation);
    let rows = artifact
        .positions()
        .iter()
        .filter(|p| p.kind() == SyntaxKind::BracketRow)
        .collect::<Vec<_>>();
    assert_eq!(rows.len(), 2);
    assert_eq!(
        artifact.position(rows[0].parent().unwrap()).unwrap().kind(),
        SyntaxKind::TypeExpression
    );
    assert_eq!(
        artifact.position(rows[1].parent().unwrap()).unwrap().kind(),
        SyntaxKind::TypeArrowTail
    );
    assert_ne!(rows[0].parent(), rows[1].parent());
    let calls = artifact
        .positions()
        .iter()
        .filter(|p| p.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 2);
    assert_ne!(calls[0].range(), calls[1].range());
    assert!(artifact.skeleton().is_err());
}

#[test]
fn shadow_annotation_positions_brands_same_spelling_and_foreign_artifacts() {
    let source = "x as int; x as int";
    assert!(parsed(source).syntax_diagnostics().unwrap().is_empty());
    let first = from_source(source).unwrap();
    let second = from_source(source).unwrap();
    assert_whole_tree(&first);
    assert_eq!(first.annotations().len(), 2);
    assert_ne!(
        first.annotations()[0].position(),
        first.annotations()[1].position()
    );
    let repeated = first
        .positions()
        .iter()
        .filter(|p| !p.is_node() && &first.source()[p.range().clone()] == "int")
        .collect::<Vec<_>>();
    assert_eq!(repeated.len(), 2);
    assert_ne!(repeated[0].range(), repeated[1].range());
    assert_eq!(
        first
            .position(second.annotations()[0].position())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_ne!(
        first.annotations()[0].position(),
        second.annotations()[0].position()
    );
}

#[test]
fn shadow_annotation_positions_preserves_siblings_trivia_and_rejects_diagnostics() {
    let source = " \nmy x: T = value; my y: T = value\n ";
    assert!(parsed(source).syntax_diagnostics().unwrap().is_empty());
    let artifact = from_source(source).unwrap();
    assert_whole_tree(&artifact);
    assert_eq!(artifact.annotations().len(), 2);
    assert_eq!(
        artifact
            .positions()
            .iter()
            .filter(|p| p.kind() == SyntaxKind::BindingStatement)
            .count(),
        2
    );
    assert_eq!(
        from_source("my x: = value").unwrap_err(),
        ShadowError::MalformedSource
    );
}

#[test]
fn shadow_annotation_positions_keeps_utf8_trivia_in_byte_ranges() {
    let source = "// λ\nx as int";
    let artifact = from_source(source).unwrap();
    assert_whole_tree(&artifact);
    let lambda_start = source.find('λ').unwrap();
    let comment = artifact
        .positions()
        .iter()
        .find(|position| {
            !position.is_node() && &artifact.source()[position.range().clone()] == "// λ"
        })
        .unwrap();
    assert!(comment.range().start <= lambda_start);
    assert!(comment.range().end >= lambda_start + 'λ'.len_utf8());
    let token = artifact
        .positions()
        .iter()
        .find(|position| !position.is_node() && &artifact.source()[position.range().clone()] == "x")
        .unwrap();
    assert_eq!(token.range().start, source.find("x as").unwrap());
}

#[test]
fn shadow_annotation_positions_ids_preserve_each_retained_annotation_occurrence() {
    let source = "my x: T = value; my y: T = value; x as T; y as T";
    assert!(parsed(source).syntax_diagnostics().unwrap().is_empty());
    let artifact = from_source(source).unwrap();
    let retained = artifact
        .positions()
        .iter()
        .filter(|position| {
            matches!(
                position.kind(),
                SyntaxKind::PatternTypeAnnotation | SyntaxKind::TypeAnnotationTail
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(artifact.annotations().len(), 4);
    assert_eq!(artifact.annotations().len(), retained.len());
    for (index, (annotation, position)) in artifact.annotations().iter().zip(retained).enumerate() {
        let looked_up = artifact.annotation(annotation.id()).unwrap();
        assert_eq!(looked_up.id(), annotation.id());
        assert_eq!(looked_up.position(), annotation.position());
        assert!(std::ptr::eq(
            artifact.position(looked_up.position()).unwrap(),
            position
        ));
        assert_eq!(
            looked_up.correspondence(),
            &Correspondence::PendingTypedPortAndProfile
        );
        for previous in &artifact.annotations()[..index] {
            assert_ne!(previous.id(), annotation.id());
        }
    }
    let other = from_source(source).unwrap();
    assert_ne!(artifact.annotations()[0].id(), other.annotations()[0].id());
    assert_eq!(
        artifact
            .annotation(other.annotations()[0].id())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
}

#[test]
fn shadow_annotation_positions_associates_only_grouped_parameter_identifier() {
    let source = "my apply (f: T) x = f x";
    let artifact = from_source(source).unwrap();
    assert_whole_tree(&artifact);
    let skeleton = artifact.skeleton().unwrap();
    let [incidence] = skeleton.parameter_annotations() else {
        panic!("one grouped formal annotation")
    };
    assert_eq!(skeleton.binder(incidence.parameter()).unwrap().name(), "f");
    assert_eq!(incidence.annotation(), artifact.annotations()[0].id());
    let annotation = artifact.annotation(incidence.annotation()).unwrap();
    assert_eq!(
        annotation.correspondence(),
        &Correspondence::PendingTypedPortAndProfile
    );
    let binder = skeleton.binder(incidence.parameter()).unwrap();
    let binder_position = artifact.position(binder.position()).unwrap();
    let annotation_position = artifact.position(annotation.position()).unwrap();
    assert_eq!(
        annotation_position.kind(),
        SyntaxKind::PatternTypeAnnotation
    );
    assert_eq!(binder_position.parent(), annotation_position.parent());
    let inner = artifact
        .position(annotation_position.parent().unwrap())
        .unwrap();
    assert_eq!(inner.kind(), SyntaxKind::Pattern);
    assert_eq!(
        artifact.position(inner.parent().unwrap()).unwrap().kind(),
        SyntaxKind::ParenthesizedPattern
    );
    let root = SyntaxNode::new_root(artifact.parsed().green().clone());
    let mut exact = root;
    for ordinal in syntax_path(&artifact, annotation.position()) {
        exact = exact
            .children_with_tokens()
            .nth(ordinal)
            .unwrap()
            .into_node()
            .unwrap();
    }
    assert_eq!(exact.kind(), SyntaxKind::PatternTypeAnnotation);
    assert_eq!(exact.to_string(), ": T");
    assert_eq!(
        skeleton
            .binders()
            .iter()
            .map(Binder::name)
            .collect::<Vec<_>>(),
        ["f", "x"]
    );
    assert_eq!(
        skeleton
            .pending()
            .iter()
            .map(PendingPremise::premise)
            .collect::<Vec<_>>(),
        [
            Premise::CallableRole,
            Premise::FullFunctionMembership,
            Premise::CallViewRealization,
            Premise::QIndependentSourceCallViewFormation,
            Premise::SourceEventContributionAndTypedOutputObservation,
            Premise::JointArgumentTypingAndActualReturnedProviderCarrierCompatibility,
            Premise::SourceSignatureLocalImmediateCallEffectPositionFormation,
            Premise::OriginalTypedCallEffectOccurrenceIntroduction,
            Premise::SourceFormalUseRuleApplicabilityAndInterpretation,
            Premise::SourceDirectionalOutputEffectProtectionIntroduction
        ]
    );
    let other = from_source(source).unwrap();
    assert_eq!(
        other.annotation(incidence.annotation()).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        other.position(annotation.position()).unwrap_err(),
        ShadowError::ForeignArtifact
    );
    assert_eq!(
        other
            .skeleton()
            .unwrap()
            .binder(incidence.parameter())
            .unwrap_err(),
        ShadowError::ForeignArtifact
    );
}

#[test]
fn shadow_annotation_positions_does_not_misbind_ungrouped_or_expression_annotations() {
    for source in ["my apply f: T x = f x", "my apply f x = f x as T"] {
        let artifact = from_source(source).unwrap();
        assert_eq!(artifact.annotations().len(), 1);
        assert_eq!(
            artifact.annotations()[0].correspondence(),
            &Correspondence::PendingTypedPortAndProfile
        );
        assert!(artifact.skeleton().is_err());
        assert_whole_tree(&artifact);
    }
}

#[test]
fn shadow_annotation_positions_keeps_noninitial_grouped_parameters_distinct() {
    let artifact = from_source("my apply x (f: T) (g: T) = f (g x)").unwrap();
    let skeleton = artifact.skeleton().unwrap();
    let [f, g] = skeleton.parameter_annotations() else {
        panic!("two grouped formal annotations")
    };
    assert_eq!(skeleton.binder(f.parameter()).unwrap().name(), "f");
    assert_eq!(skeleton.binder(g.parameter()).unwrap().name(), "g");
    assert_ne!(f.parameter(), g.parameter());
    assert_eq!(f.annotation(), artifact.annotations()[0].id());
    assert_eq!(g.annotation(), artifact.annotations()[1].id());
    assert_ne!(f.annotation(), g.annotation());
    for incidence in [f, g] {
        let binder = skeleton.binder(incidence.parameter()).unwrap();
        let annotation = artifact.annotation(incidence.annotation()).unwrap();
        assert_eq!(
            artifact.position(binder.position()).unwrap().parent(),
            artifact.position(annotation.position()).unwrap().parent()
        );
        assert_eq!(
            annotation.correspondence(),
            &Correspondence::PendingTypedPortAndProfile
        );
    }
    assert_eq!(skeleton.binders()[0].name(), "x");
    assert!(
        skeleton
            .parameter_annotations()
            .iter()
            .all(|incidence| { skeleton.binder(incidence.parameter()).unwrap().name() != "x" })
    );
}
