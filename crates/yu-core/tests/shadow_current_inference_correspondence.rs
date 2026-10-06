#![cfg(feature = "shadow")]

//! Support-boundary characterization from one ParsedFile. Exact production
//! sidecar joins cover admitted definitions, parameters and leaves only.
//! Rejected applications have no production occurrence join, even when an Error
//! range overlaps shadow syntax. This establishes no type/scheme, callable-role,
//! effect, soundness, principality, source-adequacy or old-infer equivalence.

use std::sync::Arc;
use yu_core::shadow::{Form, ShadowArtifact};
use yu_core::shadow_derivation::{PendingStructuralProjection, RawStructuralArena};
use yu_hir::shadow::{SourceIdentityError, lower_module_with_source_identity};
use yu_hir::{
    FileId, FileKey, HirErrorKind, HirItem, HirModule, ModuleIdentity, NameResolution,
    ResolvedExpr, SemanticImports, lower_module,
};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

#[test]
fn common_leaves_join_actual_production_identities_to_shadow_positions() {
    for source in ["my identity x = x", "my constant x = 42"] {
        let (hir, shadow) = pair(source);
        assert!(hir.errors().is_empty());
        let [HirItem::Binding(binding)] = hir.items() else {
            panic!("admitted leaf definition");
        };
        let skeleton = shadow.skeleton().unwrap();
        let crosswalk = shadow.skeleton_source_crosswalk();
        let definition = shadow
            .definition_source_position(&hir, binding.definition_root())
            .unwrap();
        let (_, declaration) = crosswalk
            .definition_at_position(&definition)
            .unwrap()
            .unwrap();
        let declaration = skeleton.binder(declaration).unwrap();
        assert_eq!(declaration.name(), binding.name().spelling());
        assert_eq!(declaration.range(), binding.name().range());
        let [parameter] = binding.parameters() else {
            panic!("one admitted parameter");
        };
        let position = shadow
            .parameter_source_position(&hir, parameter.id())
            .unwrap();
        let (_, binder) = crosswalk.parameter_at_position(&position).unwrap().unwrap();
        let retained = skeleton.binder(binder).unwrap();
        assert_eq!(retained.position(), &position);
        assert_eq!(retained.name(), parameter.name().spelling());
        assert_eq!(retained.range(), parameter.name().range());
        let ResolvedExpr::Lambda {
            parameter: owner,
            body,
            ..
        } = binding.value()
        else {
            panic!("production unary lambda");
        };
        assert_eq!(owner, parameter.id());
        let position = shadow
            .occurrence_source_position(&hir, body.occurrence())
            .unwrap();
        let retained_body = skeleton.expression(skeleton.body()).unwrap();
        assert_eq!(&position, retained_body.position());
        assert_eq!(body.range(), retained_body.range());
        match (body.as_ref(), retained_body.form()) {
            (
                ResolvedExpr::Name {
                    name,
                    resolution: NameResolution::Parameter(id),
                    ..
                },
                Form::Use {
                    binder: used,
                    occurrence,
                },
            ) => {
                assert_eq!(id, parameter.id());
                assert_eq!(used, binder);
                assert_eq!(
                    crosswalk.use_at_position(&position).unwrap(),
                    Some(occurrence)
                );
                assert_eq!(name.spelling(), retained.name());
            }
            (
                ResolvedExpr::Integer { spelling, .. },
                Form::IntegerLiteral { spelling: retained },
            ) => {
                assert_eq!(spelling, retained);
                assert!(crosswalk.use_at_position(&position).unwrap().is_none());
            }
            _ => panic!("genuine common leaf subset"),
        }
        assert!(skeleton.pending().is_empty());
    }
}

#[test]
fn rejected_unary_applications_retain_separate_shadow_calls_and_pending_rows() {
    for (source, calls, uses, outer_direct) in [
        ("my call f = f 1", 1, 1, true),
        ("my twice f = f (f 1)", 2, 2, true),
        ("my grouped f = (f) 1", 1, 1, false),
        ("my computed f = (f 1) 2", 2, 1, false),
    ] {
        let (hir, shadow) = pair(source);
        let [HirItem::Binding(binding)] = hir.items() else {
            panic!("unary header remains admitted");
        };
        let [parameter] = binding.parameters() else {
            panic!("retained formal")
        };
        let ResolvedExpr::Lambda { body, .. } = binding.value() else {
            panic!("unary lambda")
        };
        assert!(matches!(body.as_ref(), ResolvedExpr::Error { .. }));
        assert!(
            hir.errors()
                .iter()
                .any(|error| error.kind() == HirErrorKind::UnsupportedExpression)
        );
        assert_eq!(
            shadow.occurrence_source_position(&hir, body.occurrence()),
            Err(SourceIdentityError::MissingSource)
        );
        let position = shadow
            .parameter_source_position(&hir, parameter.id())
            .unwrap();
        assert!(
            shadow
                .skeleton_source_crosswalk()
                .parameter_at_position(&position)
                .unwrap()
                .is_some()
        );
        check_shadow(&shadow, 1, calls, uses, outer_direct, 0);
    }
}

#[test]
fn two_formal_parser_candidates_are_not_production_supported_headers() {
    for (source, calls, uses, annotations) in [
        ("my apply f x = f x", 1, 2, 0),
        ("my apply f x = f (f x)", 2, 3, 0),
        ("my apply (f: T) (x: U) = f x", 1, 2, 2),
    ] {
        let (hir, shadow) = pair(source);
        assert!(matches!(hir.items(), [HirItem::Error { .. }]));
        assert!(
            hir.errors()
                .iter()
                .any(|error| error.kind() == HirErrorKind::UnsupportedTarget)
        );
        // There is no admitted definition/parameter/occurrence ID to join here.
        check_shadow(&shadow, 2, calls, uses, true, annotations);
    }
}

fn pair(source: &str) -> (HirModule, ShadowArtifact) {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    let hir = lower_module_with_source_identity(
        ModuleIdentity::source_root(FileId::new(FileKey::new(
            "current-inference-shadow",
            "candidate.yu",
        ))),
        &parsed,
        SemanticImports::empty(),
    )
    .unwrap();
    let ordinary = lower_module(hir.identity().clone(), &parsed, SemanticImports::empty()).unwrap();
    assert_eq!(hir, ordinary, "the opt-in sidecar preserves production HIR");
    (hir, ShadowArtifact::from_parsed(parsed).unwrap())
}

fn check_shadow(
    shadow: &ShadowArtifact,
    parameters: usize,
    calls: usize,
    uses: usize,
    outer_direct: bool,
    annotations: usize,
) {
    let skeleton = shadow.skeleton().unwrap();
    let raw = RawStructuralArena::from_artifact(shadow).unwrap();
    let projected = PendingStructuralProjection::from_raw_with_header(&raw).unwrap();
    let header = projected.root_declaration_header().unwrap();
    assert_eq!(header.parameters().len(), parameters);
    assert_eq!(header.body(), skeleton.body());
    assert_eq!(projected.annotations().len(), annotations);
    assert_eq!(skeleton.uses().len(), uses);
    assert_eq!(projected.nodes().len(), raw.nodes().len());
    let applications = raw
        .nodes()
        .iter()
        .filter(|node| node.call.is_some())
        .collect::<Vec<_>>();
    assert_eq!(applications.len(), calls);
    let outer = applications
        .iter()
        .find(|node| &node.source == header.body())
        .unwrap();
    assert_eq!(
        outer.call.as_ref().unwrap().direct_use.is_some(),
        outer_direct
    );
    for (index, node) in applications.iter().enumerate() {
        assert!(
            applications[..index]
                .iter()
                .all(|other| other.source != node.source)
        );
        let call = node.call.as_ref().unwrap();
        assert_eq!(
            call.source_use_input.is_some(),
            call.direct_use.is_some(),
            "source-use input follows only a retained direct Use registration"
        );
        assert_eq!(
            call.header_parameter.is_some(),
            call.direct_use.is_some(),
            "root-header membership follows only a retained direct Use registration"
        );
        let rows = skeleton
            .pending()
            .iter()
            .filter(|row| row.call() == &node.source)
            .collect::<Vec<_>>();
        assert!(!rows.is_empty());
        assert_eq!(call.application_premises.len(), rows.len());
        for (retained, original) in call.application_premises.iter().zip(rows) {
            assert!(std::ptr::eq(*retained, original));
        }
        if let Some(input) = &call.source_use_input {
            let member = call.header_parameter.as_ref().unwrap();
            assert_eq!(input.binder(), member.parameter);
            assert_eq!(input.application().expression(), &node.source);
            assert_eq!(
                skeleton.use_position(input.occurrence()).unwrap(),
                skeleton
                    .use_expression(input.occurrence())
                    .unwrap()
                    .position()
            );
        }
    }
}
