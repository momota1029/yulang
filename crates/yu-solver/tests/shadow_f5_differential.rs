#![cfg(feature = "shadow-f5")]

//! Structural differential for the exact common leaf-only input `my f x = x`.
//! Parsing is shared; shadow projection and current production F5 lowering are
//! separate paths. Compare source spelling/ranges and lexical resolution within
//! each artifact, never IDs across artifacts. This does not establish old-infer
//! parity, scheme equality, Apply support, callable roles, Function membership,
//! call views, soundness, or principality.

use std::sync::Arc;
use yu_hir::{
    FileId, FileKey, HirItem, ModuleIdentity, NameResolution, ResolvedExpr, SemanticImports,
    lower_module,
    shadow::{Form, ShadowArtifact},
};
use yu_solver::{ConstraintBatch, SolvedModule};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

#[test]
fn shadow_and_current_f5_preserve_leaf_parameter_source_and_resolution() {
    let source: Arc<SourceText> = Arc::from("my f x = x");
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    let hir = Arc::new(
        lower_module(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "shadow-f5-differential",
                "leaf.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .expect("current F5 HIR is available for the common leaf input"),
    );
    let shadow = ShadowArtifact::from_parsed(parsed).expect("shadow artifact is available");
    let skeleton = shadow.skeleton().expect("leaf skeleton is supported");
    assert!(skeleton.pending().is_empty());
    assert!(
        skeleton
            .expressions()
            .iter()
            .all(|expression| !matches!(expression.form(), Form::Apply { .. }))
    );
    assert_eq!(skeleton.binders().len(), 1);
    assert_eq!(skeleton.uses().len(), 1);
    let shadow_body = skeleton.expression(skeleton.body()).unwrap();
    let Form::Use { binder, occurrence } = shadow_body.form() else {
        panic!("shadow leaf body must be a lexical use");
    };
    let shadow_parameter = skeleton.binder(binder).unwrap();
    assert_eq!(shadow_parameter.name(), "x");
    assert_eq!(shadow_parameter.range(), &(5..6));
    assert_eq!(shadow_body.range(), &(9..10));
    assert_eq!(
        skeleton.use_expression(occurrence).unwrap().range(),
        shadow_body.range()
    );
    assert_eq!(
        skeleton.expression(&skeleton.uses()[0]).unwrap().range(),
        shadow_body.range()
    );

    assert!(hir.errors().is_empty());
    assert!(hir.diagnostics().is_empty());
    let [HirItem::Binding(binding)] = hir.items() else {
        panic!("current F5 must retain the single binding");
    };
    let [parameter] = binding.parameters() else {
        panic!("current F5 must retain the single formal parameter");
    };
    let ResolvedExpr::Lambda {
        parameter: lambda_parameter,
        body,
        ..
    } = binding.value()
    else {
        panic!("current F5 must lower the binding to a lambda");
    };
    let ResolvedExpr::Name {
        name,
        resolution: NameResolution::Parameter(resolved_parameter),
        ..
    } = body.as_ref()
    else {
        panic!("current F5 leaf body must resolve to its formal parameter");
    };
    assert_eq!(lambda_parameter, parameter.id());
    assert_eq!(resolved_parameter, parameter.id());
    assert!(hir.owns_parameter(resolved_parameter));
    assert_eq!(parameter.name().spelling(), shadow_parameter.name());
    assert_eq!(parameter.name().range(), shadow_parameter.range());
    assert_eq!(name.spelling(), shadow_parameter.name());
    assert_eq!(name.range(), shadow_body.range());
    assert_eq!(body.range(), shadow_body.range());

    let body_occurrence = body.occurrence().clone();
    let batch = ConstraintBatch::collect(hir).expect("current F5 collection is available");
    assert!(
        batch
            .occurrences()
            .iter()
            .any(|constraint| { constraint.cause().occurrence().occurrence() == &body_occurrence })
    );
    let solved = SolvedModule::solve(batch).expect("current F5 solving is available");
    assert!(solved.errors().is_empty());
    assert!(
        solved
            .store()
            .provenance()
            .iter()
            .any(|edge| { edge.cause().occurrence().occurrence() == &body_occurrence })
    );
}
