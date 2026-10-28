#![cfg(feature = "shadow-f5")]

use std::sync::Arc;
use yu_hir::shadow::{
    ShadowArtifact, lower_module_with_shadow_local_binding, lower_module_with_source_identity,
};
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, ResolvedExpr, SemanticImports};
use yu_solver::shadow_f5::{GeneralizationOriginState, ParameterRowState};
use yu_solver::{ConstraintBatch, PendingApplicationState, SolvedModule};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str, local: bool) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let identity =
        ModuleIdentity::source_root(FileId::new(FileKey::new("shadow", "parameter-row.yu")));
    Arc::new(if local {
        let shadow = Arc::new(ShadowArtifact::from_parsed(parsed.clone()).unwrap());
        lower_module_with_shadow_local_binding(identity, &parsed, SemanticImports::empty(), shadow)
            .unwrap()
    } else {
        lower_module_with_source_identity(identity, &parsed, SemanticImports::empty()).unwrap()
    })
}

#[test]
fn startup_parameter_row_is_exact_selected_origin_and_solve_branded() {
    let hir = module("my id x = x", false);
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("binding")
    };
    let parameter = binding.parameters()[0].id();
    let batch = ConstraintBatch::collect(hir.clone()).unwrap();
    let ordinary_batch = ConstraintBatch::collect(hir.clone()).unwrap();
    let ordinary = SolvedModule::solve(ordinary_batch.clone()).unwrap();
    let solved = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
    assert_eq!(ordinary.counters(), solved.counters());
    let other = SolvedModule::solve_with_shadow_fresh_capture(batch).unwrap();
    assert!(matches!(
        ordinary.shadow_parameter_row(parameter).unwrap(),
        ParameterRowState::NotRequested
    ));
    let ParameterRowState::Captured(row) = solved.shadow_parameter_row(parameter).unwrap() else {
        panic!("allocated parameter")
    };
    let ParameterRowState::Captured(repeated) = solved.shadow_parameter_row(parameter).unwrap()
    else {
        panic!("repeated parameter")
    };
    let ParameterRowState::Captured(foreign_solve) = other.shadow_parameter_row(parameter).unwrap()
    else {
        panic!("other solve parameter")
    };
    assert!(row.same_identity(repeated));
    assert!(!row.same_identity(foreign_solve));
    let scheme = solved
        .shadow_closed_schemes()
        .for_root(binding.definition_root())
        .unwrap();
    let GeneralizationOriginState::Captured(origins) = scheme.current_generalization_origins()
    else {
        panic!("selected origins")
    };
    assert_eq!(
        origins
            .bindings()
            .filter(|(_, origin)| row.same_identity(*origin))
            .count(),
        1
    );
    let foreign_hir = module("my id x = x", false);
    let HirItem::Binding(foreign_binding) = &foreign_hir.items()[0] else {
        panic!("binding")
    };
    assert!(matches!(
        solved.shadow_parameter_row(foreign_binding.parameters()[0].id()),
        Err(yu_hir::shadow::SourceIdentityError::ForeignHirArtifact)
    ));
    assert_eq!(ordinary.errors(), solved.errors());
    for occurrence in solved.occurrences() {
        assert_eq!(
            ordinary.projection_for(occurrence).unwrap(),
            solved.projection_for(occurrence).unwrap()
        );
    }
    assert_eq!(ordinary.store().facts().len(), solved.store().facts().len());
}

#[test]
fn pending_local_apply_retains_outer_startup_row_without_fabricating_local_row() {
    let hir = module("my apply f = { my step x = f x; step }", true);
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("binding")
    };
    let ResolvedExpr::Lambda { parameter: f, .. } = binding.value() else {
        panic!("outer lambda")
    };
    let ResolvedExpr::Lambda { body, .. } = binding.value() else {
        unreachable!()
    };
    assert!(matches!(body.as_ref(), ResolvedExpr::Error { .. }));
    let local = hir
        .shadow_local_binding(binding.definition_root())
        .unwrap()
        .unwrap();
    let ResolvedExpr::Lambda { parameter: x, .. } = &local.initializer else {
        panic!("local lambda")
    };
    let batch = ConstraintBatch::collect(hir.clone()).unwrap();
    let ordinary_batch = ConstraintBatch::collect(hir.clone()).unwrap();
    let ordinary = SolvedModule::solve(ordinary_batch.clone()).unwrap();
    let solved = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
    assert!(matches!(
        solved.shadow_parameter_row(f).unwrap(),
        ParameterRowState::Captured(_)
    ));
    assert!(matches!(
        solved.shadow_parameter_row(x).unwrap(),
        ParameterRowState::NoProductionRecipe
    ));
    assert_eq!(solved.pending_applications().len(), 1);
    assert!(solved.store().facts().is_empty());
    assert_eq!(
        solved.pending_applications()[0].state,
        PendingApplicationState::ApplicationTypingRuleUnresolved
    );
    assert_eq!(ordinary.errors(), solved.errors());
    for occurrence in solved.occurrences() {
        assert_eq!(
            ordinary.projection_for(occurrence).unwrap(),
            solved.projection_for(occurrence).unwrap()
        );
    }
    assert_eq!(ordinary.counters(), solved.counters());
    assert_eq!(ordinary.store().facts().len(), solved.store().facts().len());
}
