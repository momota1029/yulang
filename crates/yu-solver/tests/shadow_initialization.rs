#![cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]

use std::sync::Arc;
use yu_hir::{
    FileId, FileKey, ModuleIdentity, SemanticImports,
    shadow::{ShadowArtifact, lower_module_with_source_identity},
};
use yu_solver::{
    ConstraintBatch, SolvedModule,
    shadow_initialization::{
        InitializationBoundaryOutcome, InitializationLookupError, InitializationPremise,
        InitializationRejectionReason,
    },
};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn input(source: &str) -> (Arc<yu_hir::HirModule>, ShadowArtifact) {
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(source.clone()));
    let parsed = parse_file(source, header, Arc::new(SyntaxEnvironment::empty()));
    let hir = Arc::new(
        lower_module_with_source_identity(
            ModuleIdentity::source_root(FileId::new(FileKey::new("shadow-init", "case.yu"))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    );
    (hir, ShadowArtifact::from_parsed(parsed).unwrap())
}

#[test]
fn exact_self_name_retains_original_edge_and_current_never_without_production_changes() {
    let (hir, shadow) = input("my f = f");
    let batch = ConstraintBatch::collect(hir.clone()).unwrap();
    let before = batch.counters();
    let inventory = batch.shadow_initialization_candidates();
    assert_eq!(batch.counters(), before);
    let candidate = inventory.candidates().next().unwrap();
    let outcome = inventory.boundary_outcome();
    assert_eq!(
        outcome,
        InitializationBoundaryOutcome::Reject {
            reason: InitializationRejectionReason::SelfInitNoValue,
            binder: candidate.root(),
            rhs: candidate.rhs_occurrence(),
        }
    );
    assert_eq!(inventory.candidates().count(), 1);
    assert_eq!(candidate.parent_ordinal(), candidate.target_ordinal());
    assert_eq!(
        candidate.component_canonical_ordinal(),
        candidate.parent_ordinal()
    );
    let root_position = candidate.definition_source_position(&shadow).unwrap();
    let rhs_position = candidate.rhs_source_position(&shadow).unwrap();
    let solved = SolvedModule::solve(batch).unwrap();
    let baseline = SolvedModule::solve(ConstraintBatch::collect(hir).unwrap()).unwrap();
    let before = solved.counters();
    // Terms are arena-branded: compare exact facts within this solve, not
    // identity-bearing records from the independently collected baseline.
    let before_facts = solved.store().facts().to_vec();
    let joined = solved.shadow_initialization(&inventory).unwrap();
    let retained = joined.candidates().next().unwrap();
    assert_eq!(inventory.boundary_outcome(), outcome);
    assert!(retained.same_use_identity(candidate));
    assert!(retained.same_component_identity(candidate));
    assert_eq!(
        retained.definition_source_position(&shadow).unwrap(),
        root_position
    );
    assert_eq!(retained.rhs_source_position(&shadow).unwrap(), rhs_position);
    let scheme = joined.current_scheme(retained).unwrap();
    assert_eq!(scheme.owner(), retained.root());
    let endpoints = scheme.endpoints();
    assert!(matches!(
        endpoints.positive_value(endpoints.predicate()).unwrap(),
        yu_types::PositiveValueView::Bottom
    ));
    assert_eq!(
        retained.original_q1_source_envelope_premise(),
        InitializationPremise::OriginalQ1SourceEnvelopeRecognized
    );
    assert_eq!(
        retained.pre_execution_enforcement_premise(),
        InitializationPremise::PreExecutionEnforcementPending
    );
    assert_eq!(solved.counters(), before);
    assert_eq!(solved.counters(), baseline.counters());
    assert_eq!(solved.store().facts(), before_facts);
    assert_eq!(solved.errors(), baseline.errors());
}

#[test]
fn lambda_self_use_and_two_member_aliases_are_not_whole_name_self_initializers() {
    for source in ["my f x = f", "my f = g; my g = f"] {
        let (hir, _) = input(source);
        let batch = ConstraintBatch::collect(hir).unwrap();
        assert_eq!(
            batch
                .shadow_initialization_candidates()
                .candidates()
                .count(),
            0
        );
    }
}

#[test]
fn multi_definition_candidate_does_not_discharge_exact_q1_or_execution_premises() {
    let (hir, _) = input("my f = f; my g = 1");
    let batch = ConstraintBatch::collect(hir).unwrap();
    let inventory = batch.shadow_initialization_candidates();
    assert_eq!(inventory.candidates().count(), 1);
    assert_eq!(
        inventory.boundary_outcome(),
        InitializationBoundaryOutcome::Unresolved
    );
    let solved = SolvedModule::solve(batch).unwrap();
    let joined = solved.shadow_initialization(&inventory).unwrap();
    let candidate = joined.candidates().next().unwrap();
    joined.current_scheme(candidate).unwrap();
    assert_eq!(
        candidate.original_q1_source_envelope_premise(),
        InitializationPremise::OriginalQ1SourceEnvelopeRecognitionPending
    );
    assert_eq!(
        candidate.pre_execution_enforcement_premise(),
        InitializationPremise::PreExecutionEnforcementPending
    );
}

#[test]
fn source_near_misses_never_supply_execution_permission() {
    for source in [
        "my f x = f",
        "my f = g; my g = f",
        "my f = f; my g = 1",
        "my f = (f)",
        "my (f) = f",
        "my f: Integer = f",
        "my f = f: Integer",
        "my f = g",
        "our f = f",
        "pub f = f",
    ] {
        let (hir, _) = input(source);
        // Collection retains unsupported and unresolved source as existing error
        // evidence. Boundary classification must not turn it into permission.
        let batch = ConstraintBatch::collect(hir).unwrap();
        let before = batch.counters();
        let inventory = batch.shadow_initialization_candidates();
        assert_eq!(
            inventory.boundary_outcome(),
            InitializationBoundaryOutcome::Unresolved,
            "source: {source}"
        );
        assert_eq!(batch.counters(), before);
    }
}

#[test]
fn same_spelling_and_even_shared_hir_cannot_join_foreign_collection() {
    let (hir, shadow) = input("my f = f");
    let first = ConstraintBatch::collect(hir.clone()).unwrap();
    let inventory = first.shadow_initialization_candidates();
    let other = ConstraintBatch::collect(hir).unwrap();
    let foreign_inventory = other.shadow_initialization_candidates();
    let foreign_solved = SolvedModule::solve(other).unwrap();
    assert!(matches!(
        foreign_solved.shadow_initialization(&inventory),
        Err(InitializationLookupError::ForeignCollection)
    ));
    let solved = SolvedModule::solve(first).unwrap();
    let joined = solved.shadow_initialization(&inventory).unwrap();
    assert!(matches!(
        joined.current_scheme(foreign_inventory.candidates().next().unwrap()),
        Err(InitializationLookupError::ForeignCollection)
    ));
    let (separate_hir, separate_shadow) = input("my f = f");
    let separate = ConstraintBatch::collect(separate_hir)
        .unwrap()
        .shadow_initialization_candidates();
    let (
        InitializationBoundaryOutcome::Reject {
            binder: first_b,
            rhs: first_n,
            ..
        },
        InitializationBoundaryOutcome::Reject {
            binder: other_b,
            rhs: other_n,
            ..
        },
    ) = (inventory.boundary_outcome(), separate.boundary_outcome())
    else {
        panic!("both independent exact sources carry their own rejecting evidence");
    };
    assert_ne!(first_b, other_b);
    assert_ne!(first_n, other_n);
    assert!(
        !inventory
            .candidates()
            .next()
            .unwrap()
            .same_use_identity(separate.candidates().next().unwrap())
    );
    assert!(
        inventory
            .candidates()
            .next()
            .unwrap()
            .rhs_source_position(&separate_shadow)
            .is_err()
    );
    assert!(
        separate
            .candidates()
            .next()
            .unwrap()
            .definition_source_position(&shadow)
            .is_err()
    );
}
