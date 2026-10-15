use std::sync::Arc;

use yu_hir::{
    FileId, FileKey, HirItem, ModuleIdentity, ResolvedExpr, SemanticImports,
    SourceCarrierOutcome, lower_module,
};
use yu_solver::ConstraintBatch;
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

#[test]
fn ordinary_collection_retains_and_exposes_the_owning_source_carrier() {
    let source: Arc<SourceText> = Arc::from("my answer = 1");
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
        "ordinary-source-carrier",
        "answer.yu",
    )));
    let hir = Arc::new(
        lower_module(identity.clone(), &parsed, SemanticImports::empty()).unwrap(),
    );
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("ordinary binding");
    };
    let root = binding.definition_root();
    let ResolvedExpr::Integer { occurrence, .. } = binding.value() else {
        panic!("ordinary integer");
    };
    let SourceCarrierOutcome::Supported(carrier) = hir.source_carrier(root).unwrap().unwrap()
    else {
        panic!("supported ordinary source");
    };
    assert_eq!(carrier.definition_root(), root);

    // Collection retains this HIR and exposes its carrier; successor constraint
    // consumption remains a separate gate.
    let batch = ConstraintBatch::collect(hir.clone()).unwrap();
    assert!(Arc::ptr_eq(batch.hir(), &hir));
    let retained = batch.hir().local_source(root).unwrap().unwrap();
    assert!(std::ptr::eq(carrier, retained));
    assert_eq!(retained.definition_root(), root);
    for expression in retained.expressions() {
        assert!(hir.owns_occurrence(&expression.occurrence));
        assert_eq!(
            batch
                .hir()
                .occurrence_source_key(&expression.occurrence)
                .unwrap(),
            Some(&expression.source),
        );
    }

    let root_component = batch.root_value_component(root).unwrap();
    assert_eq!(root_component.definition_root(), Some(root));
    let integer_components = batch.components_for(occurrence).unwrap().unwrap();
    assert_eq!(integer_components.value().occurrence(), Some(occurrence));
    assert_eq!(integer_components.effect().occurrence(), Some(occurrence));

    let foreign = lower_module(identity, &parsed, SemanticImports::empty()).unwrap();
    let HirItem::Binding(foreign_binding) = &foreign.items()[0] else {
        panic!("foreign binding");
    };
    assert!(
        batch
            .hir()
            .source_carrier(foreign_binding.definition_root())
            .is_err()
    );
    assert!(
        batch
            .root_value_component(foreign_binding.definition_root())
            .is_err()
    );
}
