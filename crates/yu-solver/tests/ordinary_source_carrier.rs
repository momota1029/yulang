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

#[cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]
mod candidate {
    use super::*;
    use yu_hir::{DefinitionRootId, HirModule, LocalSourceForm};
    use yu_solver::shadow_apply::{
        CandidateError, CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode,
        CandidateInference,
    };
    use yu_types::ComponentKind;

    fn ordinary_modules(text: &str) -> (Arc<HirModule>, HirModule) {
        let source: Arc<SourceText> = Arc::from(text);
        let parsed = parse_file(
            source.clone(),
            Arc::new(scan_header(source)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
            "ordinary-candidate-source",
            "source.yu",
        )));
        let hir = lower_module(identity.clone(), &parsed, SemanticImports::empty()).unwrap();
        let foreign = lower_module(identity, &parsed, SemanticImports::empty()).unwrap();
        (Arc::new(hir), foreign)
    }

    fn root<'a>(hir: &'a HirModule, name: &str) -> &'a DefinitionRootId {
        hir.items()
            .iter()
            .find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == name => {
                    Some(binding.definition_root())
                }
                _ => None,
            })
            .expect("ordinary admitted binding")
    }

    fn value_lowers<'a>(graph: &CandidateGraphExport<'a>) -> Vec<CandidateGraphNode<'a>> {
        let mut work = vec![graph.root()];
        let mut visited = Vec::new();
        while let Some(node) = work.pop() {
            if visited
                .iter()
                .any(|prior: &CandidateGraphNode<'a>| prior.same_identity(node))
            {
                continue;
            }
            visited.push(node);
            for bound in graph.bounds() {
                if bound.kind() != ComponentKind::Value {
                    continue;
                }
                let upper = bound.upper();
                let same_row = node
                    .row()
                    .is_some_and(|row| upper.row().is_some_and(|other| row.same_identity(other)));
                if upper.same_identity(node) || same_row {
                    work.push(bound.lower());
                }
            }
        }
        visited
    }

    #[test]
    fn candidate_consumes_supported_carriers_from_the_exact_ordinary_hir() {
        for (text, calls, leaves) in [
            (
                "my id x = x; my result = id 1",
                1,
                vec![CandidateGraphLeaf::IntPositive],
            ),
            (
                r"my result = (\x -> x) 1",
                1,
                vec![CandidateGraphLeaf::IntPositive],
            ),
            (
                "my result = if true: 1 else: \"str\"",
                0,
                vec![
                    CandidateGraphLeaf::IntPositive,
                    CandidateGraphLeaf::StrPositive,
                ],
            ),
            (
                "my result = { my value = 1; value }",
                0,
                vec![CandidateGraphLeaf::IntPositive],
            ),
            (
                "my result = catch 1 { x -> x }",
                0,
                vec![CandidateGraphLeaf::IntPositive],
            ),
        ] {
            let (hir, foreign) = ordinary_modules(text);
            let root = root(&hir, "result");
            let source = hir.local_source(root).unwrap().expect("supported source");
            let candidate = CandidateInference::solve(hir.clone())
                .unwrap_or_else(|error| panic!("{text}: {error:?}"));
            assert!(candidate.observes_hir(hir.as_ref()), "{text}");
            assert!(!candidate.observes_hir(&foreign), "{text}");
            assert!(candidate.candidate_conflicts().is_empty(), "{text}");
            let graph = candidate.export(root).unwrap();
            let lowers = value_lowers(&graph);
            for leaf in leaves {
                assert!(
                    lowers.iter().any(|node| node.leaf() == Some(leaf)),
                    "{text}: {leaf:?}"
                );
            }
            assert_eq!(candidate.source_call_count(), calls, "{text}");
            assert_eq!(
                calls,
                source
                    .expressions()
                    .iter()
                    .filter(|expression| {
                        matches!(expression.form, LocalSourceForm::Apply { .. })
                    })
                    .count(),
                "{text}"
            );
            for index in 0..calls {
                let call = candidate.source_call(index).unwrap();
                assert_eq!(call.owner(), root);
                for expression in [call.source(), call.callee_source(), call.argument_source()] {
                    assert!(
                        source
                            .expressions()
                            .iter()
                            .any(|original| std::ptr::eq(original, expression))
                    );
                    assert_eq!(
                        hir.occurrence_source_key(&expression.occurrence).unwrap(),
                        Some(&expression.source)
                    );
                }
            }
            assert!(candidate.export(self::root(&foreign, "result")).is_err());
        }
    }

    #[test]
    fn candidate_reports_source_constraints_from_an_ordinary_conditional() {
        let (hir, _) = ordinary_modules("my result = if 1: 1 else: 2");
        let root = root(&hir, "result");
        assert!(hir.local_source(root).unwrap().is_some());
        let candidate = CandidateInference::solve(hir.clone()).unwrap();
        assert!(candidate.observes_hir(hir.as_ref()));
        assert!(!candidate.candidate_conflicts().is_empty());
        // Existing export policy rejects conflicted graphs.
        assert!(candidate.export(root).is_err());
    }

    #[test]
    fn candidate_refuses_unsupported_and_recovered_ordinary_carriers() {
        for text in ["my bad = (1, 2); my later = 1", "my bad = @; my later = 1"] {
            let (hir, _) = ordinary_modules(text);
            assert!(matches!(
                hir.source_carrier(root(&hir, "bad")).unwrap(),
                Some(SourceCarrierOutcome::Unsupported(_))
            ));
            assert!(matches!(
                hir.source_carrier(root(&hir, "later")).unwrap(),
                Some(SourceCarrierOutcome::Supported(_))
            ));
            assert!(matches!(
                CandidateInference::solve(hir),
                Err(CandidateError::Unsupported)
            ));
        }
    }
}
