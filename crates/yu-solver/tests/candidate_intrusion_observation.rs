#![cfg(all(feature = "shadow-f5", feature = "shadow-apply-candidate"))]
use std::sync::Arc;
use yu_hir::shadow::lower_module_with_local_source;
use yu_hir::{FileId, FileKey, HirItem, HirModule, ModuleIdentity, SemanticImports};
use yu_solver::shadow_apply::{CandidateInference, CandidateSourceValueIdentity};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

fn module(text: &str) -> Arc<HirModule> {
    let source: Arc<SourceText> = Arc::from(text);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    assert!(parsed.structural_recoveries().is_empty());
    Arc::new(
        lower_module_with_local_source(
            ModuleIdentity::source_root(FileId::new(FileKey::new(
                "intrusion-observation",
                "source.yu",
            ))),
            &parsed,
            SemanticImports::empty(),
        )
        .unwrap(),
    )
}

#[test]
fn retained_nested_calls_observe_actual_value_scc_and_equated_pairs() {
    let candidate =
        CandidateInference::solve(module("my loop x = { my helper y = loop y; helper x }"))
            .unwrap();
    let observation = candidate.intrusion_observation().unwrap();
    let events: Vec<_> = observation.events().collect();
    assert_eq!(events.len(), 2);
    assert!(events.iter().all(|event| event.same_scc));
    assert_ne!(events[0].origin.ordinal, events[1].origin.ordinal);
    assert_eq!(events[0].origin.ordinal, events[1].receiver.ordinal);
    assert_eq!(events[1].origin.ordinal, events[0].receiver.ordinal);
    let parents: Vec<_> = observation.parents().collect();
    assert!(!parents.is_empty());
    for parent in &parents {
        if parent.source_events.iter().any(|&id| events[id].same_scc) {
            assert_eq!(parent.copy.kind, parent.parent.kind);
            assert_eq!(parent.copy.representative, parent.parent.representative);
        }
    }
    let groups: Vec<_> = observation.groups().collect();
    for group in &groups {
        assert!(group.start < group.end && group.end <= parents.len());
        assert!(
            parents[group.start..group.end]
                .iter()
                .all(|parent| parent.occurrence == group.occurrence)
        );
    }
    for reuse in observation.reuses() {
        let group = &groups[reuse.group];
        assert_ne!(reuse.occurrence, group.occurrence);
        assert!(!reuse.source_events.is_empty());
        assert!(
            reuse
                .source_events
                .iter()
                .all(|&event| event < events.len())
        );
    }
    assert_eq!(observation.pending_total(), observation.pending_consumed());
}

#[test]
fn acyclic_source_calls_do_not_report_value_scc_qualification() {
    let hir = module("my id x = x; my client x = id x");
    let bindings: Vec<_> = hir
        .items()
        .iter()
        .filter_map(|item| match item {
            HirItem::Binding(binding) => Some(binding),
            _ => None,
        })
        .collect();
    assert_eq!(
        bindings
            .iter()
            .map(|binding| binding.name().spelling())
            .collect::<Vec<_>>(),
        ["id", "client"]
    );
    let candidate = CandidateInference::solve(hir.clone()).unwrap();
    let observation = candidate.intrusion_observation().unwrap();
    let events: Vec<_> = observation.events().collect();
    assert_eq!(events.len(), 1);
    assert!(!events[0].same_scc);
    assert!(
        matches!(events[0].origin.identity, CandidateSourceValueIdentity::Module(id) if id == bindings[1].id())
    );
    assert!(
        matches!(events[0].receiver.identity, CandidateSourceValueIdentity::Module(id) if id == bindings[0].id())
    );
    assert_ne!(events[0].origin.component, events[0].receiver.component);
    assert_eq!(observation.pending_total(), observation.pending_consumed());
}

#[test]
fn conflicts_withhold_intrusion_observation() {
    let candidate = CandidateInference::solve(module("my bad = 1 2")).unwrap();
    assert!(!candidate.candidate_conflicts().is_empty());
    assert!(candidate.intrusion_observation().is_err());
}
