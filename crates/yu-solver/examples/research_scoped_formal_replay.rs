//! Accepted source to retained typed Replay evidence for omitted formals.
//!
//! The source/HIR and candidate graph observations are provisional structural
//! evidence. They do not close an original typing or source/native theorem.

use std::sync::Arc;

use yu_hir::{
    FileId, FileKey, HirBinding, HirItem, HirModule, ModuleIdentity, SemanticImports, SourceRootId,
    lower_module,
    shadow::{LocalSourceForm, LocalSourceResolution},
};
use yu_solver::{ComponentKind, shadow_apply::{CandidateGraphExport, CandidateGraphLeaf, CandidateGraphNode, CandidateInference}};
use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

const SOURCE: &str = "my invoke f = f 1\nmy id x = x\nmy received = invoke id";
const SOURCE_SHA256: &str = "b9e4cc9a28de645a529ae31c7ca914b72efc73e51951bed917374f9c81c385d6";

fn main() {
    assert!(!SOURCE_SHA256.is_empty(), "freeze the accepted source literal");
    let source: Arc<SourceText> = Arc::from(SOURCE);
    let parsed = parse_file(
        source.clone(),
        Arc::new(scan_header(source)),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert!(
        parsed.syntax_diagnostics().unwrap().is_empty(),
        "accepted source has syntax diagnostics: {:?}",
        parsed.syntax_diagnostics().unwrap()
    );
    assert!(
        parsed.structural_recoveries().is_empty(),
        "accepted source has structural recoveries: {:?}",
        parsed.structural_recoveries()
    );
    let identity = ModuleIdentity::source_root(FileId::new(FileKey::new(
        "candidate-graph-local-source",
        "research_scoped_formal_replay.yu",
    )));
    let hir = Arc::new(
        lower_module(identity, &parsed, SemanticImports::empty()).unwrap(),
    );
    assert!(
        hir.errors().is_empty(),
        "accepted replacement fixture has HIR errors: {:?}",
        hir.errors()
    );
    assert_eq!(hir.source_carrier_outcomes().len(), 3);
    let invoke = binding(&hir, "invoke");
    let received = binding(&hir, "received");
    let invoke_owner = SourceRootId::Definition(invoke.definition_root().clone());
    let received_owner = SourceRootId::Definition(received.definition_root().clone());
    let invoke_source = hir
        .local_source(invoke.definition_root())
        .unwrap()
        .unwrap();
    let received_source = hir
        .local_source(received.definition_root())
        .unwrap()
        .unwrap();
    let formal_apply = invoke_source
        .expressions()
        .iter()
        .find(|expression| matches!(&expression.form, LocalSourceForm::Apply { .. }))
        .expect("invoke formal Apply is retained in its HIR-owned LocalSource");
    let received_apply = received_source
        .expressions()
        .iter()
        .find(|expression| matches!(&expression.form, LocalSourceForm::Apply { .. }))
        .expect("received outer Apply is retained in its HIR-owned LocalSource");
    let LocalSourceForm::Apply { callee, argument, .. } = &received_apply.form else {
        unreachable!()
    };
    let callee = received_source.expression(callee).unwrap();
    let argument = received_source.expression(argument).unwrap();
    let LocalSourceForm::Name {
        resolution: LocalSourceResolution::ModuleDef(invoke_id), ..
    } = &callee.form else {
        panic!("received callee is not the module definition invoke: {:?}", callee.form);
    };
    let LocalSourceForm::Name {
        resolution: LocalSourceResolution::ModuleDef(id_id), ..
    } = &argument.form else {
        panic!("received argument is not the module definition id: {:?}", argument.form);
    };
    assert_eq!(invoke_id, invoke.id());
    assert_eq!(id_id, binding(&hir, "id").id());

    let candidate = CandidateInference::solve_scoped_experiment(hir.clone())
        .expect("accepted source reaches scoped candidate inference");
    assert!(candidate.observes_hir(&hir));
    assert!(
        candidate.candidate_conflicts().is_empty(),
        "candidate propagation conflicts: {:?}",
        candidate.candidate_conflicts()
    );

    let formal_index = (0..candidate.source_call_count())
        .find(|index| {
            candidate.source_call(*index).is_ok_and(|call| {
                call.owner() == &invoke_owner
                    && call.source().occurrence == formal_apply.occurrence
            })
        })
        .expect("invoke's formal Apply has an exact source-call record");
    let formal_call = candidate.source_call(formal_index).unwrap();
    let introduction = formal_call
        .directional_introduction()
        .expect("omitted formal introduction is retained");
    assert_eq!(introduction.original_owner(), &invoke_owner);
    assert_eq!(introduction.original_demand(), formal_call.native_demand());
    assert_eq!(
        introduction.checking_occurrence().occurrence(),
        &formal_apply.occurrence
    );
    assert!(formal_call.formal_registration().is_some());
    println!(
        "invoke.apply call_index={formal_index} formal_introduction owner={:?} apply={:?} native_demand={:?}",
        introduction.original_owner(),
        formal_apply.occurrence,
        formal_call.native_demand()
    );

    let received_index = (0..candidate.source_call_count())
        .find(|index| {
            candidate.source_call(*index).is_ok_and(|call| {
                call.owner() == &received_owner
                    && call.source().occurrence == received_apply.occurrence
            })
        })
        .expect("received outer Apply has an exact source-call record");
    let received_call = candidate.source_call(received_index).unwrap();
    assert_eq!(received_call.source().occurrence, received_apply.occurrence);
    assert_eq!(
        received_call.checking_occurrence().occurrence(),
        &received_apply.occurrence
    );
    assert_ne!(
        received_call.checking_occurrence(),
        formal_call.checking_occurrence(),
        "received's outer Apply is distinct from invoke's formal Apply"
    );
    println!(
        "received.apply call_index={received_index} owner={:?} apply={:?} native_demand={:?}",
        received_call.owner(),
        received_call.source().occurrence,
        received_call.native_demand()
    );

    let graph = candidate.export(received.definition_root()).unwrap();
    assert!(int_reaches_root(&graph), "integer lower propagates to received result");
    println!(
        "received.result propagated_int=true graph_nodes={} graph_bounds={}",
        graph.node_count(),
        graph.bounds().count()
    );
    println!(
        "replay.expect call_index={formal_index} native_demand={:?} (typed observer rows are emitted on stderr when YU_CALL_REPLAY_OBSERVER=1)",
        formal_call.native_demand()
    );
    for transport in candidate.scoped_replay_demand_transports()
        .filter(|transport| transport.call_index == formal_index)
    {
        println!(
            "replay.transport call_index={} use_instance={} native_root={:?} copied_root={:?} native_root_matches={} route={:?} scope_map={} input_map={} ports={:?} ports_match={:?}",
            transport.call_index, transport.use_instance, transport.native_root,
            transport.copied_root, transport.native_root_matches, transport.route,
            transport.scope_map_matches, transport.input_map_matches,
            transport.ports, transport.ports_match,
        );
    }
}

fn binding<'a>(hir: &'a HirModule, name: &str) -> &'a HirBinding {
    hir.items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => Some(binding),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing module binding {name}"))
}

fn same_endpoint(left: CandidateGraphNode<'_>, right: CandidateGraphNode<'_>) -> bool {
    left.same_identity(right)
        || match (left.row(), right.row()) {
            (Some(left), Some(right)) => left.same_identity(&right),
            _ => false,
        }
}

fn reaches_root(
    graph: &CandidateGraphExport<'_>,
    start: CandidateGraphNode<'_>,
    kind: ComponentKind,
) -> bool {
    let mut pending = vec![start];
    let mut visited = Vec::new();
    while let Some(node) = pending.pop() {
        if same_endpoint(node, graph.root()) {
            return true;
        }
        if visited.iter().copied().any(|old| same_endpoint(old, node)) {
            continue;
        }
        visited.push(node);
        for bound in graph.bounds().filter(|bound| bound.kind() == kind) {
            if same_endpoint(bound.lower(), node) {
                pending.push(bound.upper());
            }
        }
    }
    false
}

fn int_reaches_root(graph: &CandidateGraphExport<'_>) -> bool {
    graph.bounds().any(|bound| {
        bound.kind() == ComponentKind::Value
            && bound.lower().leaf() == Some(CandidateGraphLeaf::IntPositive)
            && reaches_root(graph, bound.upper(), ComponentKind::Value)
    })
}
