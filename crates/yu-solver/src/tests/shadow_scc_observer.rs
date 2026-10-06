use super::{collect, module};

#[test]
fn borrows_current_component_and_use_topology_without_solver_queries() {
    let batch = collect(module(
        "my a = b; my b = a; my c = 42; my d = a",
        "shadow-scc-observer.yu",
    ));
    let before = batch.counters();
    let topology = batch.shadow_scc_topology();

    let components = topology.components().collect::<Vec<_>>();
    let observed = components
        .iter()
        .map(|component| {
            let members = component
                .members()
                .map(|definition| definition.collection_ordinal())
                .collect::<Vec<_>>();
            (
                members,
                component.internal_uses().count(),
                component.incoming_uses().count(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        observed,
        vec![(vec![0, 1], 2, 1), (vec![2], 0, 0), (vec![3], 0, 0),]
    );
    let members = components[0].members().collect::<Vec<_>>();
    assert!(members[0].same_identity(components[0].canonical_definition()));
    assert!(components[0].same_identity(topology.component_of(members[1]).unwrap()));
    let internal_uses = components[0].internal_uses().collect::<Vec<_>>();
    assert_eq!(
        internal_uses
            .iter()
            .map(|use_id| use_id.occurrence_ordinal())
            .collect::<std::collections::HashSet<_>>()
            .len(),
        2
    );
    assert!(!internal_uses[0].same_identity(internal_uses[1]));

    let chain = collect(module(
        "my head = middle; my middle = tail; my tail = 42",
        "shadow-scc-order.yu",
    ));
    assert_eq!(
        chain
            .shadow_scc_topology()
            .definitions()
            .map(|definition| definition.collection_ordinal())
            .collect::<Vec<_>>(),
        vec![2, 1, 0]
    );
    assert_eq!(before, batch.counters());
}

#[test]
fn rejects_definition_handles_from_a_different_collection() {
    let first = collect(module("my a = 1", "shadow-scc-first.yu"));
    let second = collect(module("my b = 2", "shadow-scc-second.yu"));
    let foreign = second.shadow_scc_topology().definitions().next().unwrap();

    assert!(matches!(
        first.shadow_scc_topology().component_of(foreign),
        Err(crate::shadow_scc::SccTopologyLookupError::ForeignArtifact)
    ));
}
