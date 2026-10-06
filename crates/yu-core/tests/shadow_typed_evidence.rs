#![cfg(feature = "shadow")]

use yu_core::shadow_directional_protection::AssumedOriginalContext;
use yu_core::shadow_typed_evidence::*;

#[test]
fn finite_path_matches_independent_closure_for_all_three_node_graphs() {
    let tokens = [1_u8; 12]; // Equal values are deliberately distinct witnesses.
    let context = AssumedOriginalContext {
        beta: &tokens[0],
        scope: &tokens[1],
        xi: &tokens[2],
        shared_variable: &tokens[3],
    };
    let nodes = (0..3)
        .map(|i| AssumedTypedPort {
            context: &context,
            view: &tokens[4 + i],
            position: &tokens[7],
        })
        .collect::<Vec<_>>();
    let boundary = AssumedBoundary {
        context: &context,
        witness: &tokens[8],
        original_receiver: &tokens[9],
    };
    let profiles = (0..3)
        .map(|port| AssumedProfile {
            witness: &tokens[8],
            boundary: &boundary,
            port,
        })
        .collect::<Vec<_>>();
    let event = AssumedEvent {
        context: &context,
        witness: &tokens[10],
    };
    let handler = AssumedHandler {
        context: &context,
        witness: &tokens[11],
        owner: &tokens[0],
    };
    let handlers = [&tokens[11]];
    let owners = [&tokens[0], &tokens[9]];
    let current = AssumedConfiguration {
        context: &context,
        active_handlers: &handlers,
        active_owners: &owners,
    };
    for mask in 0..512_u16 {
        let flows = (0..9)
            .filter(|bit| mask & (1 << bit) != 0)
            .map(|bit| AssumedFlow {
                context: &context,
                from: bit / 3,
                to: bit % 3,
            })
            .collect::<Vec<_>>();
        let mut closure = [[false; 3]; 3];
        for (i, row) in closure.iter_mut().enumerate() {
            row[i] = true;
        }
        for edge in &flows {
            closure[edge.from][edge.to] = true;
        }
        for via in 0..3 {
            for from in 0..3 {
                for to in 0..3 {
                    closure[from][to] |= closure[from][via] && closure[via][to];
                }
            }
        }
        for target in 0..3 {
            let observations = [AssumedObserve {
                event: &event,
                port: target,
            }];
            let receipts = [AssumedReceive {
                context: &context,
                owner: handler.owner,
                port: target,
            }];
            let graph = AssumedTypedEvidence::new(
                &context,
                &nodes,
                &profiles,
                &flows,
                &observations,
                &receipts,
            )
            .unwrap();
            for (from, row) in closure.iter().enumerate() {
                let answer = graph
                    .query_conditionally(from, &event, &handler, &current)
                    .unwrap();
                assert_eq!(answer.status, ConditionalStatus::Assumed);
                assert_eq!(answer.path, row[target], "mask={mask}, {from}->{target}");
                assert_eq!(answer.inc_c, row[target]);
            }
        }
    }
}

#[test]
fn exact_joins_lifetime_and_malformed_inputs_remain_conditional() {
    let tokens = [1_u8; 12];
    let context = AssumedOriginalContext {
        beta: &tokens[0],
        scope: &tokens[1],
        xi: &tokens[2],
        shared_variable: &tokens[3],
    };
    let other_context = AssumedOriginalContext {
        beta: &tokens[0],
        scope: &tokens[1],
        xi: &tokens[2],
        shared_variable: &tokens[3],
    };
    let nodes = [
        AssumedTypedPort {
            context: &context,
            view: &tokens[4],
            position: &tokens[6],
        },
        AssumedTypedPort {
            context: &context,
            view: &tokens[5],
            position: &tokens[6],
        },
    ];
    let boundary = AssumedBoundary {
        context: &context,
        witness: &tokens[7],
        original_receiver: &tokens[8],
    };
    let profiles = [AssumedProfile {
        witness: &tokens[7],
        boundary: &boundary,
        port: 0,
    }];
    let event = AssumedEvent {
        context: &context,
        witness: &tokens[9],
    };
    let same_event = AssumedEvent {
        context: &context,
        witness: &tokens[9],
    };
    let distinct_event = AssumedEvent {
        context: &context,
        witness: &tokens[0],
    };
    let handler = AssumedHandler {
        context: &context,
        witness: &tokens[10],
        owner: &tokens[11],
    };
    let observations = [AssumedObserve {
        event: &event,
        port: 1,
    }];
    let receipts = [AssumedReceive {
        context: &context,
        owner: handler.owner,
        port: 1,
    }];
    let flows = [AssumedFlow {
        context: &context,
        from: 0,
        to: 1,
    }];
    let handlers = [handler.witness];
    let owners = [handler.owner, boundary.original_receiver];
    let current = AssumedConfiguration {
        context: &context,
        active_handlers: &handlers,
        active_owners: &owners,
    };
    let query = |flows: &[AssumedFlow<'_, u8>],
                 obs: &[AssumedObserve<'_, u8>],
                 receipts: &[AssumedReceive<'_, u8>],
                 current: &AssumedConfiguration<'_, u8>| {
        AssumedTypedEvidence::new(&context, &nodes, &profiles, flows, obs, receipts)
            .unwrap()
            .query_conditionally(0, &event, &handler, current)
            .unwrap()
    };
    assert!(query(&flows, &observations, &receipts, &current).inc_c);
    assert!(!query(&[], &observations, &receipts, &current).path); // same-valued alias
    assert!(!query(&flows, &[], &receipts, &current).path);
    assert!(!query(&flows, &observations, &[], &current).path);
    let wrong_receipt = [AssumedReceive {
        context: &context,
        owner: &tokens[0],
        port: 1,
    }];
    assert!(!query(&flows, &observations, &wrong_receipt, &current).path);
    let wrong_port = [AssumedReceive {
        context: &context,
        owner: handler.owner,
        port: 0,
    }];
    assert!(!query(&flows, &observations, &wrong_port, &current).path);
    for (active_handlers, active_owners) in [
        (&[][..], &owners[..]),
        (&handlers[..], &owners[1..]),
        (&handlers[..], &owners[..1]),
    ] {
        let expired = AssumedConfiguration {
            context: &context,
            active_handlers,
            active_owners,
        };
        let answer = query(&flows, &observations, &receipts, &expired);
        assert!(answer.path);
        assert!(!answer.inc_c);
    }
    // A fresh equal-valued receiver reachable on raw reentry is not the original.
    let reentry_owners = [handler.owner, &tokens[0]];
    let reentry = AssumedConfiguration {
        context: &context,
        active_handlers: &handlers,
        active_owners: &reentry_owners,
    };
    assert!(!query(&flows, &observations, &receipts, &reentry).inc_c);
    let graph = AssumedTypedEvidence::new(
        &context,
        &nodes,
        &profiles,
        &flows,
        &observations,
        &receipts,
    )
    .unwrap();
    assert!(
        graph
            .query_conditionally(0, &same_event, &handler, &current)
            .unwrap()
            .path
    );
    assert!(
        !graph
            .query_conditionally(0, &distinct_event, &handler, &current)
            .unwrap()
            .path
    );
    assert_eq!(
        graph.query_conditionally(usize::MAX, &event, &handler, &current),
        Err(EvidenceError::InvalidProfile)
    );
    let mixed_current = AssumedConfiguration {
        context: &other_context,
        active_handlers: &handlers,
        active_owners: &owners,
    };
    assert_eq!(
        graph.query_conditionally(0, &event, &handler, &mixed_current),
        Err(EvidenceError::MixedContext)
    );
    let mixed_event = AssumedEvent {
        context: &other_context,
        witness: event.witness,
    };
    assert_eq!(
        graph.query_conditionally(0, &mixed_event, &handler, &current),
        Err(EvidenceError::MixedContext)
    );
    let mixed_handler = AssumedHandler {
        context: &other_context,
        witness: handler.witness,
        owner: handler.owner,
    };
    assert_eq!(
        graph.query_conditionally(0, &event, &mixed_handler, &current),
        Err(EvidenceError::MixedContext)
    );
    let invalid = [AssumedFlow {
        context: &context,
        from: 0,
        to: usize::MAX,
    }];
    assert!(matches!(
        AssumedTypedEvidence::new(
            &context,
            &nodes,
            &profiles,
            &invalid,
            &observations,
            &receipts
        ),
        Err(EvidenceError::InvalidNode)
    ));
    let mixed = [AssumedFlow {
        context: &other_context,
        from: 0,
        to: 1,
    }];
    assert!(matches!(
        AssumedTypedEvidence::new(
            &context,
            &nodes,
            &profiles,
            &mixed,
            &observations,
            &receipts
        ),
        Err(EvidenceError::MixedContext)
    ));
    let duplicate = [
        AssumedTypedPort {
            context: &context,
            view: &tokens[4],
            position: &tokens[6],
        },
        AssumedTypedPort {
            context: &context,
            view: &tokens[4],
            position: &tokens[6],
        },
    ];
    assert!(matches!(
        AssumedTypedEvidence::new(
            &context,
            &duplicate,
            &profiles,
            &flows,
            &observations,
            &receipts
        ),
        Err(EvidenceError::DuplicatePort)
    ));
    let mixed_nodes = [AssumedTypedPort {
        context: &other_context,
        view: &tokens[4],
        position: &tokens[6],
    }];
    assert!(matches!(
        AssumedTypedEvidence::new(&context, &mixed_nodes, &[], &[], &[], &[]),
        Err(EvidenceError::MixedContext)
    ));
}

#[test]
fn zero_sized_storage_cannot_supply_distinct_identity_tokens() {
    let tokens = [(); 4];
    let context = AssumedOriginalContext {
        beta: &tokens[0],
        scope: &tokens[1],
        xi: &tokens[2],
        shared_variable: &tokens[3],
    };
    assert!(matches!(
        AssumedTypedEvidence::new(&context, &[], &[], &[], &[], &[]),
        Err(EvidenceError::ZeroSizedWitness)
    ));
}
