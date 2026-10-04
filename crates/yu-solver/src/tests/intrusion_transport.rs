use std::collections::HashSet;

use crate::intrusion_transport::{
    AllocationLane, Atom, Bound, FaultInjection, Graph, Identity, ParentView, Term, TermId,
    TransportError, make_parent, make_uses,
};

fn sample_graph() -> Graph {
    Graph {
        identities: vec![Identity(1), Identity(2), Identity(90)],
        terms: vec![
            Term::Variable(Identity(1)),
            Term::Variable(Identity(2)),
            Term::Variable(Identity(90)),
            Term::Atom(Atom::Int),
            Term::Atom(Atom::Bool),
            Term::Function {
                argument: TermId(0),
                argument_effect: TermId(1),
                result_effect: TermId(2),
                result: TermId(3),
            },
            Term::Function {
                argument: TermId(5),
                argument_effect: TermId(4),
                result_effect: TermId(1),
                result: TermId(0),
            },
            // A real regular back-edge, retained as an address rather than
            // expanded into a recursive type equation.
            Term::Function {
                argument: TermId(3),
                argument_effect: TermId(2),
                result_effect: TermId(4),
                result: TermId(7),
            },
            Term::Atom(Atom::EffectRead),
            Term::Atom(Atom::EffectWrite),
            Term::Bottom,
            Term::Top,
        ],
        bounds: vec![
            Bound {
                lower: TermId(0),
                upper: TermId(5),
                evidence: 0..2,
            },
            Bound {
                lower: TermId(5),
                upper: TermId(2),
                evidence: 2..3,
            },
            Bound {
                lower: TermId(7),
                upper: TermId(7),
                evidence: 3..5,
            },
            Bound {
                lower: TermId(6),
                upper: TermId(7),
                evidence: 5..5,
            },
        ],
        evidence: vec![103, 107, 109, 113, 127],
        root: TermId(7),
    }
}

fn parent(graph: &Graph) -> ParentView {
    make_parent(
        graph,
        &[Identity(1), Identity(2)],
        &[Identity(90)],
        &[Identity(300), Identity(301)],
        FaultInjection::default(),
    )
    .unwrap()
}

// Independent whole-graph copy-and-substitute reference. It walks the source
// arrays directly and never calls the transport implementation.
fn reference_substitute(graph: &Graph, mapping: &[(Identity, Identity)]) -> Graph {
    let rename = |identity: Identity| {
        mapping
            .iter()
            .find_map(|(from, to)| (*from == identity).then_some(*to))
            .unwrap_or(identity)
    };
    Graph {
        terms: graph
            .terms
            .iter()
            .map(|term| match *term {
                Term::Variable(identity) => Term::Variable(rename(identity)),
                Term::Atom(atom) => Term::Atom(atom),
                Term::Bottom => Term::Bottom,
                Term::Top => Term::Top,
                Term::Function {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } => Term::Function {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                },
            })
            .collect(),
        bounds: graph.bounds.clone(),
        evidence: graph.evidence.clone(),
        identities: graph.identities.iter().copied().map(rename).collect(),
        root: graph.root,
    }
}

fn inverse_map(mapping: &[(Identity, Identity)]) -> Vec<(Identity, Identity)> {
    mapping.iter().map(|(from, to)| (*to, *from)).collect()
}

fn assert_injective_mapping(mapping: &[(Identity, Identity)]) {
    let from: HashSet<_> = mapping.iter().map(|(from, _)| *from).collect();
    let to: HashSet<_> = mapping.iter().map(|(_, to)| *to).collect();
    assert_eq!(from.len(), mapping.len(), "mapping domain is not unique");
    assert_eq!(to.len(), mapping.len(), "mapping range is not injective");
}

fn reference_join(left: &Graph, right: &Graph) -> Graph {
    let term_offset = left.terms.len();
    let evidence_offset = left.evidence.len();
    let shift = |term: TermId| TermId(term.0 + term_offset);
    let mut terms = left.terms.clone();
    terms.extend(right.terms.iter().map(|term| match *term {
        Term::Function {
            argument,
            argument_effect,
            result_effect,
            result,
        } => Term::Function {
            argument: shift(argument),
            argument_effect: shift(argument_effect),
            result_effect: shift(result_effect),
            result: shift(result),
        },
        atom => atom,
    }));

    let mut bounds = left.bounds.clone();
    bounds.extend(right.bounds.iter().map(|bound| Bound {
        lower: shift(bound.lower),
        upper: shift(bound.upper),
        evidence: (bound.evidence.start + evidence_offset)..(bound.evidence.end + evidence_offset),
    }));

    let mut evidence = left.evidence.clone();
    evidence.extend_from_slice(&right.evidence);
    evidence.push(211);
    bounds.push(Bound {
        lower: left.root,
        upper: shift(right.root),
        evidence: (evidence.len() - 1)..evidence.len(),
    });

    let mut seen = HashSet::new();
    let identities = left
        .identities
        .iter()
        .chain(&right.identities)
        .copied()
        .filter(|identity| seen.insert(*identity))
        .collect();
    Graph {
        terms,
        bounds,
        evidence,
        identities,
        root: left.root,
    }
}

#[test]
fn parent_transport_matches_independent_whole_graph_substitution() {
    let source = sample_graph();
    let source_snapshot = source.clone();
    let view = parent(&source);
    assert_eq!(source, source_snapshot);
    assert_eq!(
        view.graph,
        reference_substitute(&source, &view.identity_map)
    );
    assert_injective_mapping(&view.identity_map);
    assert_eq!(
        reference_substitute(&view.graph, &inverse_map(&view.identity_map)),
        source
    );

    // All four Function children, shared term addresses, evidence order and
    // the regular back-edge survive the copy.
    assert_eq!(view.graph.terms[5], source.terms[5]);
    assert_eq!(view.graph.terms[6], source.terms[6]);
    assert_eq!(view.graph.terms[7], source.terms[7]);
    assert_eq!(view.graph.terms[8], Term::Atom(Atom::EffectRead));
    assert_eq!(view.graph.terms[9], Term::Atom(Atom::EffectWrite));
    assert_eq!(view.graph.terms[10], Term::Bottom);
    assert_eq!(view.graph.terms[11], Term::Top);
    assert_eq!(view.graph.bounds, source.bounds);
    assert_eq!(view.graph.evidence, source.evidence);
    assert_eq!(view.graph.root, source.root);
}

#[test]
fn independent_uses_are_fresh_against_every_receiver_and_each_other() {
    let source = sample_graph();
    let view = parent(&source);
    let receiver_a = (0..12).map(Identity).collect::<Vec<_>>();
    let receiver_b = (20..30).map(Identity).collect::<Vec<_>>();
    let overlays = make_uses(
        &view,
        &[receiver_a.clone(), receiver_b.clone()],
        FaultInjection::default(),
    )
    .unwrap();
    assert_eq!(overlays.len(), 2);

    for (overlay, receiver) in overlays.iter().zip([receiver_a, receiver_b]) {
        assert_eq!(
            overlay.graph,
            reference_substitute(&view.graph, &overlay.identity_map)
        );
        assert_injective_mapping(&overlay.identity_map);
        assert_eq!(
            reference_substitute(&overlay.graph, &inverse_map(&overlay.identity_map)),
            view.graph
        );
        assert!(
            overlay
                .identity_map
                .iter()
                .all(|(_, fresh)| !receiver.contains(fresh))
        );
        assert!(
            overlay
                .identity_map
                .iter()
                .all(|(_, fresh)| !view.graph.identities.contains(fresh))
        );
        assert!(overlay.identity_map.iter().all(|(_, fresh)| {
            view.identity_map
                .iter()
                .all(|(source, parent)| fresh != source && fresh != parent)
        }));
    }
    let first: HashSet<_> = overlays[0]
        .identity_map
        .iter()
        .map(|(_, fresh)| *fresh)
        .collect();
    let second: HashSet<_> = overlays[1]
        .identity_map
        .iter()
        .map(|(_, fresh)| *fresh)
        .collect();
    assert!(first.is_disjoint(&second));
}

#[test]
fn joint_graph_transport_keeps_cross_use_bounds_supplied_before_transport() {
    let source = sample_graph();
    let left = reference_substitute(
        &source,
        &[(Identity(1), Identity(10)), (Identity(2), Identity(11))],
    );
    let right = reference_substitute(
        &source,
        &[(Identity(1), Identity(20)), (Identity(2), Identity(21))],
    );
    let joint = reference_join(&left, &right);
    let joint_snapshot = joint.clone();
    let view = make_parent(
        &joint,
        &[Identity(10), Identity(11), Identity(20), Identity(21)],
        &[Identity(90)],
        &[Identity(400)],
        FaultInjection::default(),
    )
    .unwrap();

    let cross_use = joint.bounds.last().unwrap();
    let transported = view.graph.bounds.last().unwrap();
    assert_eq!(transported.lower, cross_use.lower);
    assert_eq!(transported.upper, cross_use.upper);
    assert_eq!(
        &view.graph.evidence[transported.evidence.clone()],
        &joint.evidence[cross_use.evidence.clone()]
    );
    assert_eq!(
        reference_substitute(&view.graph, &inverse_map(&view.identity_map)),
        joint
    );
    assert_injective_mapping(&view.identity_map);

    let use_a: HashSet<_> = [Identity(10), Identity(11)]
        .into_iter()
        .map(|source| {
            view.identity_map
                .iter()
                .find_map(|(from, to)| (*from == source).then_some(*to))
                .unwrap()
        })
        .collect();
    let use_b: HashSet<_> = [Identity(20), Identity(21)]
        .into_iter()
        .map(|source| {
            view.identity_map
                .iter()
                .find_map(|(from, to)| (*from == source).then_some(*to))
                .unwrap()
        })
        .collect();
    assert!(use_a.is_disjoint(&use_b));
    assert_eq!(joint, joint_snapshot);
}

#[test]
fn each_overlay_can_change_without_mutating_its_sibling_or_source() {
    let source = sample_graph();
    let source_snapshot = source.clone();
    let view = parent(&source);
    let mut overlays = make_uses(
        &view,
        &[vec![Identity(400)], vec![Identity(401)]],
        FaultInjection::default(),
    )
    .unwrap();
    let sibling_snapshot = overlays[1].clone();
    overlays[0].graph.terms[3] = Term::Atom(Atom::String);
    assert_eq!(overlays[1], sibling_snapshot);
    assert_eq!(source, source_snapshot);
    assert_eq!(view.graph.terms[3], Term::Atom(Atom::Int));
}

#[test]
fn invalid_partition_is_rejected_and_use_ids_avoid_source_namespaces() {
    let source = sample_graph();
    let source_snapshot = source.clone();
    assert_eq!(
        make_parent(
            &source,
            &[Identity(1), Identity(1)],
            &[Identity(90)],
            &[],
            FaultInjection::default(),
        ),
        Err(TransportError::DuplicateIdentity),
    );
    assert_eq!(source, source_snapshot);

    let view = parent(&source);
    // Isolated receiver: before source identities were reserved, the first
    // use reused source IDs 1 and 2.
    let receiver = vec![Identity(400)];
    let overlay = make_uses(&view, &[receiver.clone()], FaultInjection::default())
        .unwrap()
        .pop()
        .unwrap();
    assert!(
        overlay
            .identity_map
            .iter()
            .all(|(_, identity)| !receiver.contains(identity))
    );
    assert!(overlay.identity_map.iter().all(|(_, fresh)| {
        view.identity_map
            .iter()
            .all(|(source, parent)| fresh != source && fresh != parent)
    }));
}

#[test]
fn injected_allocation_failures_return_no_partial_graph() {
    let source = sample_graph();
    let source_snapshot = source.clone();
    assert_eq!(
        make_parent(
            &source,
            &[Identity(1), Identity(2)],
            &[Identity(90)],
            &[],
            FaultInjection::fail_at(AllocationLane::Terms),
        ),
        Err(TransportError::AllocationFailed(AllocationLane::Terms)),
    );
    assert_eq!(source, source_snapshot);

    let view = parent(&source);
    assert_eq!(
        make_uses(
            &view,
            &[vec![Identity(500)], vec![Identity(501)]],
            FaultInjection::fail_after(AllocationLane::Terms, 1),
        ),
        Err(TransportError::AllocationFailed(AllocationLane::Terms)),
    );
    assert_eq!(source, source_snapshot);
}
