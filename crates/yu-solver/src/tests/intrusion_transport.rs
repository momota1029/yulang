use std::collections::{HashMap, HashSet};

use crate::intrusion_transport::Term as GraphTerm;
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
fn incomplete_overlapping_and_unknown_partitions_are_rejected_atomically() {
    let source = sample_graph();
    let source_snapshot = source.clone();

    assert_eq!(
        make_parent(
            &source,
            &[Identity(1)],
            &[Identity(90)],
            &[],
            FaultInjection::default(),
        ),
        Err(TransportError::IncompletePartition),
    );
    assert_eq!(
        make_parent(
            &source,
            &[Identity(1), Identity(2)],
            &[Identity(2), Identity(90)],
            &[],
            FaultInjection::default(),
        ),
        Err(TransportError::DuplicateIdentity),
    );
    assert_eq!(
        make_parent(
            &source,
            &[Identity(1), Identity(999)],
            &[Identity(90)],
            &[],
            FaultInjection::default(),
        ),
        Err(TransportError::UnknownIdentity),
    );
    assert_eq!(source, source_snapshot);

    let view = parent(&source);
    assert_eq!(
        make_uses(
            &view,
            &[vec![Identity(300), Identity(300)]],
            FaultInjection::default(),
        ),
        Err(TransportError::DuplicateIdentity),
    );
    assert_eq!(source, source_snapshot);
}

#[test]
fn every_explicit_fault_point_returns_no_partial_transport() {
    let source = sample_graph();
    let source_snapshot = source.clone();
    let parent_lanes = [
        AllocationLane::Identities,
        AllocationLane::Terms,
        AllocationLane::Bounds,
        AllocationLane::Evidence,
    ];

    for lane in parent_lanes {
        let mut saw_failure = false;
        let mut reached_success = false;
        for skip in 0..64 {
            match make_parent(
                &source,
                &[Identity(1), Identity(2)],
                &[Identity(90)],
                &[],
                FaultInjection::fail_after(lane, skip),
            ) {
                Err(TransportError::AllocationFailed(observed)) => {
                    assert_eq!(observed, lane);
                    saw_failure = true;
                }
                Ok(view) => {
                    assert_eq!(
                        view.graph,
                        reference_substitute(&source, &view.identity_map)
                    );
                    reached_success = true;
                    break;
                }
                Err(other) => panic!("unexpected parent transport error: {other:?}"),
            }
            assert_eq!(source, source_snapshot);
        }
        assert!(saw_failure, "allocation lane {lane:?} was never injected");
        assert!(reached_success, "allocation lane {lane:?} did not converge");
    }

    let view = parent(&source);
    let receivers = [vec![Identity(500)], vec![Identity(501)]];
    let use_lanes = [
        AllocationLane::Identities,
        AllocationLane::Terms,
        AllocationLane::Bounds,
        AllocationLane::Evidence,
        AllocationLane::UseViews,
    ];

    for lane in use_lanes {
        let mut saw_failure = false;
        let mut reached_success = false;
        for skip in 0..64 {
            match make_uses(&view, &receivers, FaultInjection::fail_after(lane, skip)) {
                Err(TransportError::AllocationFailed(observed)) => {
                    assert_eq!(observed, lane);
                    saw_failure = true;
                }
                Ok(overlays) => {
                    assert_eq!(overlays.len(), receivers.len());
                    for overlay in &overlays {
                        assert_eq!(
                            overlay.graph,
                            reference_substitute(&view.graph, &overlay.identity_map)
                        );
                    }
                    reached_success = true;
                    break;
                }
                Err(other) => panic!("unexpected use transport error: {other:?}"),
            }
            assert_eq!(source, source_snapshot);
            assert_eq!(view, parent(&source));
        }
        assert!(saw_failure, "allocation lane {lane:?} was never injected");
        assert!(reached_success, "allocation lane {lane:?} did not converge");
    }

    // Three identity-lane checks build one use overlay. Failure at the next
    // check happens while constructing the second overlay; no first overlay
    // escapes through the Result.
    assert_eq!(
        make_uses(
            &view,
            &receivers,
            FaultInjection::fail_after(AllocationLane::Identities, 3),
        ),
        Err(TransportError::AllocationFailed(AllocationLane::Identities)),
    );
    assert_eq!(source, source_snapshot);
    assert_eq!(view, parent(&source));
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

// This bridge observes one closed scheme only. Its identity namespace belongs
// to this export, not to bare Q/R ordinals or to a successor classification.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum SchemeNode {
    Positive(yu_types::PositiveValueId),
    Negative(yu_types::NegativeValueId),
    PositiveEffect(yu_types::PositiveEffectId),
    NegativeEffect(yu_types::NegativeEffectId),
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum SchemeBinder {
    Quantified(yu_types::QuantifierId),
    Recursive(yu_types::RecursiveBinderId),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SchemeExportError {
    Lookup,
    UnsupportedUnion,
    UnsupportedIntersection,
    NodeLimit,
}

struct ExportedScheme<'a> {
    // Retaining the exact source view qualifies every sidecar binder key.
    source: yu_types::ClosedValueSchemeView<'a>,
    graph: Graph,
    nodes: HashMap<SchemeNode, TermId>,
    binders: HashMap<SchemeBinder, Identity>,
    recursive_bounds: Vec<(SchemeBinder, usize)>,
}

fn export_scheme(
    source: yu_types::ClosedValueSchemeView<'_>,
) -> Result<ExportedScheme<'_>, SchemeExportError> {
    use yu_types::{NegativeValueView as N, PositiveValueView as P};
    let mut exported = ExportedScheme {
        source,
        graph: Graph {
            terms: Vec::new(),
            bounds: Vec::new(),
            evidence: Vec::new(),
            identities: Vec::new(),
            root: TermId(0),
        },
        nodes: HashMap::new(),
        binders: HashMap::new(),
        recursive_bounds: Vec::new(),
    };
    let mut pending = Vec::new();
    fn intern(
        exported: &mut ExportedScheme<'_>,
        pending: &mut Vec<SchemeNode>,
        node: SchemeNode,
    ) -> Result<TermId, SchemeExportError> {
        if let Some(&id) = exported.nodes.get(&node) {
            return Ok(id);
        }
        // A fixed envelope for this small research fixture; never truncate.
        if exported.nodes.len() == 256 {
            return Err(SchemeExportError::NodeLimit);
        }
        let id = TermId(exported.graph.terms.len());
        exported.nodes.insert(node, id);
        exported.graph.terms.push(GraphTerm::Bottom);
        pending.push(node);
        Ok(id)
    }
    fn binder(exported: &mut ExportedScheme<'_>, key: SchemeBinder) -> Identity {
        if let Some(&identity) = exported.binders.get(&key) {
            return identity;
        }
        let identity = Identity(exported.binders.len() as u32);
        exported.binders.insert(key, identity);
        exported.graph.identities.push(identity);
        identity
    }
    // Public IDs are obtained from occurrences. Reject unused Q declarations
    // below rather than silently omitting identities we cannot obtain.
    exported.graph.root = intern(
        &mut exported,
        &mut pending,
        SchemeNode::Positive(source.predicate()),
    )?;
    for bound in source.recursive_bounds() {
        let key = SchemeBinder::Recursive(bound.binder());
        binder(&mut exported, key);
        let yu_types::NeutralValueView::Bounds { lower, upper } = source
            .neutral_value(bound.bounds())
            .map_err(|_| SchemeExportError::Lookup)?;
        let lower = intern(&mut exported, &mut pending, SchemeNode::Positive(lower))?;
        let upper = intern(&mut exported, &mut pending, SchemeNode::Negative(upper))?;
        exported
            .recursive_bounds
            .push((key, exported.graph.bounds.len()));
        // The closed view exposes no provenance. Empty evidence means absent
        // evidence, never a certification of successor evidence validity.
        exported.graph.bounds.push(Bound {
            lower,
            upper,
            evidence: 0..0,
        });
    }
    while let Some(node) = pending.pop() {
        let term = match node {
            SchemeNode::Positive(id) => match source
                .positive_value(id)
                .map_err(|_| SchemeExportError::Lookup)?
            {
                P::Bottom => GraphTerm::Bottom,
                P::Int => GraphTerm::Atom(Atom::Int),
                P::Unit => GraphTerm::Atom(Atom::Unit),
                P::Quantified(q) => {
                    GraphTerm::Variable(binder(&mut exported, SchemeBinder::Quantified(q)))
                }
                P::Recursive(r) => {
                    GraphTerm::Variable(binder(&mut exported, SchemeBinder::Recursive(r)))
                }
                P::Union(_) => return Err(SchemeExportError::UnsupportedUnion),
                P::Function {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } => GraphTerm::Function {
                    argument: intern(&mut exported, &mut pending, SchemeNode::Negative(argument))?,
                    argument_effect: intern(
                        &mut exported,
                        &mut pending,
                        SchemeNode::NegativeEffect(argument_effect),
                    )?,
                    result_effect: intern(
                        &mut exported,
                        &mut pending,
                        SchemeNode::PositiveEffect(result_effect),
                    )?,
                    result: intern(&mut exported, &mut pending, SchemeNode::Positive(result))?,
                },
            },
            SchemeNode::Negative(id) => match source
                .negative_value(id)
                .map_err(|_| SchemeExportError::Lookup)?
            {
                N::Top => GraphTerm::Top,
                N::Bottom => GraphTerm::Bottom,
                N::Int => GraphTerm::Atom(Atom::Int),
                N::Unit => GraphTerm::Atom(Atom::Unit),
                N::Quantified(q) => {
                    GraphTerm::Variable(binder(&mut exported, SchemeBinder::Quantified(q)))
                }
                N::Recursive(r) => {
                    GraphTerm::Variable(binder(&mut exported, SchemeBinder::Recursive(r)))
                }
                N::Intersection(_) => return Err(SchemeExportError::UnsupportedIntersection),
                N::Function {
                    argument,
                    argument_effect,
                    result_effect,
                    result,
                } => GraphTerm::Function {
                    argument: intern(&mut exported, &mut pending, SchemeNode::Positive(argument))?,
                    argument_effect: intern(
                        &mut exported,
                        &mut pending,
                        SchemeNode::PositiveEffect(argument_effect),
                    )?,
                    result_effect: intern(
                        &mut exported,
                        &mut pending,
                        SchemeNode::NegativeEffect(result_effect),
                    )?,
                    result: intern(&mut exported, &mut pending, SchemeNode::Negative(result))?,
                },
            },
            SchemeNode::PositiveEffect(id) => match source
                .positive_effect(id)
                .map_err(|_| SchemeExportError::Lookup)?
            {
                yu_types::PositiveEffectView::Bottom => GraphTerm::Bottom,
            },
            SchemeNode::NegativeEffect(id) => match source
                .negative_effect(id)
                .map_err(|_| SchemeExportError::Lookup)?
            {
                yu_types::NegativeEffectView::Empty => GraphTerm::Top,
            },
        };
        exported.graph.terms[exported.nodes[&node].0] = term;
    }
    if exported
        .binders
        .keys()
        .filter(|key| matches!(key, SchemeBinder::Quantified(_)))
        .count()
        != source.quantifier_count() as usize
    {
        return Err(SchemeExportError::Lookup);
    }
    Ok(exported)
}

#[test]
fn real_identity_scheme_exports_all_ports_and_transports_supplied_partition() {
    use super::*;
    let hir = module(
        "my id x = x; my a = id; my b = id",
        "transport-real-scheme.yu",
    );
    assert!(hir.errors().is_empty());
    assert!(hir.diagnostics().is_empty());
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("expected identity binding");
    };
    let solved = SolvedModule::solve(collect(hir.clone())).unwrap();
    assert!(solved.errors().is_empty());
    let position = solved.root_scheme_positions[binding.definition_root()];
    let scheme = solved.schemes[position].as_ref().unwrap();
    let exported = export_scheme(solved.closed_types.scheme_view(scheme).unwrap()).unwrap();
    let yu_types::PositiveValueView::Function {
        argument,
        argument_effect,
        result_effect,
        result,
    } = exported
        .source
        .positive_value(exported.source.predicate())
        .unwrap()
    else {
        panic!("expected identity Function");
    };
    let ports = [
        SchemeNode::Negative(argument),
        SchemeNode::NegativeEffect(argument_effect),
        SchemeNode::PositiveEffect(result_effect),
        SchemeNode::Positive(result),
    ];
    let ids = ports.map(|node| exported.nodes[&node]);
    assert_eq!(
        exported.graph.terms[exported.graph.root.0],
        GraphTerm::Function {
            argument: ids[0],
            argument_effect: ids[1],
            result_effect: ids[2],
            result: ids[3],
        }
    );
    assert_eq!(
        exported.graph.terms[ids[0].0],
        exported.graph.terms[ids[3].0]
    );
    assert!(matches!(
        exported.graph.terms[ids[0].0],
        GraphTerm::Variable(_)
    ));
    assert_eq!(exported.graph.terms[ids[1].0], GraphTerm::Top);
    assert_eq!(exported.graph.terms[ids[2].0], GraphTerm::Bottom);
    assert_eq!(exported.nodes.len(), exported.graph.terms.len());
    assert_eq!(exported.binders.len(), 1);
    assert!(exported.recursive_bounds.is_empty());
    // Experimental supplied premise: this test elects all exported identities
    // local. Current Q/R membership does not establish successor eligibility.
    let locals = exported.graph.identities.clone();
    let anchors = Vec::new();
    let snapshot = exported.graph.clone();
    let parent = make_parent(
        &exported.graph,
        &locals,
        &anchors,
        &[Identity(100)],
        FaultInjection::default(),
    )
    .unwrap();
    let receivers = [vec![Identity(200)], vec![Identity(201)]];
    let mut uses = make_uses(&parent, &receivers, FaultInjection::default()).unwrap();
    assert_eq!(
        parent.graph,
        reference_substitute(&snapshot, &parent.identity_map)
    );
    let mut seen = HashSet::new();
    for overlay in &uses {
        assert_eq!(
            overlay.graph,
            reference_substitute(&parent.graph, &overlay.identity_map)
        );
        assert_eq!(
            reference_substitute(&overlay.graph, &inverse_map(&overlay.identity_map)),
            parent.graph
        );
        for (_, fresh) in &overlay.identity_map {
            assert!(seen.insert(*fresh));
            assert!(!snapshot.identities.contains(fresh));
            assert!(!parent.graph.identities.contains(fresh));
            assert!(!receivers.iter().flatten().any(|identity| identity == fresh));
        }
    }
    let sibling = uses[1].clone();
    uses[0].graph.terms[ids[3].0] = GraphTerm::Atom(Atom::Int);
    assert_eq!(uses[1], sibling);
    assert_eq!(exported.graph, snapshot);
}

#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
#[test]
fn retained_source_use_captures_supply_receiver_namespaces_for_exported_transport() {
    use super::*;
    use crate::shadow_f5::{FreshBinderRef, FreshCaptureState, FreshRowRef};
    use crate::shadow_scc::PendingUseInstantiationPremise;

    let hir = module(
        "my id x = x; my a = id; my b = id",
        "transport-retained-captures.yu",
    );
    assert!(hir.errors().is_empty());
    assert!(hir.diagnostics().is_empty());
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("expected identity binding");
    };
    let batch = collect(hir.clone());
    let ordinary = SolvedModule::solve(batch.clone()).unwrap();
    let solved = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
    assert_eq!(ordinary.errors(), solved.errors());
    for occurrence in ordinary.occurrences() {
        assert_eq!(
            ordinary.projection_for(occurrence),
            solved.projection_for(occurrence)
        );
    }
    assert!(solved.errors().is_empty());
    let topology = batch.shadow_scc_topology();
    let occurrences = topology
        .components()
        .flat_map(|component| component.incoming_uses())
        .collect::<Vec<_>>();
    assert_eq!(occurrences.len(), 2);
    assert!(!occurrences[0].same_identity(occurrences[1]));
    let pending = occurrences
        .iter()
        .map(|occurrence| {
            topology
                .pending_use_instantiation(&solved, *occurrence)
                .unwrap()
        })
        .collect::<Vec<_>>();
    let target = pending[0].current_scheme();
    assert_eq!(target.owner(), binding.definition_root());
    assert!(target.same_identity(pending[1].current_scheme()));
    let exported = export_scheme(target.endpoints()).unwrap();
    assert!(!exported.binders.is_empty());

    // Tokens represent opaque historical row identities only. No numeric live
    // row ID is observed, and no token claims a successor semantic identity.
    let mut row_tokens: Vec<(FreshRowRef<'_>, Identity)> = Vec::new();
    let mut receivers = Vec::new();
    for use_pending in &pending {
        assert!(use_pending.current_scheme().same_identity(target));
        let FreshCaptureState::Captured(capture) = use_pending.current_fresh_capture() else {
            panic!("each successful source use must retain its complete capture");
        };
        assert!(capture.scheme().same_identity(target));
        let mut matched = HashSet::new();
        let mut receiver = Vec::new();
        for (binder, row) in capture.bindings() {
            // Ordinals are compared only after establishing the exact scheme
            // owner shared by the capture and this export's source view.
            let key = match binder {
                FreshBinderRef::Quantified(q) => {
                    assert!(q.scheme().same_identity(target));
                    *exported
                        .binders
                        .keys()
                        .find(|key| {
                            matches!(key,
                                SchemeBinder::Quantified(id) if id.ordinal() == q.ordinal()
                            )
                        })
                        .expect("captured Q must occur in the exact export sidecar")
                }
                FreshBinderRef::Recursive(r) => {
                    assert!(r.scheme().same_identity(target));
                    *exported
                        .binders
                        .keys()
                        .find(|key| {
                            matches!(key,
                                SchemeBinder::Recursive(id) if id.ordinal() == r.ordinal()
                            )
                        })
                        .expect("captured R must occur in the exact export sidecar")
                }
            };
            assert!(matched.insert(key), "capture must cover each binder once");
            let token = if let Some((_, token)) = row_tokens
                .iter()
                .find(|(previous, _)| row.same_identity(*previous))
            {
                *token
            } else {
                let token = Identity(100 + u32::try_from(row_tokens.len()).unwrap());
                assert!(!exported.graph.identities.contains(&token));
                row_tokens.push((row, token));
                token
            };
            assert!(
                !receiver.contains(&token),
                "distinct binders need distinct rows"
            );
            receiver.push(token);
        }
        assert_eq!(matched.len(), exported.binders.len());
        receivers.push(receiver);
    }
    assert!(
        receivers[0]
            .iter()
            .all(|token| !receivers[1].contains(token))
    );
    let all_receivers = receivers.iter().flatten().copied().collect::<Vec<_>>();
    // Experimental supplied partition: elect all exported identities local.
    // Current Q/R capture does not justify successor local/anchor classification.
    let snapshot = exported.graph.clone();
    let parent = make_parent(
        &exported.graph,
        &exported.graph.identities,
        &[],
        &all_receivers,
        FaultInjection::default(),
    )
    .unwrap();
    assert_eq!(
        parent.graph,
        reference_substitute(&snapshot, &parent.identity_map)
    );
    let overlays = make_uses(&parent, &receivers, FaultInjection::default()).unwrap();
    assert_eq!(overlays.len(), 2);
    assert_eq!(
        parent.graph,
        reference_substitute(&snapshot, &parent.identity_map)
    );
    let mut fresh = HashSet::new();
    for overlay in &overlays {
        assert_injective_mapping(&overlay.identity_map);
        assert_eq!(
            overlay.graph,
            reference_substitute(&parent.graph, &overlay.identity_map)
        );
        for (_, token) in &overlay.identity_map {
            assert!(fresh.insert(*token));
            assert!(!all_receivers.contains(token));
            assert!(!snapshot.identities.contains(token));
            assert!(!parent.graph.identities.contains(token));
        }
    }
    assert_eq!(exported.graph, snapshot);
    // Executing transport promotes neither pending semantic premise nor the
    // opaque bound evidence into current-type or successor correctness evidence.
    for use_pending in pending {
        assert_eq!(
            use_pending.qr_correspondence_premise(),
            PendingUseInstantiationPremise::CurrentToSuccessorQrCorrespondenceUnresolved
        );
        assert_eq!(
            use_pending.shared_contract_transport_premise(),
            PendingUseInstantiationPremise::UseTimeSharedContractTransportUnresolved
        );
    }
}

#[cfg(all(feature = "shadow-f5", feature = "shadow-scc-observer"))]
#[test]
fn retained_recursive_uses_export_and_freshen_r_binders() {
    use super::*;
    use crate::shadow_f5::{FreshBinderRef, FreshCaptureState, FreshRowRef};

    let hir = module(
        "my f x = g; my g y = f; my a = f; my b = f",
        "transport-retained-recursive-captures.yu",
    );
    assert!(hir.errors().is_empty());
    assert!(hir.diagnostics().is_empty());
    let HirItem::Binding(binding) = &hir.items()[0] else {
        panic!("expected first recursive binding");
    };
    let batch = collect(hir.clone());
    let ordinary = SolvedModule::solve(batch.clone()).unwrap();
    let solved = SolvedModule::solve_with_shadow_fresh_capture(batch.clone()).unwrap();
    assert_eq!(ordinary.errors(), solved.errors());
    for occurrence in ordinary.occurrences() {
        assert_eq!(
            ordinary.projection_for(occurrence),
            solved.projection_for(occurrence)
        );
    }
    assert!(solved.errors().is_empty());
    let topology = batch.shadow_scc_topology();
    let occurrences = topology
        .components()
        .flat_map(|component| component.incoming_uses())
        .collect::<Vec<_>>();
    let pending = occurrences
        .iter()
        .filter_map(|occurrence| {
            let use_pending = topology
                .pending_use_instantiation(&solved, *occurrence)
                .unwrap();
            (use_pending.current_scheme().owner() == binding.definition_root())
                .then_some(use_pending)
        })
        .collect::<Vec<_>>();
    assert!(pending.len() >= 2, "expected multiple uses of recursive f");
    let target = pending[0].current_scheme();
    let ordinary_target = ordinary
        .shadow_closed_schemes()
        .for_root(binding.definition_root())
        .unwrap();
    assert!(ordinary_target.endpoints().alpha_eq(target.endpoints()));
    assert!(
        pending
            .iter()
            .all(|use_pending| use_pending.current_scheme().same_identity(target))
    );
    let exported = export_scheme(target.endpoints()).unwrap();
    assert!(
        exported
            .binders
            .keys()
            .any(|binder| matches!(binder, SchemeBinder::Recursive(_)))
    );
    assert!(!exported.recursive_bounds.is_empty());

    let mut row_tokens: Vec<(FreshRowRef<'_>, Identity)> = Vec::new();
    let mut receivers = Vec::new();
    for use_pending in &pending {
        let FreshCaptureState::Captured(capture) = use_pending.current_fresh_capture() else {
            panic!("each successful recursive source use must retain its capture");
        };
        assert!(capture.scheme().same_identity(target));
        let mut matched = HashSet::new();
        let mut receiver = Vec::new();
        for (binder, row) in capture.bindings() {
            let key = match binder {
                FreshBinderRef::Quantified(q) => {
                    assert!(q.scheme().same_identity(target));
                    *exported
                        .binders
                        .keys()
                        .find(|key| {
                            matches!(key,
                            SchemeBinder::Quantified(id) if id.ordinal() == q.ordinal())
                        })
                        .expect("captured Q must occur in the exact recursive export")
                }
                FreshBinderRef::Recursive(r) => {
                    assert!(r.scheme().same_identity(target));
                    *exported
                        .binders
                        .keys()
                        .find(|key| {
                            matches!(key,
                            SchemeBinder::Recursive(id) if id.ordinal() == r.ordinal())
                        })
                        .expect("captured R must occur in the exact recursive export")
                }
            };
            assert!(
                matched.insert(key),
                "capture must cover each Q/R binder once"
            );
            let token = row_tokens
                .iter()
                .find(|(known, _)| row.same_identity(*known))
                .map(|(_, token)| *token)
                .unwrap_or_else(|| {
                    let token = Identity(100 + u32::try_from(row_tokens.len()).unwrap());
                    row_tokens.push((row, token));
                    token
                });
            receiver.push(token);
        }
        assert_eq!(matched.len(), exported.binders.len());
        receivers.push(receiver);
    }
    let mut receiver_ids = HashSet::new();
    for receiver in &receivers {
        assert!(
            receiver
                .iter()
                .all(|identity| receiver_ids.insert(*identity))
        );
    }
    let snapshot = exported.graph.clone();
    let parent = make_parent(
        &snapshot,
        &snapshot.identities,
        &[],
        &receiver_ids.iter().copied().collect::<Vec<_>>(),
        FaultInjection::default(),
    )
    .unwrap();
    assert_injective_mapping(&parent.identity_map);
    assert_eq!(
        parent.graph,
        reference_substitute(&snapshot, &parent.identity_map)
    );
    assert_eq!(
        reference_substitute(&parent.graph, &inverse_map(&parent.identity_map)),
        snapshot
    );
    for (_, fresh) in &parent.identity_map {
        assert!(!receiver_ids.contains(fresh));
        assert!(!snapshot.identities.contains(fresh));
    }
    let overlays = make_uses(&parent, &receivers, FaultInjection::default()).unwrap();
    assert_eq!(overlays.len(), pending.len());
    let mut fresh_ids = HashSet::new();
    for overlay in &overlays {
        assert_eq!(
            overlay.graph,
            reference_substitute(&parent.graph, &overlay.identity_map)
        );
        for (_, fresh) in &overlay.identity_map {
            assert!(fresh_ids.insert(*fresh));
            assert!(!receiver_ids.contains(fresh));
            assert!(!snapshot.identities.contains(fresh));
            assert!(!parent.graph.identities.contains(fresh));
        }
    }
    assert_eq!(exported.graph, snapshot);
}

#[test]
fn scheme_export_rejects_union_and_intersection_without_partial_graph() {
    let mut session = yu_types::ClosedTypeFinalizationSession::try_new().unwrap();
    let union = session
        .finalize_scheme(|f| {
            let int = f.positive_int()?;
            let bottom = f.positive_bottom()?;
            let root = f.positive_union(&[int, bottom])?;
            f.set_scheme(0, &[], root)
        })
        .unwrap()
        .into_parts()
        .0;
    assert!(matches!(
        export_scheme(session.scheme_view(&union).unwrap()),
        Err(SchemeExportError::UnsupportedUnion)
    ));
    let intersection = session
        .finalize_scheme(|f| {
            let int = f.negative_int()?;
            let top = f.negative_top()?;
            let argument = f.negative_intersection(&[int, top])?;
            let ae = f.negative_effect_empty()?;
            let re = f.positive_effect_bottom()?;
            let result = f.positive_int()?;
            let root = f.positive_function(argument, ae, re, result)?;
            f.set_scheme(0, &[], root)
        })
        .unwrap()
        .into_parts()
        .0;
    assert!(matches!(
        export_scheme(session.scheme_view(&intersection).unwrap()),
        Err(SchemeExportError::UnsupportedIntersection)
    ));
}

#[test]
fn scheme_export_retains_recursive_bound_associations_and_shared_references() {
    let mut session = yu_types::ClosedTypeFinalizationSession::try_new().unwrap();
    let scheme = session
        .finalize_scheme(|f| {
            let r = f.recursive_binder(0);
            let recursive = f.positive_recursive(r)?;
            let argument = f.negative_recursive(r)?;
            let ae = f.negative_effect_empty()?;
            let re = f.positive_effect_bottom()?;
            let root = f.positive_function(argument, ae, re, recursive)?;
            let endpoints = f.neutral_bounds(root, argument)?;
            let bound = f.recursive_bound(r, endpoints)?;
            f.set_scheme(0, &[bound], root)
        })
        .unwrap()
        .into_parts()
        .0;
    let exported = export_scheme(session.scheme_view(&scheme).unwrap()).unwrap();
    let bound = exported.source.recursive_bounds()[0];
    let key = SchemeBinder::Recursive(bound.binder());
    assert_eq!(exported.recursive_bounds, [(key, 0)]);
    assert_eq!(exported.graph.bounds.len(), 1);
    assert_eq!(exported.graph.bounds[0].lower, exported.graph.root);
    let GraphTerm::Function {
        argument, result, ..
    } = exported.graph.terms[exported.graph.root.0]
    else {
        panic!("expected recursive Function");
    };
    assert_eq!(exported.graph.bounds[0].upper, argument);
    assert_eq!(
        exported.graph.terms[argument.0],
        GraphTerm::Variable(exported.binders[&key])
    );
    assert_eq!(
        exported.graph.terms[result.0],
        GraphTerm::Variable(exported.binders[&key])
    );
    // The sidecar links that shared identity to its ordered bound, preserving
    // regular recursion without expanding the binder's body indefinitely.
    let locals = exported.graph.identities.clone(); // supplied experimental premise
    let parent = make_parent(
        &exported.graph,
        &locals,
        &[],
        &[],
        FaultInjection::default(),
    )
    .unwrap();
    let overlays = make_uses(&parent, &[vec![], vec![]], FaultInjection::default()).unwrap();
    for overlay in &overlays {
        assert_eq!(overlay.graph.bounds, exported.graph.bounds);
        let renamed_parent = parent
            .identity_map
            .iter()
            .find(|(from, _)| *from == exported.binders[&key])
            .unwrap()
            .1;
        let renamed_use = overlay
            .identity_map
            .iter()
            .find(|(from, _)| *from == renamed_parent)
            .unwrap()
            .1;
        assert_eq!(
            overlay.graph.terms[argument.0],
            GraphTerm::Variable(renamed_use)
        );
        assert_eq!(
            overlay.graph.terms[result.0],
            GraphTerm::Variable(renamed_use)
        );
        assert_eq!(
            reference_substitute(&overlay.graph, &inverse_map(&overlay.identity_map)),
            parent.graph
        );
    }
    assert_ne!(overlays[0].identity_map, overlays[1].identity_map);
}
