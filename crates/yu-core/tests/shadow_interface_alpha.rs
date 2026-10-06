#![cfg(feature = "shadow")]

use yu_core::shadow_interface_alpha::*;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Rigid {
    Literal(&'static str),
    BinderMode(&'static str),
    Scope(u32),
    SourceOrigin(u32),
    Direction(&'static str),
    ProviderProtection(bool),
    Primitive(&'static str),
    ExternalContext(u32),
}

type Graph = Presentation<&'static str, Rigid>;

fn graph() -> Graph {
    Graph {
        context: vec![Rigid::ExternalContext(17), Rigid::Primitive("call")],
        exports: vec![Field::Local(0), Field::Local(2)],
        nodes: vec![
            Node {
                sort: "binder",
                fields: vec![
                    Field::Rigid(Rigid::BinderMode("eligible")),
                    Field::Rigid(Rigid::Scope(3)),
                    Field::Rigid(Rigid::SourceOrigin(41)),
                    Field::Local(1),
                    Field::Local(2),
                ],
            },
            Node {
                sort: "port",
                fields: vec![
                    Field::Rigid(Rigid::Direction("upper")),
                    Field::Rigid(Rigid::ProviderProtection(true)),
                    Field::Local(2),
                    Field::Local(0),
                ],
            },
            Node {
                sort: "port",
                fields: vec![
                    Field::Rigid(Rigid::Literal("result")),
                    Field::Local(1),
                    Field::Local(1),
                ],
            },
        ],
    }
}

// Independent fixture relabeling, preserving every occurrence and ordered field.
fn relabel(p: &Graph, map: &[usize]) -> Graph {
    fn field(f: &Field<Rigid>, map: &[usize]) -> Field<Rigid> {
        match f {
            Field::Rigid(value) => Field::Rigid(value.clone()),
            Field::Local(id) => Field::Local(map[*id]),
        }
    }
    let mut output = p.clone();
    output.exports = p.exports.iter().map(|f| field(f, map)).collect();
    for (id, node) in p.nodes.iter().enumerate() {
        output.nodes[map[id]] = Node {
            sort: node.sort,
            fields: node.fields.iter().map(|f| field(f, map)).collect(),
        };
    }
    output
}

#[test]
fn cyclic_alpha_graph_returns_actual_bijection_and_verified_inverse() {
    let left = graph();
    let right = relabel(&left, &[2, 0, 1]);
    let Comparison::StructurallyAlphaEqual(certificate) = compare(&left, &right, 2).unwrap() else {
        panic!("expected alpha certificate")
    };
    assert_eq!(certificate.left_to_right, vec![2, 0, 1]);
    assert_eq!(certificate.right_to_left, vec![1, 2, 0]);
    assert_eq!(verify_certificate(&left, &right, &certificate), Ok(true));
    let inverse = AlphaCertificate {
        left_to_right: certificate.right_to_left.clone(),
        right_to_left: certificate.left_to_right.clone(),
    };
    assert_eq!(verify_certificate(&right, &left, &inverse), Ok(true));
    let Canonicalization::Completed(completed) = canonicalize(&left, 2).unwrap() else {
        panic!("expected complete search")
    };
    assert_eq!(completed.examined_candidates, 2);
    assert_eq!(completed.canonical.presentation().nodes[0].sort, "binder");
    let mut corrupt = certificate.clone();
    corrupt.right_to_left[0] = 0;
    assert_eq!(verify_certificate(&left, &right, &corrupt), Ok(false));
    corrupt.left_to_right[0] = usize::MAX;
    assert_eq!(verify_certificate(&left, &right, &corrupt), Ok(false));
    corrupt.left_to_right = vec![0, 0, 0];
    assert_eq!(verify_certificate(&left, &right, &corrupt), Ok(false));
}

#[test]
fn every_supplied_observable_and_ordered_operand_is_retained() {
    let original = graph();
    let changes = [
        (0, 0, Field::Rigid(Rigid::BinderMode("import"))),
        (0, 1, Field::Rigid(Rigid::Scope(4))),
        (0, 2, Field::Rigid(Rigid::SourceOrigin(42))),
        (1, 0, Field::Rigid(Rigid::Direction("lower"))),
        (1, 1, Field::Rigid(Rigid::ProviderProtection(false))),
        // A rigid literal must never be interpreted as a local reference.
        (2, 1, Field::Rigid(Rigid::Literal("1"))),
    ];
    for (node, field, replacement) in changes {
        let mut changed = original.clone();
        changed.nodes[node].fields[field] = replacement;
        assert_eq!(
            compare(&original, &changed, 2),
            Ok(Comparison::StructurallyDifferent)
        );
    }
    let mut changed = original.clone();
    changed.nodes[0].fields.swap(3, 4);
    assert_eq!(
        compare(&original, &changed, 2),
        Ok(Comparison::StructurallyDifferent)
    );
    changed = original.clone();
    changed.exports.swap(0, 1);
    assert_eq!(
        compare(&original, &changed, 2),
        Ok(Comparison::StructurallyDifferent)
    );
    changed = original.clone();
    changed.context[0] = Rigid::ExternalContext(18);
    assert_eq!(
        compare(&original, &changed, 2),
        Ok(Comparison::StructurallyDifferent)
    );
    changed = original.clone();
    changed.context.swap(0, 1);
    assert_eq!(
        compare(&original, &changed, 2),
        Ok(Comparison::StructurallyDifferent)
    );
    changed = original.clone();
    changed.nodes[0].sort = "port";
    assert_eq!(
        compare(&original, &changed, 6),
        Ok(Comparison::StructurallyDifferent)
    );
}

#[test]
fn sharing_is_not_unfolded_or_collapsed_into_identical_split_nodes() {
    let shared = Presentation {
        context: vec![],
        exports: vec![Field::Local(0)],
        nodes: vec![
            Node {
                sort: "root",
                fields: vec![Field::Local(1), Field::Local(1)],
            },
            Node {
                sort: "leaf",
                fields: vec![Field::Rigid(Rigid::Literal("same"))],
            },
        ],
    };
    let mut split = shared.clone();
    split.nodes.push(shared.nodes[1].clone());
    split.nodes[0].fields[1] = Field::Local(2);
    assert_eq!(
        compare(&shared, &split, 2),
        Ok(Comparison::StructurallyDifferent)
    );
    // Same node count but a different alias pattern is also distinguished.
    let mut same_count = split.clone();
    same_count.nodes[0].fields[1] = Field::Local(1);
    assert_eq!(
        compare(&same_count, &split, 2),
        Ok(Comparison::StructurallyDifferent)
    );
}

#[test]
fn partial_search_and_node_limit_never_publish_a_difference_or_certificate() {
    let p = graph();
    assert_eq!(
        canonicalize(&p, 0),
        Ok(Canonicalization::Exhausted(Exhaustion::CandidateBudget {
            examined: 0,
            budget: 0
        }))
    );
    assert_eq!(
        compare(&p, &p, 1),
        Ok(Comparison::Exhausted {
            side: Side::Left,
            reason: Exhaustion::CandidateBudget {
                examined: 1,
                budget: 1
            },
        })
    );
    let mut larger = p.clone();
    while larger.nodes.len() <= MAX_LOCAL_NODES {
        larger.nodes.push(p.nodes[2].clone());
    }
    assert_eq!(
        canonicalize(&larger, usize::MAX),
        Ok(Canonicalization::Exhausted(Exhaustion::NodeLimit {
            node_count: 9,
            limit: 8
        }))
    );
    // A complete left search must not mask an exhausted right search.
    let mut right = p.clone();
    right.nodes[0].sort = "port";
    assert_eq!(
        compare(&p, &right, 2),
        Ok(Comparison::Exhausted {
            side: Side::Right,
            reason: Exhaustion::CandidateBudget {
                examined: 2,
                budget: 2
            },
        })
    );
}

#[test]
fn malformed_references_are_errors_before_resource_statuses() {
    let p = graph();
    let mut bad = p.clone();
    bad.exports.push(Field::Local(3));
    assert_eq!(
        canonicalize(&bad, 0),
        Err(InvalidReference {
            site: ReferenceSite::Export { field: 2 },
            target: 3,
            node_count: 3,
        })
    );
    bad = p.clone();
    bad.nodes[2].fields.push(Field::Local(usize::MAX));
    let error = InvalidReference {
        site: ReferenceSite::Node { node: 2, field: 3 },
        target: usize::MAX,
        node_count: 3,
    };
    assert_eq!(canonicalize(&bad, 0), Err(error.clone()));
    assert_eq!(
        compare(&p, &bad, 0),
        Err(InvalidInput {
            side: Side::Right,
            reference: error
        })
    );
    while bad.nodes.len() <= MAX_LOCAL_NODES {
        bad.nodes.push(p.nodes[2].clone());
    }
    assert!(canonicalize(&bad, 0).is_err());
}

#[test]
fn empty_graph_has_exactly_one_candidate_and_rigid_exports_still_matter() {
    let empty: Graph = Presentation {
        context: vec![],
        exports: vec![],
        nodes: vec![],
    };
    assert_eq!(
        canonicalize(&empty, 0),
        Ok(Canonicalization::Exhausted(Exhaustion::CandidateBudget {
            examined: 0,
            budget: 0
        }))
    );
    let Canonicalization::Completed(completed) = canonicalize(&empty, 1).unwrap() else {
        panic!("expected empty candidate")
    };
    assert_eq!(completed.examined_candidates, 1);
    assert!(completed.renaming.is_empty());
    let Comparison::StructurallyAlphaEqual(certificate) = compare(&empty, &empty, 1).unwrap()
    else {
        panic!("expected empty certificate")
    };
    assert_eq!(verify_certificate(&empty, &empty, &certificate), Ok(true));
    let mut rigid_export = empty.clone();
    rigid_export
        .exports
        .push(Field::Rigid(Rigid::Literal("export")));
    assert_eq!(
        compare(&empty, &rigid_export, 1),
        Ok(Comparison::StructurallyDifferent)
    );
}
