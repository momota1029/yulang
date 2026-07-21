use super::*;
use crate::constraints::explain::*;

#[test]
fn explains_root_and_unary_structure_in_stable_order() {
    let mut machine = ConstraintMachine::new();
    let origin = machine.alloc_source_boundary(ConstraintOriginKind::Annotation);
    let left = machine.alloc_pos(Pos::Con(vec!["left".into()], Vec::new()));
    let right = machine.alloc_pos(Pos::Con(vec!["right".into()], Vec::new()));
    let lower = machine.alloc_pos(Pos::Union(left, right));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.subtype(lower, upper, origin.origin());
    let child = machine
        .debug_constraint_record_id(left, ConstraintWeights::empty(), upper)
        .expect("union child record");

    let first = machine
        .why_constraint(child, ExplanationBudget::default())
        .unwrap();
    let second = machine
        .why_constraint(child, ExplanationBudget::default())
        .unwrap();

    assert_eq!(first, second, "insertion-order DFS is deterministic");
    assert_eq!(first.completeness, ExplanationCompleteness::Complete);
    assert_eq!(
        first.source_leaves,
        [ExplanationSourceLeaf {
            origin: origin.origin(),
            boundary: origin.boundary(),
            kind: ConstraintOriginKind::Annotation,
        }]
    );
    assert!(first.edges.iter().any(|edge| matches!(
        edge.kind,
        ExplanationEdgeKind::Structural(StructuralDerivationRule::UnionBranch { .. })
    )));
    assert!(
        first
            .edges
            .iter()
            .any(|edge| edge.kind == ExplanationEdgeKind::RootOrigin)
    );
}

#[test]
fn canonical_cycle_is_visited_once() {
    let mut machine = ConstraintMachine::new();
    let lower = machine.alloc_pos(Pos::Con(vec!["cycle-lower".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["cycle-upper".into()], Vec::new()));
    machine.subtype(lower, upper, OriginId::internal());
    let record = machine
        .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
        .unwrap();
    machine.constraint_records[record.0 as usize]
        .structural_derivations
        .push(StructuralDerivation {
            parent: record,
            rule: StructuralDerivationRule::UnionBranch {
                branch: StructuralIndex(0),
            },
        });

    let explanation = machine
        .why_constraint(record, ExplanationBudget::default())
        .unwrap();
    assert_eq!(explanation.completeness, ExplanationCompleteness::Complete);
    assert_eq!(
        explanation
            .nodes
            .iter()
            .filter(|node| node.id() == ExplanationNodeId::Constraint(record))
            .count(),
        1
    );
}

#[test]
fn explains_duplicate_bound_derivations_and_binary_replay() {
    let mut machine = ConstraintMachine::new();
    let first = machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    let second = machine
        .alloc_source_boundary(ConstraintOriginKind::Return)
        .origin();
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["lower".into()], Vec::new()));
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], first);
    let lower_record = match machine.events()[0] {
        ConstraintEvent::LowerBoundAdded { record, .. } => record,
        _ => panic!("lower event"),
    };
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], second);

    let duplicate = machine
        .why_lower_bound(pivot, lower_record, ExplanationBudget::default())
        .unwrap();
    assert_eq!(duplicate.source_leaves.len(), 2);
    assert_eq!(
        duplicate
            .edges
            .iter()
            .filter(|edge| matches!(edge.kind, ExplanationEdgeKind::Bound(_)))
            .count(),
        2
    );

    let upper = machine.alloc_neg(Neg::Con(vec!["upper".into()], Vec::new()));
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    machine.subtype(pivot_pos, upper, first);
    let result = machine
        .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
        .expect("replay result");
    let replay = machine
        .why_constraint(result, ExplanationBudget::default())
        .unwrap();
    let edge = replay
        .edges
        .iter()
        .find(|edge| matches!(edge.kind, ExplanationEdgeKind::BinaryReplay(_)))
        .expect("binary replay edge");
    assert_eq!(edge.parents.len(), 2);
    assert!(
        edge.parents
            .contains(&ExplanationNodeId::Bound(lower_record))
    );
}

#[test]
fn incomplete_storage_is_distinct_from_query_truncation() {
    let mut machine = ConstraintMachine::new();
    machine.set_replay_derivation_budget_for_test(0, usize::MAX);
    let origin = machine
        .alloc_source_boundary(ConstraintOriginKind::Annotation)
        .origin();
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["capped-lower".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["capped-upper".into()], Vec::new()));
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], origin);
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    machine.subtype(pivot_pos, upper, origin);
    let producer = machine
        .events()
        .iter()
        .find_map(|event| match event {
            ConstraintEvent::NominalCastNeeded { producer, .. } => Some(*producer),
            _ => None,
        })
        .expect("capped replay still emits its semantic result");
    machine.subtype(lower, upper, origin);

    let stored_incomplete = machine
        .why_constraint(producer, ExplanationBudget::default())
        .unwrap();
    assert_eq!(
        stored_incomplete.completeness,
        ExplanationCompleteness::IncompleteProvenance
    );
    assert_eq!(stored_incomplete.truncation, None);

    let also_truncated = machine
        .why_constraint(
            producer,
            ExplanationBudget {
                max_nodes: 4,
                max_edges: 0,
                max_depth: 4,
            },
        )
        .unwrap();
    assert_eq!(
        also_truncated.completeness,
        ExplanationCompleteness::TruncatedAndIncompleteProvenance
    );
    assert_eq!(
        also_truncated.truncation,
        Some(ExplanationTruncationReason::EdgeBudget { limit: 0 })
    );
}

#[test]
fn explains_unweighted_row_multi_parent_hyperedge() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let alias = TypeVar(1);
    let tail_var = TypeVar(2);
    let path = vec!["effect".into()];
    let item_pos = machine.alloc_pos(Pos::Con(path.clone(), Vec::new()));
    let row_pos = machine.alloc_pos(Pos::Row(vec![item_pos]));
    let item_neg = machine.alloc_neg(Neg::Con(path, Vec::new()));
    let alias_neg = machine.alloc_neg(Neg::Var(alias));
    let alias_pos = machine.alloc_pos(Pos::Var(alias));
    let source_neg = machine.alloc_neg(Neg::Var(source));
    let source_pos = machine.alloc_pos(Pos::Var(source));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let row_upper = machine.alloc_neg(Neg::Row(vec![item_neg], tail));
    let origin = OriginId::unknown_internal();

    machine.subtype(row_pos, alias_neg, origin);
    machine.subtype(alias_pos, source_neg, origin);
    machine.subtype(row_pos, source_neg, origin);
    machine.subtype(source_pos, row_upper, origin);

    let (record, aggregate) = machine
        .bounds
        .records
        .iter()
        .enumerate()
        .find_map(|(index, record)| {
            record
                .derivations
                .iter()
                .find_map(|derivation| match derivation {
                    BoundDerivation::Row(row)
                        if machine.row_derivations[row.0 as usize].rule
                            == RowDerivationRule::UnweightedReduction =>
                    {
                        Some((BoundRecordId(index as u32), *row))
                    }
                    _ => None,
                })
        })
        .expect("row-reduced upper bound");
    let explanation = machine
        .why_upper_bound(source, record, ExplanationBudget::default())
        .unwrap();
    let edge = explanation
        .edges
        .iter()
        .find(|edge| {
            edge.child == ExplanationNodeId::RowDerivation(aggregate)
                && edge.kind == ExplanationEdgeKind::Row(RowDerivationRule::UnweightedReduction)
        })
        .expect("row aggregation edge");
    assert!(
        edge.parents
            .iter()
            .filter(|parent| matches!(parent, ExplanationNodeId::Bound(_)))
            .count()
            >= 2
    );
}

#[test]
fn explains_evidence_promotion_on_the_preserved_bound_record() {
    let mut machine = ConstraintMachine::new();
    let pivot = TypeVar(0);
    let target = TypeVar(1);
    let lower = machine.alloc_pos(Pos::Con(vec!["lower".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["upper".into()], Vec::new()));
    let lower_parent = machine.bounds.add_lower(
        pivot,
        lower,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(OriginId::internal()),
    );
    let upper_parent = machine.bounds.add_upper(
        pivot,
        upper,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(OriginId::internal()),
    );
    let promoted_endpoint = machine.alloc_pos(Pos::Var(TypeVar(2)));
    let evidence = machine.bounds.add_evidence_lower(
        target,
        promoted_endpoint,
        ConstraintWeights::empty(),
        BoundDerivation::ReplayEvidence(BinaryReplayDerivation {
            pivot,
            lower: lower_parent.id,
            upper: upper_parent.id,
            rule: ReplayRule::LowerBoundAdded,
        }),
    );
    let promoted = machine.bounds.add_lower(
        target,
        promoted_endpoint,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(OriginId::unknown_internal()),
    );
    assert_eq!(evidence.id, promoted.id);
    assert!(promoted.promoted);

    let explanation = machine
        .why_lower_bound(target, promoted.id, ExplanationBudget::default())
        .unwrap();
    assert!(explanation.nodes.iter().any(|node| matches!(
        node,
        ExplanationNode::Bound { id, state: BoundRecordState::Ordinary, .. }
            if *id == promoted.id
    )));
    assert!(explanation.edges.iter().any(|edge| matches!(
        edge.kind,
        ExplanationEdgeKind::Bound(BoundDerivation::ReplayEvidence(_))
    )));
    assert!(explanation.edges.iter().any(|edge| matches!(
        edge.kind,
        ExplanationEdgeKind::Bound(BoundDerivation::Origin(_))
    )));
}

#[test]
fn explains_subsumed_disposition_and_tombstoned_bound() {
    let mut machine = ConstraintMachine::new();
    let source = TypeVar(0);
    let tail_var = TypeVar(1);
    let lower = machine.alloc_pos(Pos::Con(vec!["effect".into()], Vec::new()));
    let item = machine.alloc_neg(Neg::Con(vec!["effect".into()], Vec::new()));
    let tail = machine.alloc_neg(Neg::Var(tail_var));
    let row = machine.alloc_neg(Neg::Row(vec![item], tail));
    let origin = OriginId::unknown_internal();
    machine.add_lower_bound(
        source,
        lower,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    machine.add_upper_bound(
        source,
        row,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );
    let row_record = machine
        .events()
        .iter()
        .find_map(|event| match event {
            ConstraintEvent::UpperBoundAdded { record, bound, .. } if *bound == row => {
                Some(*record)
            }
            _ => None,
        })
        .unwrap();
    machine.add_upper_bound(
        source,
        tail,
        ConstraintWeights::empty(),
        BoundDerivation::Origin(origin),
    );

    let tombstone = machine.bounds.record(row_record).unwrap();
    assert_eq!(tombstone.state, BoundRecordState::Tombstone);
    let disposition = tombstone.disposition.unwrap();
    let disposition_explanation = machine
        .why_bound_disposition(disposition, ExplanationBudget::default())
        .unwrap();
    assert!(disposition_explanation.edges.iter().any(|edge| matches!(
        edge.kind,
        ExplanationEdgeKind::BoundDisposition(BoundDisposition::SubsumedBy(_))
    )));

    let tombstone_explanation = machine
        .why_upper_bound(source, row_record, ExplanationBudget::default())
        .unwrap();
    assert!(tombstone_explanation.nodes.iter().any(|node| matches!(
        node,
        ExplanationNode::Bound { id, state: BoundRecordState::Tombstone, .. }
            if *id == row_record
    )));
    assert!(tombstone_explanation.nodes.iter().any(
        |node| matches!(node, ExplanationNode::BoundDisposition { id, .. } if *id == disposition)
    ));
}
