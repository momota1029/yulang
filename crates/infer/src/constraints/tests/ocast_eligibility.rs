use super::*;
use crate::constraints::explain::ExplanationBudget;
use crate::constraints::ocast_eligibility::{
    EligibleBoundaryEvidence, InternalOnlyEvidence, OcastEligibilityOutcome, OcastIncompleteReason,
};

#[test]
fn coherent_replay_requires_one_boundary_on_both_exact_parents() {
    let mut machine = ConstraintMachine::new();
    let source = machine.alloc_source_boundary(ConstraintOriginKind::Annotation);
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["source".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], source.origin());
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    machine.subtype(pivot_pos, upper, source.origin());
    let producer = nominal_producer(&machine);

    let classification = machine.classify_ocast_eligibility(producer, ExplanationBudget::default());
    assert!(matches!(
        classification.outcome,
        OcastEligibilityOutcome::EligibleSourceBoundary {
            boundary,
            kind: ConstraintOriginKind::Annotation,
            evidence: EligibleBoundaryEvidence::SharedReplayPair { .. },
            ..
        } if boundary == source.boundary()
    ));
}

#[test]
fn unrelated_source_obligations_are_internal_only_with_disjoint_pair_evidence() {
    let mut machine = ConstraintMachine::new();
    let lower_source = machine.alloc_source_boundary(ConstraintOriginKind::Annotation);
    let upper_source = machine.alloc_source_boundary(ConstraintOriginKind::Return);
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["source".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], lower_source.origin());
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    machine.subtype(pivot_pos, upper, upper_source.origin());
    let producer = nominal_producer(&machine);

    let classification = machine.classify_ocast_eligibility(producer, ExplanationBudget::default());
    let OcastEligibilityOutcome::InternalOnly {
        evidence:
            InternalOnlyEvidence::DisjointReplayParents {
                lower_boundaries,
                upper_boundaries,
                ..
            },
    } = classification.outcome
    else {
        panic!("expected disjoint replay evidence: {classification:?}");
    };
    assert_eq!(lower_boundaries.len(), 1);
    assert_eq!(upper_boundaries.len(), 1);
    assert_eq!(lower_boundaries[0].boundary, lower_source.boundary());
    assert_eq!(upper_boundaries[0].boundary, upper_source.boundary());
}

#[test]
fn unwired_field_assignment_and_imported_boundaries_remain_incomplete() {
    for seam in ["field", "assignment", "imported"] {
        let mut machine = ConstraintMachine::new();
        let lower = machine.alloc_pos(Pos::Con(vec![format!("{seam}-source")], Vec::new()));
        let upper = machine.alloc_neg(Neg::Con(vec![format!("{seam}-target")], Vec::new()));
        machine.subtype(lower, upper, OriginId::unknown_internal());
        let producer = nominal_producer(&machine);
        let classification =
            machine.classify_ocast_eligibility(producer, ExplanationBudget::default());
        assert!(
            matches!(
                classification.outcome,
                OcastEligibilityOutcome::Incomplete {
                    reason: OcastIncompleteReason::UnknownOrigin(_)
                }
            ),
            "{seam}: {classification:?}"
        );
    }
}

#[test]
fn internal_origin_does_not_hide_an_unknown_alternate_derivation() {
    let mut machine = ConstraintMachine::new();
    let lower = machine.alloc_pos(Pos::Con(vec!["source".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.subtype(lower, upper, OriginId::internal());
    machine.subtype(lower, upper, OriginId::unknown_internal());
    let producer = nominal_producer(&machine);

    let classification = machine.classify_ocast_eligibility(producer, ExplanationBudget::default());
    assert!(matches!(
        classification.outcome,
        OcastEligibilityOutcome::Incomplete {
            reason: OcastIncompleteReason::UnknownOrigin(_)
        }
    ));
}

fn nominal_producer(machine: &ConstraintMachine) -> ConstraintRecordId {
    machine
        .events()
        .iter()
        .find_map(|event| match event {
            ConstraintEvent::NominalCastNeeded { producer, .. } => Some(*producer),
            _ => None,
        })
        .expect("fixture emits a nominal cast event")
}
