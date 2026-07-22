use super::*;
use crate::constraints::explain::ExplanationBudget;
use crate::constraints::ocast_eligibility::{
    EligibleBoundaryEvidence, InternalOnlyEvidence, OcastEligibilityOutcome, OcastIncompleteReason,
    ReplaySourceParent,
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
fn internal_replay_parents_are_internal_only() {
    let mut machine = ConstraintMachine::new();
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["source".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], OriginId::internal());
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    machine.subtype(pivot_pos, upper, OriginId::internal());
    let producer = nominal_producer(&machine);

    let classification = machine.classify_ocast_eligibility(producer, ExplanationBudget::default());
    assert!(matches!(
        classification.outcome,
        OcastEligibilityOutcome::InternalOnly {
            evidence: InternalOnlyEvidence::NoEligibleSourceBoundary
        }
    ));
}

#[test]
fn one_source_parent_and_one_internal_parent_are_eligible() {
    let mut machine = ConstraintMachine::new();
    let source = machine.alloc_source_boundary(ConstraintOriginKind::ApplicationArgument);
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["source".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], OriginId::internal());
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    machine.subtype(pivot_pos, upper, source.origin());
    let producer = nominal_producer(&machine);

    let classification = machine.classify_ocast_eligibility(producer, ExplanationBudget::default());
    assert!(matches!(
        classification.outcome,
        OcastEligibilityOutcome::EligibleSourceBoundary {
            boundary,
            kind: ConstraintOriginKind::ApplicationArgument,
            evidence: EligibleBoundaryEvidence::OneSidedReplayPair {
                source_parent: ReplaySourceParent::Upper,
                ..
            },
            ..
        } if boundary == source.boundary()
    ));
}

#[test]
fn body_requirement_is_source_owned_but_never_an_eligible_cast_boundary() {
    let mut machine = ConstraintMachine::new();
    let body = machine.alloc_source_boundary(ConstraintOriginKind::BodyRequirement(
        BodyRequirementKind::BooleanCondition,
    ));
    let lower = machine.alloc_pos(Pos::Con(vec!["source".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.subtype(lower, upper, body.origin());
    let producer = nominal_producer(&machine);

    let explanation = machine
        .why_constraint(producer, ExplanationBudget::default())
        .expect("query body-owned nominal mismatch");
    assert!(explanation.source_leaves.iter().any(|leaf| {
        leaf.boundary == body.boundary()
            && leaf.kind
                == ConstraintOriginKind::BodyRequirement(BodyRequirementKind::BooleanCondition)
    }));
    let classification = machine.classify_ocast_eligibility(producer, ExplanationBudget::default());
    assert!(matches!(
        classification.outcome,
        OcastEligibilityOutcome::InternalOnly {
            evidence: InternalOnlyEvidence::NoEligibleSourceBoundary
        }
    ));
    assert_eq!(
        machine.timing().body_requirement_origins,
        BodyRequirementOriginCoverage {
            boolean_condition: 1,
            roots_lacking_location: 1,
            ..BodyRequirementOriginCoverage::default()
        }
    );
}

#[test]
fn body_requirement_does_not_disqualify_application_plus_internal_replay() {
    let mut machine = ConstraintMachine::new();
    let application = machine.alloc_source_boundary(ConstraintOriginKind::ApplicationArgument);
    let body = machine.alloc_source_boundary(ConstraintOriginKind::BodyRequirement(
        BodyRequirementKind::BooleanCondition,
    ));
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["source".into()], Vec::new()));
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], OriginId::internal());
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], body.origin());
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.subtype(pivot_pos, upper, application.origin());
    let producer = nominal_producer(&machine);

    let classification = machine.classify_ocast_eligibility(producer, ExplanationBudget::default());
    assert!(matches!(
        classification.outcome,
        OcastEligibilityOutcome::EligibleSourceBoundary {
            boundary,
            kind: ConstraintOriginKind::ApplicationArgument,
            evidence: EligibleBoundaryEvidence::OneSidedReplayPair {
                source_parent: ReplaySourceParent::Upper,
                ..
            },
            ..
        } if boundary == application.boundary()
    ));
}

#[test]
fn one_sided_pair_with_multiple_source_obligations_is_not_eligible() {
    let mut machine = ConstraintMachine::new();
    let first = machine.alloc_source_boundary(ConstraintOriginKind::Annotation);
    let second = machine.alloc_source_boundary(ConstraintOriginKind::ApplicationArgument);
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["source".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], OriginId::internal());
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    machine.subtype(pivot_pos, upper, first.origin());
    machine.subtype(pivot_pos, upper, second.origin());
    let producer = nominal_producer(&machine);

    let classification = machine.classify_ocast_eligibility(producer, ExplanationBudget::default());
    assert!(matches!(
        classification.outcome,
        OcastEligibilityOutcome::InternalOnly { .. }
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
fn source_origin_does_not_hide_an_unknown_alternate_derivation() {
    let mut machine = ConstraintMachine::new();
    let source = machine.alloc_source_boundary(ConstraintOriginKind::ApplicationArgument);
    let pivot = TypeVar(0);
    let lower = machine.alloc_pos(Pos::Con(vec!["source".into()], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec!["target".into()], Vec::new()));
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], source.origin());
    machine.constrain_pos_to_var_direct_many([(lower, pivot)], OriginId::unknown_internal());
    let pivot_pos = machine.alloc_pos(Pos::Var(pivot));
    machine.subtype(pivot_pos, upper, OriginId::internal());
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
