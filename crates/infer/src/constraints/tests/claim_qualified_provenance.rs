use super::*;

use crate::analysis::AnalysisSession;
use crate::constraints::explain::{ExplanationBudget, ExplanationEdgeKind, ExplanationNodeId};
use poly::expr::{Arena as PolyArena, DefId};
use poly::provenance::{
    PortableBoundDirection, PortableConstraintOriginKind, PortableProvenanceNodeKind,
    ProvenanceCompleteness as PortableCompleteness, TypeOccurrenceKey, TypeOccurrenceOwner,
    TypeOccurrenceRole,
};

#[test]
fn claim_qualified_local_explanation_projects_each_lineage_without_expanding_the_bound() {
    for lineage in LineageCase::ALL {
        let fixture = claim_qualified_fixture(lineage);
        let machine = fixture.session.infer.constraints();
        let explanation = machine
            .why_generalized_witness(fixture.witness, ExplanationBudget::default())
            .expect("manually constructed generalized witness");
        let edge = explanation
            .edges
            .iter()
            .find(|edge| {
                edge.child == ExplanationNodeId::GeneralizedWitness(fixture.witness)
                    && matches!(edge.kind, ExplanationEdgeKind::Generalization(_))
            })
            .expect("generalization edge");

        assert_eq!(edge.parents, fixture.expected_parents, "{lineage:?}");
        assert!(
            !explanation
                .nodes
                .iter()
                .any(|node| node.id() == ExplanationNodeId::Bound(fixture.audit_bound)),
            "{lineage:?}: the mixed audit bound must not be a semantic explanation parent"
        );
        assert!(
            !explanation
                .nodes
                .iter()
                .any(|node| node.id() == ExplanationNodeId::Constraint(fixture.sibling_constraint)),
            "{lineage:?}: sibling covered derivations must not leak from the mixed bound"
        );
    }
}

#[test]
fn claim_qualified_occurrence_roots_round_trip_portably_for_each_lineage() {
    for lineage in LineageCase::ALL {
        let fixture = claim_qualified_fixture(lineage);
        let sidecar = fixture.session.build_subtype_provenance_sidecar();
        let key = TypeOccurrenceKey {
            owner: TypeOccurrenceOwner::Definition(fixture.owner),
            role: TypeOccurrenceRole::DefinitionPredicate,
            path: Default::default(),
        };
        let occurrence = sidecar
            .occurrences
            .get(&key)
            .expect("generalized occurrence");

        assert_eq!(
            occurrence.completeness,
            PortableCompleteness::Complete,
            "{lineage:?}"
        );
        assert_eq!(
            occurrence.anchors.len(),
            fixture.expected_parents.len(),
            "{lineage:?}"
        );
        let root_kinds = occurrence
            .anchors
            .iter()
            .map(|anchor| {
                let node = sidecar
                    .snapshot
                    .anchor(*anchor)
                    .and_then(|anchor| sidecar.snapshot.node(anchor.node))
                    .expect("portable anchor node");
                node.kind
            })
            .collect::<Vec<_>>();
        assert_eq!(root_kinds, fixture.expected_portable_roots, "{lineage:?}");

        let origins = sidecar
            .snapshot
            .nodes()
            .iter()
            .filter_map(|node| match node.kind {
                PortableProvenanceNodeKind::Origin { kind, .. } => Some(kind),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(
            origins.len(),
            fixture.expected_portable_origins.len(),
            "{lineage:?}: portable closure must contain only claim-local origins"
        );
        for expected in fixture.expected_portable_origins {
            assert!(origins.contains(&expected), "{lineage:?}: {origins:?}");
        }
        assert!(
            !origins.contains(&PortableConstraintOriginKind::ApplicationArgument),
            "{lineage:?}: sibling bound derivation leaked into portable output"
        );
        assert!(
            !origins.contains(&PortableConstraintOriginKind::BodyRequirement(
                poly::provenance::PortableBodyRequirementKind::BooleanCondition,
            )),
            "{lineage:?}: a derived claim projected through its original producer"
        );
    }
}

#[derive(Debug, Clone, Copy)]
enum LineageCase {
    Original,
    ReplayConstraint,
    ReductionRouteConstraint,
    ReplayEvidence,
}

impl LineageCase {
    const ALL: [Self; 4] = [
        Self::Original,
        Self::ReplayConstraint,
        Self::ReductionRouteConstraint,
        Self::ReplayEvidence,
    ];
}

struct ClaimQualifiedFixture {
    session: AnalysisSession,
    owner: DefId,
    witness: GeneralizedSchemeWitnessId,
    audit_bound: BoundRecordId,
    sibling_constraint: ConstraintRecordId,
    expected_parents: Vec<ExplanationNodeId>,
    expected_portable_roots: Vec<PortableProvenanceNodeKind>,
    expected_portable_origins: Vec<PortableConstraintOriginKind>,
}

fn claim_qualified_fixture(lineage: LineageCase) -> ClaimQualifiedFixture {
    let mut session = AnalysisSession::new(PolyArena::new());
    let owner = DefId(0);
    let (audit_bound, claim, sibling_constraint, expected_parents, expected_portable_roots) = {
        let machine = session.infer.constraints_mut();
        let original = root_constraint(machine, "original", ConstraintOriginKind::Annotation);
        let replay_result = root_constraint(machine, "replay-result", ConstraintOriginKind::Return);
        let reduction_result =
            root_constraint(machine, "reduction-result", ConstraintOriginKind::Field);
        let replay_lower_constraint =
            root_constraint(machine, "replay-lower", ConstraintOriginKind::Assignment);
        let replay_upper_constraint =
            root_constraint(machine, "replay-upper", ConstraintOriginKind::Pattern);
        let sibling_constraint = root_constraint(
            machine,
            "covered-sibling",
            ConstraintOriginKind::ApplicationArgument,
        );
        let original_parent = root_constraint(
            machine,
            "original-parent",
            ConstraintOriginKind::BodyRequirement(BodyRequirementKind::BooleanCondition),
        );

        let audit_owner = TypeVar(10);
        let audit_pos = machine.alloc_pos(Pos::Con(vec!["audit-bound".into()], Vec::new()));
        machine.add_lower_bound(
            audit_owner,
            audit_pos,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(sibling_constraint),
        );
        let audit_bound = machine.bounds.scheme_projection_lower_record_by_constraint
            [&sibling_constraint];

        let replay_pivot = TypeVar(20);
        let replay_lower_pos =
            machine.alloc_pos(Pos::Con(vec!["replay-lower-bound".into()], Vec::new()));
        let replay_lower = machine
            .bounds
            .add_lower(
                replay_pivot,
                replay_lower_pos,
                ConstraintWeights::empty(),
                BoundDerivation::Constraint(replay_lower_constraint),
            )
            .id;
        let replay_upper_neg =
            machine.alloc_neg(Neg::Con(vec!["replay-upper-bound".into()], Vec::new()));
        let replay_upper = machine
            .bounds
            .add_upper(
                replay_pivot,
                replay_upper_neg,
                ConstraintWeights::empty(),
                BoundDerivation::Constraint(replay_upper_constraint),
            )
            .id;
        let replay = BinaryReplayDerivation {
            pivot: replay_pivot,
            lower: replay_lower,
            upper: replay_upper,
            rule: ReplayRule::LowerBoundAdded,
        };
        let reduction_derivation = machine.intern_row_derivation(
            RowDerivationRule::UnweightedReduction,
            vec![RowDerivationParent::Constraint(reduction_result)],
            Vec::new(),
        );

        let claim_source = TypeVar(30);
        let original_upper_neg =
            machine.alloc_neg(Neg::Con(vec!["claim-original-upper".into()], Vec::new()));
        let root_producer = match lineage {
            LineageCase::Original => original,
            _ => original_parent,
        };
        machine.add_upper_bound(
            claim_source,
            original_upper_neg,
            ConstraintWeights::empty(),
            BoundDerivation::Constraint(root_producer),
        );
        let original_claim = machine.bounds.root_claim_by_producer_constraint[&root_producer];

        let selected_claim = match lineage {
            LineageCase::Original => original_claim,
            LineageCase::ReplayConstraint | LineageCase::ReductionRouteConstraint => {
                let derived_upper_neg =
                    machine.alloc_neg(Neg::Con(vec!["claim-derived-upper".into()], Vec::new()));
                machine.add_upper_bound(
                    claim_source,
                    derived_upper_neg,
                    ConstraintWeights::empty(),
                    BoundDerivation::Origin(OriginId::unknown_internal()),
                );
                let derived_upper = machine.bounds.of(claim_source)
                    .into_iter()
                    .flat_map(VarBounds::upper_record_ids)
                    .copied()
                    .find(|record| machine.bounds.record(*record).is_some_and(|record| {
                        record.endpoint() == BoundEndpoint::Upper(derived_upper_neg)
                    }))
                    .expect("derived upper record");
                let (producer, parent) = match lineage {
                    LineageCase::ReplayConstraint => (replay_result,
                        ClaimQualifiedParent::ReplayConstraint {
                            parent_claim: original_claim,
                            parent_side: ReplayClaimParentSide::Upper,
                            replay,
                        }),
                    LineageCase::ReductionRouteConstraint => {
                        (reduction_result, ClaimQualifiedParent::ReductionRouteConstraint {
                            parent_claim: original_claim,
                            derivation: reduction_derivation,
                        })
                    }
                    LineageCase::Original | LineageCase::ReplayEvidence => unreachable!(),
                };
                machine.admit_claim_qualified_parent(producer, parent);
                machine.register_constraint_upper_replay_claims(
                    derived_upper,
                    Some(producer),
                ).into_iter().find(|claim| {
                    machine.bounds.upper_replay_claims[claim.0 as usize].current_record
                        == derived_upper
                }).expect("qualified parent materializes the derived claim")
            }
            LineageCase::ReplayEvidence => {
                let evidence_lower = machine.alloc_pos(Pos::Var(TypeVar(40)));
                let evidence_upper = machine.alloc_neg(Neg::Var(TypeVar(41)));
                machine.materialize_replay_evidence_claim_for_test(
                    evidence_lower,
                    evidence_upper,
                    replay,
                    original_claim,
                )
            }
        };
        let mutation = machine.bounds.link_scheme_projection_claim(audit_bound, selected_claim);
        machine.apply_scheme_projection_mutation(mutation);
        let root = machine.bounds.upper_replay_claims[selected_claim.0 as usize].coverage_root;
        let support = SchemeProjectionProofSupport::Claimed(root);
        machine.register_cpk_projection_clause_for_test(
            audit_bound,
            RecordProofClauseLinkAdmission::claimed(
                root,
                RecordProofClause::Standalone { support },
                ClaimedAttributionSource::FlatRetained,
            ),
        );
        assert_eq!(
            machine
                .scheme_projectable_lowers(audit_owner)
                .find(|entry| entry.record == audit_bound)
                .map(|entry| entry.reason),
            Some(SchemeProjectableLowerReason::Qualified {
                uncovered_claims: vec![selected_claim],
                independent_supports: Vec::new(),
            }),
            "fixture must use the same bound-claim link validated by projection"
        );

        let (expected_parents, expected_portable_roots) = match lineage {
            LineageCase::Original => (
                vec![ExplanationNodeId::Constraint(original)],
                vec![PortableProvenanceNodeKind::Constraint {
                    replay_complete: true,
                }],
            ),
            LineageCase::ReplayConstraint => (
                vec![ExplanationNodeId::Constraint(replay_result)],
                vec![PortableProvenanceNodeKind::Constraint {
                    replay_complete: true,
                }],
            ),
            LineageCase::ReductionRouteConstraint => (
                vec![ExplanationNodeId::Constraint(reduction_result)],
                vec![PortableProvenanceNodeKind::Constraint {
                    replay_complete: true,
                }],
            ),
            LineageCase::ReplayEvidence => (
                vec![
                    ExplanationNodeId::Bound(replay_lower),
                    ExplanationNodeId::Bound(replay_upper),
                ],
                vec![
                    PortableProvenanceNodeKind::Bound {
                        direction: PortableBoundDirection::Lower,
                        state: poly::provenance::PortableBoundState::Ordinary,
                        weighted: false,
                    },
                    PortableProvenanceNodeKind::Bound {
                        direction: PortableBoundDirection::Upper,
                        state: poly::provenance::PortableBoundState::Ordinary,
                        weighted: false,
                    },
                ],
            ),
        };
        (
            audit_bound,
            selected_claim,
            sibling_constraint,
            expected_parents,
            expected_portable_roots,
        )
    };

    let scheme = session.record_generalized_scheme(
        owner,
        vec![GeneralizedWitnessDraft {
            path: GeneralizedTypePath::default(),
            role: GeneralizedWitnessRole::LowerBound,
            incoming: vec![GeneralizationDerivation {
                rule: GeneralizationDerivationRule::BoundCollection,
                parents: vec![GeneralizationParent::BoundClaim {
                    bound: audit_bound,
                    claim,
                }],
            }],
            completeness: ProvenanceCompleteness::Complete,
        }],
        ProvenanceCompleteness::Complete,
    );
    let witness = session
        .infer
        .constraints()
        .generalized_scheme_record(scheme)
        .expect("manual scheme")
        .witnesses[0];
    let expected_portable_origins = match lineage {
        LineageCase::Original => vec![PortableConstraintOriginKind::Annotation],
        LineageCase::ReplayConstraint => vec![PortableConstraintOriginKind::Return],
        LineageCase::ReductionRouteConstraint => vec![PortableConstraintOriginKind::Field],
        LineageCase::ReplayEvidence => vec![
            PortableConstraintOriginKind::Assignment,
            PortableConstraintOriginKind::Pattern,
        ],
    };

    ClaimQualifiedFixture {
        session,
        owner,
        witness,
        audit_bound,
        sibling_constraint,
        expected_parents,
        expected_portable_roots,
        expected_portable_origins,
    }
}

fn root_constraint(
    machine: &mut ConstraintMachine,
    name: &str,
    kind: ConstraintOriginKind,
) -> ConstraintRecordId {
    let origin = machine.alloc_source_boundary(kind).origin();
    let lower = machine.alloc_pos(Pos::Con(vec![format!("{name}-lower")], Vec::new()));
    let upper = machine.alloc_neg(Neg::Con(vec![format!("{name}-upper")], Vec::new()));
    machine.subtype(lower, upper, origin);
    machine
        .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
        .expect("root constraint")
}
