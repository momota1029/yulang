//! CPK-0b logical-proof baseline capture.
//!
//! Unlike `SemanticExecutionSnapshot`, this snapshot is set-like. It maps session-local record
//! identities to semantic first-seen ordinals and sorts every relation by its canonical key.

use super::*;
use crate::constraints::explain::{PortableProvenanceExportBudget, PortableProvenanceExportRoot};
use poly::provenance::{PortableProvenanceSnapshot, PortableSourceLocation};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LogicalProofSnapshot {
    pub(crate) occurrences: Vec<CanonicalProofOccurrence>,
    pub(crate) claim_relation: Vec<CanonicalClaimRelationEntry>,
    pub(crate) projection: Vec<CanonicalProjectionEntry>,
    pub(crate) dependencies: Vec<CanonicalDependencyEntry>,
    pub(crate) generalized: CanonicalGeneralizedProvenance,
    pub(crate) portable: CanonicalPortableProvenance,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CanonicalProofOccurrence {
    pub(crate) result: usize,
    pub(crate) cause: CanonicalProofCause,
    pub(crate) carrier: CanonicalCarrier,
    pub(crate) parents: Vec<CanonicalParentRoot>,
    pub(crate) completeness: CanonicalCompleteness,
    pub(crate) event_class: CanonicalProofEventClass,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CanonicalProofCause {
    Replay,
    Structural,
    ReductionRoute,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CanonicalProofEventClass {
    CanonicalReplayOccurrence,
    NonReplayQualifiedParent,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CanonicalParentSide {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CanonicalCompleteness {
    Complete,
    Incomplete,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CanonicalParentRoot {
    pub(crate) root: usize,
    pub(crate) side: Option<CanonicalParentSide>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CanonicalClaimRelationEntry {
    pub(crate) result: usize,
    pub(crate) root: usize,
    pub(crate) representative_claim: usize,
    pub(crate) side: Option<CanonicalParentSide>,
    pub(crate) carrier: CanonicalCarrier,
    pub(crate) first_winner: bool,
    pub(crate) lineage: String,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CanonicalCarrier {
    Replay {
        result: Option<usize>,
        pivot: usize,
        lower: usize,
        upper: usize,
        rule: String,
    },
    Structural {
        result: Option<usize>,
        parent: usize,
        rule: String,
    },
    ReductionRoute {
        result: Option<usize>,
        derivation: usize,
    },
    ConstraintOrigin {
        constraint: usize,
        origin: usize,
    },
    Origin {
        origin: usize,
    },
    SchemeInstantiation {
        witness: usize,
        result: Option<usize>,
    },
    Incomplete,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CanonicalProjectionEntry {
    pub(crate) lower: usize,
    pub(crate) supports: Vec<CanonicalSupport>,
    pub(crate) clauses: Vec<CanonicalClause>,
    pub(crate) links: Vec<(CanonicalSupport, usize)>,
    pub(crate) reverse_roots: Vec<usize>,
    pub(crate) projectable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CanonicalSupport {
    Claimed { root: usize },
    Independent { carrier: CanonicalCarrier },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CanonicalClause {
    Standalone(CanonicalSupport),
    DerivedUnary {
        carrier: CanonicalCarrier,
        premise: CanonicalPremise,
    },
    ReplayConjunction {
        carrier: CanonicalCarrier,
        lower_premise: usize,
        upper_premise: usize,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum CanonicalPremise {
    Record(usize),
    Constraint(usize),
    Root(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CanonicalDependencyEntry {
    pub(crate) premise: CanonicalPremise,
    pub(crate) dependent: usize,
    pub(crate) transitive_dependents: Vec<usize>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct CanonicalGeneralizedProvenance {
    pub(crate) schemes: Vec<CanonicalGeneralizedScheme>,
    pub(crate) witnesses: Vec<CanonicalGeneralizedWitness>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CanonicalGeneralizedScheme {
    pub(crate) owner: DefId,
    pub(crate) generation: u32,
    pub(crate) witnesses: Vec<usize>,
    pub(crate) completeness: CanonicalCompleteness,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CanonicalGeneralizedWitness {
    pub(crate) scheme: usize,
    pub(crate) path: GeneralizedTypePath,
    pub(crate) role: GeneralizedWitnessRole,
    pub(crate) incoming: Vec<CanonicalGeneralizationDerivation>,
    pub(crate) completeness: CanonicalCompleteness,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CanonicalGeneralizationDerivation {
    pub(crate) rule: GeneralizationDerivationRule,
    pub(crate) parents: Vec<CanonicalGeneralizationParent>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CanonicalGeneralizationParent {
    Constraint(usize),
    Bound(usize),
    BoundClaim {
        bound: usize,
        claim: usize,
    },
    BoundProjectionProof {
        bound: usize,
        carrier: CanonicalCarrier,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CanonicalPortableProvenance {
    pub(crate) roots: Vec<CanonicalPortableRoot>,
    pub(crate) snapshot: PortableProvenanceSnapshot,
    pub(crate) root_anchors: Vec<Option<usize>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CanonicalPortableRoot {
    Constraint(usize),
    Bound(usize),
    Origin(usize),
    RowDerivation(usize),
    GeneralizedWitness(usize),
}

struct Canonicalizer {
    vars: FxHashMap<TypeVar, usize>,
}

impl Canonicalizer {
    fn new(machine: &ConstraintMachine) -> Self {
        let mut vars = FxHashMap::default();
        for record in &machine.bounds.records {
            let next = vars.len();
            vars.entry(record.owner()).or_insert(next);
        }
        Self { vars }
    }

    fn var(&mut self, var: TypeVar) -> usize {
        let next = self.vars.len();
        *self.vars.entry(var).or_insert(next)
    }

    fn replay(
        &mut self,
        replay: BinaryReplayDerivation,
        result: Option<ConstraintRecordId>,
    ) -> CanonicalCarrier {
        CanonicalCarrier::Replay {
            result: result.map(|result| result.0 as usize),
            pivot: self.var(replay.pivot),
            lower: replay.lower.0 as usize,
            upper: replay.upper.0 as usize,
            rule: format!("{:?}", replay.rule),
        }
    }

    fn qualified(&mut self, parent: ClaimQualifiedParent) -> CanonicalCarrier {
        match parent {
            ClaimQualifiedParent::ReplayConstraint { replay, .. } => self.replay(replay, None),
            ClaimQualifiedParent::StructuralConstraint { derivation, .. } => {
                CanonicalCarrier::Structural {
                    result: None,
                    parent: derivation.parent.0 as usize,
                    rule: format!("{:?}", derivation.rule),
                }
            }
            ClaimQualifiedParent::ReductionRouteConstraint { derivation, .. } => {
                CanonicalCarrier::ReductionRoute {
                    result: None,
                    derivation: derivation.0 as usize,
                }
            }
        }
    }

    fn projection(&mut self, carrier: ProjectionProofCarrier) -> CanonicalCarrier {
        match carrier {
            ProjectionProofCarrier::ConstraintOrigin { constraint, origin } => {
                CanonicalCarrier::ConstraintOrigin {
                    constraint: constraint.0 as usize,
                    origin: origin.0 as usize,
                }
            }
            ProjectionProofCarrier::StructuralConstraint { result, derivation } => {
                CanonicalCarrier::Structural {
                    result: Some(result.0 as usize),
                    parent: derivation.parent.0 as usize,
                    rule: format!("{:?}", derivation.rule),
                }
            }
            ProjectionProofCarrier::ReplayConstraint { result, derivation } => {
                self.replay(derivation, Some(result))
            }
            ProjectionProofCarrier::ReplayEvidence(derivation) => self.replay(derivation, None),
            ProjectionProofCarrier::RowConstraint { result, derivation } => {
                CanonicalCarrier::ReductionRoute {
                    result: Some(result.0 as usize),
                    derivation: derivation.0 as usize,
                }
            }
            ProjectionProofCarrier::Row(derivation) => CanonicalCarrier::ReductionRoute {
                result: None,
                derivation: derivation.0 as usize,
            },
            ProjectionProofCarrier::SchemeInstantiationConstraint {
                result,
                source_witness,
            } => CanonicalCarrier::SchemeInstantiation {
                witness: source_witness.0 as usize,
                result: Some(result.0 as usize),
            },
            ProjectionProofCarrier::SchemeInstantiation(source_witness) => {
                CanonicalCarrier::SchemeInstantiation {
                    witness: source_witness.0 as usize,
                    result: None,
                }
            }
            ProjectionProofCarrier::Origin(origin) => CanonicalCarrier::Origin {
                origin: origin.0 as usize,
            },
            ProjectionProofCarrier::Incomplete => CanonicalCarrier::Incomplete,
        }
    }
}

impl ConstraintMachine {
    pub(crate) fn logical_proof_snapshot(&self) -> LogicalProofSnapshot {
        self.logical_proof_snapshot_with_source_locations(|_, _| None)
    }

    pub(crate) fn logical_proof_snapshot_with_source_locations(
        &self,
        mut source_location: impl FnMut(
            SourceBoundaryId,
            ConstraintOriginKind,
        ) -> Option<PortableSourceLocation>,
    ) -> LogicalProofSnapshot {
        let mut canonical = Canonicalizer::new(self);
        let mut occurrences = Vec::new();
        let mut claim_relation = Vec::new();

        for occurrence in &self.replay_occurrences.occurrences {
            let carrier = canonical.replay(occurrence.carrier, None);
            let mut roots = Vec::new();
            for (side, version) in [
                (ReplayClaimParentSide::Lower, occurrence.lower_parents),
                (ReplayClaimParentSide::Upper, occurrence.upper_parents),
            ] {
                for entry in self
                    .replay_parent_sets
                    .iter(version)
                    .expect("factored parent set")
                {
                    roots.push(CanonicalParentRoot {
                        root: entry.coverage_root.0 as usize,
                        side: Some(canonical_side(side)),
                    });
                    let winner = self
                        .replay_result_summary
                        .first_parent_by_root
                        .get(&(occurrence.result, entry.coverage_root))
                        .is_some_and(|winner| {
                            winner.occurrence == occurrence.id
                                && winner.parent_side == side
                                && winner.parent_claim == entry.representative_claim
                        });
                    claim_relation.push(CanonicalClaimRelationEntry {
                        result: occurrence.result.0 as usize,
                        root: entry.coverage_root.0 as usize,
                        representative_claim: entry.representative_claim.0 as usize,
                        side: Some(canonical_side(side)),
                        carrier: carrier.clone(),
                        first_winner: winner,
                        lineage: claim_lineage_class(
                            &self.bounds.upper_replay_claims[entry.representative_claim.0 as usize],
                        ),
                    });
                }
            }
            roots.sort_unstable();
            roots.dedup();
            occurrences.push(CanonicalProofOccurrence {
                result: occurrence.result.0 as usize,
                cause: CanonicalProofCause::Replay,
                carrier,
                parents: roots,
                completeness: canonical_completeness(
                    self.constraint_records[occurrence.result.0 as usize].replay_provenance,
                ),
                event_class: CanonicalProofEventClass::CanonicalReplayOccurrence,
            });
        }

        for result_index in 0..self.constraint_records.len() {
            let result = ConstraintRecordId(result_index as u32);
            for parent in self.non_replay_claim_parents_for_result(result) {
                let claim = parent.parent_claim();
                let root = self.bounds.upper_replay_claims[claim.0 as usize].coverage_root;
                let carrier = canonical.qualified(parent);
                let cause = match parent {
                    ClaimQualifiedParent::StructuralConstraint { .. } => {
                        CanonicalProofCause::Structural
                    }
                    ClaimQualifiedParent::ReductionRouteConstraint { .. } => {
                        CanonicalProofCause::ReductionRoute
                    }
                    ClaimQualifiedParent::ReplayConstraint { .. } => unreachable!(),
                };
                occurrences.push(CanonicalProofOccurrence {
                    result: result_index,
                    cause,
                    carrier: carrier.clone(),
                    parents: vec![CanonicalParentRoot {
                        root: root.0 as usize,
                        side: None,
                    }],
                    completeness: CanonicalCompleteness::Complete,
                    event_class: CanonicalProofEventClass::NonReplayQualifiedParent,
                });
                claim_relation.push(CanonicalClaimRelationEntry {
                    result: result_index,
                    root: root.0 as usize,
                    representative_claim: claim.0 as usize,
                    side: None,
                    carrier,
                    first_winner: self
                        .replay_result_summary
                        .test_first_qualified_parent_source(result, root)
                        .is_some_and(|source| {
                            source == replay_factored::FirstQualifiedParentSource::NonReplay(parent)
                        }),
                    lineage: claim_lineage_class(
                        &self.bounds.upper_replay_claims[claim.0 as usize],
                    ),
                });
            }
        }
        occurrences.sort();
        occurrences.dedup();
        claim_relation.sort();
        claim_relation.dedup();

        let projection = capture_projection(self, &mut canonical);
        let dependencies = capture_dependencies(self);
        let generalized = capture_generalized(self, &mut canonical);
        let portable = capture_portable(self, &mut source_location);
        LogicalProofSnapshot {
            occurrences,
            claim_relation,
            projection,
            dependencies,
            generalized,
            portable,
        }
    }
}

fn capture_projection(
    machine: &ConstraintMachine,
    canonical: &mut Canonicalizer,
) -> Vec<CanonicalProjectionEntry> {
    let mut lowers = machine
        .bounds
        .projection_proofs_by_lower_record
        .keys()
        .chain(
            machine
                .bounds
                .record_proof_clause_ids_by_lower_record
                .keys(),
        )
        .copied()
        .collect::<Vec<_>>();
    lowers.sort_unstable_by_key(|record| record.0);
    lowers.dedup();
    lowers
        .into_iter()
        .map(|lower| {
            let mut supports = machine
                .bounds
                .projection_proofs_by_lower_record
                .get(&lower)
                .into_iter()
                .flatten()
                .map(|proof| canonical_support(canonical, proof.support))
                .collect::<Vec<_>>();
            supports.sort();
            supports.dedup();
            let clause_ids = machine
                .bounds
                .record_proof_clause_ids_by_lower_record
                .get(&lower)
                .cloned()
                .unwrap_or_default();
            let mut clauses = clause_ids
                .iter()
                .map(|id| {
                    canonical_clause(
                        canonical,
                        machine.bounds.record_proof_clauses[id.0 as usize].clause,
                    )
                })
                .collect::<Vec<_>>();
            clauses.sort();
            clauses.dedup();
            let mut links = machine
                .bounds
                .record_proof_clause_links_by_lower_record
                .get(&lower)
                .into_iter()
                .flatten()
                .map(|link| {
                    let clause = canonical_clause(
                        canonical,
                        machine.bounds.record_proof_clauses[link.clause.0 as usize].clause,
                    );
                    let clause_index = clauses.binary_search(&clause).expect("canonical clause");
                    (canonical_support(canonical, link.support), clause_index)
                })
                .collect::<Vec<_>>();
            links.sort();
            links.dedup();
            let mut reverse_roots = machine
                .bounds
                .scheme_projection_lower_record_memberships
                .iter()
                .filter_map(|(root, record)| (*record == lower).then_some(root.0 as usize))
                .collect::<Vec<_>>();
            reverse_roots.sort_unstable();
            reverse_roots.dedup();
            CanonicalProjectionEntry {
                lower: lower.0 as usize,
                supports,
                clauses,
                links,
                reverse_roots,
                projectable: machine.scheme_projection_record_is_included(lower),
            }
        })
        .collect()
}

fn capture_dependencies(machine: &ConstraintMachine) -> Vec<CanonicalDependencyEntry> {
    let mut entries = Vec::new();
    for (&premise, dependents) in &machine.bounds.dependent_records_by_premise {
        let canonical_premise = canonical_premise(premise);
        let mut transitive = dependents.clone();
        machine.extend_with_record_dependents(&mut transitive);
        let mut transitive = transitive
            .into_iter()
            .map(|record| record.0 as usize)
            .collect::<Vec<_>>();
        transitive.sort_unstable();
        for dependent in dependents {
            entries.push(CanonicalDependencyEntry {
                premise: canonical_premise.clone(),
                dependent: dependent.0 as usize,
                transitive_dependents: transitive.clone(),
            });
        }
    }
    entries.sort();
    entries.dedup();
    entries
}

fn capture_generalized(
    machine: &ConstraintMachine,
    canonical: &mut Canonicalizer,
) -> CanonicalGeneralizedProvenance {
    let schemes = machine
        .generalized_schemes
        .iter()
        .map(|scheme| CanonicalGeneralizedScheme {
            owner: scheme.owner,
            generation: scheme.generation,
            witnesses: scheme.witnesses.iter().map(|id| id.0 as usize).collect(),
            completeness: canonical_completeness(scheme.completeness),
        })
        .collect();
    let witnesses = machine
        .generalized_witnesses
        .iter()
        .map(|witness| CanonicalGeneralizedWitness {
            scheme: witness.scheme.0 as usize,
            path: witness.path.clone(),
            role: witness.role,
            incoming: witness
                .incoming
                .iter()
                .map(|derivation| CanonicalGeneralizationDerivation {
                    rule: derivation.rule,
                    parents: derivation
                        .parents
                        .iter()
                        .map(|parent| canonical_generalization_parent(canonical, *parent))
                        .collect(),
                })
                .collect(),
            completeness: canonical_completeness(witness.completeness),
        })
        .collect();
    CanonicalGeneralizedProvenance { schemes, witnesses }
}

fn capture_portable(
    machine: &ConstraintMachine,
    source_location: &mut impl FnMut(
        SourceBoundaryId,
        ConstraintOriginKind,
    ) -> Option<PortableSourceLocation>,
) -> CanonicalPortableProvenance {
    let mut roots = Vec::new();
    let mut export_roots = Vec::new();
    for index in 0..machine.constraint_records.len() {
        roots.push(CanonicalPortableRoot::Constraint(index));
        export_roots.push(PortableProvenanceExportRoot::Constraint(
            ConstraintRecordId(index as u32),
        ));
    }
    for index in 0..machine.bounds.records.len() {
        roots.push(CanonicalPortableRoot::Bound(index));
        export_roots.push(PortableProvenanceExportRoot::Bound(BoundRecordId(
            index as u32,
        )));
    }
    for index in 0..machine.origins.len() {
        roots.push(CanonicalPortableRoot::Origin(index));
        export_roots.push(PortableProvenanceExportRoot::Origin(OriginId(index as u32)));
    }
    for index in 0..machine.row_derivations.len() {
        roots.push(CanonicalPortableRoot::RowDerivation(index));
        export_roots.push(PortableProvenanceExportRoot::RowDerivation(
            RowDerivationId(index as u32),
        ));
    }
    for index in 0..machine.generalized_witnesses.len() {
        roots.push(CanonicalPortableRoot::GeneralizedWitness(index));
        export_roots.push(PortableProvenanceExportRoot::GeneralizedWitness(
            GeneralizedSchemeWitnessId(index as u32),
        ));
    }
    let export = machine
        .export_portable_provenance(
            &export_roots,
            PortableProvenanceExportBudget::default(),
            source_location,
        )
        .expect("canonical proof roots must be exportable");
    CanonicalPortableProvenance {
        roots,
        snapshot: export.snapshot,
        root_anchors: export
            .root_anchors
            .into_iter()
            .map(|anchor| anchor.map(|anchor| anchor.index()))
            .collect(),
    }
}

fn canonical_support(
    canonical: &mut Canonicalizer,
    support: SchemeProjectionProofSupport,
) -> CanonicalSupport {
    match support {
        SchemeProjectionProofSupport::Claimed(root) => CanonicalSupport::Claimed {
            root: root.0 as usize,
        },
        SchemeProjectionProofSupport::Independent(carrier) => CanonicalSupport::Independent {
            carrier: canonical.projection(carrier),
        },
    }
}

fn canonical_clause(canonical: &mut Canonicalizer, clause: RecordProofClause) -> CanonicalClause {
    match clause {
        RecordProofClause::Standalone { support } => {
            CanonicalClause::Standalone(canonical_support(canonical, support))
        }
        RecordProofClause::DerivedUnary { carrier, premise } => CanonicalClause::DerivedUnary {
            carrier: match carrier {
                DerivedUnaryCarrier::Structural(derivation) => CanonicalCarrier::Structural {
                    result: None,
                    parent: derivation.parent.0 as usize,
                    rule: format!("{:?}", derivation.rule),
                },
                DerivedUnaryCarrier::ReductionRoute(derivation) => {
                    CanonicalCarrier::ReductionRoute {
                        result: None,
                        derivation: derivation.0 as usize,
                    }
                }
            },
            premise: canonical_premise(premise),
        },
        RecordProofClause::ReplayConjunction {
            carrier,
            lower_premise,
            upper_premise,
        } => CanonicalClause::ReplayConjunction {
            carrier: canonical.replay(carrier, None),
            lower_premise: lower_premise.0 as usize,
            upper_premise: upper_premise.0 as usize,
        },
    }
}

fn canonical_premise(premise: ProofPremise) -> CanonicalPremise {
    match premise {
        ProofPremise::Record(record) => CanonicalPremise::Record(record.0 as usize),
        ProofPremise::Constraint(record) => CanonicalPremise::Constraint(record.0 as usize),
        ProofPremise::RootCoverage(root) => CanonicalPremise::Root(root.0 as usize),
    }
}

fn canonical_generalization_parent(
    canonical: &mut Canonicalizer,
    parent: GeneralizationParent,
) -> CanonicalGeneralizationParent {
    match parent {
        GeneralizationParent::Constraint(record) => {
            CanonicalGeneralizationParent::Constraint(record.0 as usize)
        }
        GeneralizationParent::Bound(record) => {
            CanonicalGeneralizationParent::Bound(record.0 as usize)
        }
        GeneralizationParent::BoundClaim { bound, claim } => {
            CanonicalGeneralizationParent::BoundClaim {
                bound: bound.0 as usize,
                claim: claim.0 as usize,
            }
        }
        GeneralizationParent::BoundProjectionProof { bound, carrier } => {
            CanonicalGeneralizationParent::BoundProjectionProof {
                bound: bound.0 as usize,
                carrier: canonical.projection(carrier),
            }
        }
    }
}

fn claim_lineage_class(claim: &UpperReplayClaim) -> String {
    match claim.lineage {
        UpperReplayClaimLineage::Original => "original",
        UpperReplayClaimLineage::ReplayConstraint { .. } => "replay-constraint",
        UpperReplayClaimLineage::ReplayEvidence { .. } => "replay-evidence",
        UpperReplayClaimLineage::StructuralConstraint { .. } => "structural-constraint",
        UpperReplayClaimLineage::ReductionRouteConstraint { .. } => "reduction-route-constraint",
    }
    .into()
}

fn canonical_side(side: ReplayClaimParentSide) -> CanonicalParentSide {
    match side {
        ReplayClaimParentSide::Lower => CanonicalParentSide::Lower,
        ReplayClaimParentSide::Upper => CanonicalParentSide::Upper,
    }
}

fn canonical_completeness(completeness: ProvenanceCompleteness) -> CanonicalCompleteness {
    match completeness {
        ProvenanceCompleteness::Complete => CanonicalCompleteness::Complete,
        ProvenanceCompleteness::Incomplete => CanonicalCompleteness::Incomplete,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn projection_carriers_that_differ_only_by_result_remain_distinct() {
        let machine = ConstraintMachine::new();
        let mut canonical = Canonicalizer::new(&machine);
        let results = [ConstraintRecordId(7), ConstraintRecordId(8)];
        let structural = StructuralDerivation {
            parent: ConstraintRecordId(3),
            rule: StructuralDerivationRule::FunctionReturn,
        };
        let replay = BinaryReplayDerivation {
            pivot: TypeVar(4),
            lower: BoundRecordId(5),
            upper: BoundRecordId(6),
            rule: ReplayRule::LowerBoundAdded,
        };

        assert_ne!(
            canonical.projection(ProjectionProofCarrier::StructuralConstraint {
                result: results[0],
                derivation: structural,
            }),
            canonical.projection(ProjectionProofCarrier::StructuralConstraint {
                result: results[1],
                derivation: structural,
            }),
        );
        assert_ne!(
            canonical.projection(ProjectionProofCarrier::ReplayConstraint {
                result: results[0],
                derivation: replay,
            }),
            canonical.projection(ProjectionProofCarrier::ReplayConstraint {
                result: results[1],
                derivation: replay,
            }),
        );
        assert_ne!(
            canonical.projection(ProjectionProofCarrier::RowConstraint {
                result: results[0],
                derivation: RowDerivationId(9),
            }),
            canonical.projection(ProjectionProofCarrier::RowConstraint {
                result: results[1],
                derivation: RowDerivationId(9),
            }),
        );
    }
}
