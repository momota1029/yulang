//! Quiescent ordinary-cast diagnostic activation.
//!
//! This module retains the exact nominal event payload beside its settled eligibility, plans the
//! cast-table cardinality outcome, and emits diagnostics only for proven source boundaries. The
//! solver's eager candidate instantiation remains unchanged; activation is a diagnostic overlay.

use poly::cast_resolution::OrdinaryCastResolution;
use poly::expr::DefId;
use poly::types::{NegId, PosId};

use crate::analysis::{
    BodyRequirementDiagnosticKind, DiagnosticTypeDerivation, DiagnosticTypeExplanation,
    DiagnosticTypeExplanationSite, DiagnosticTypeExplanationSiteRole,
};
use crate::casts::CastTable;
use crate::constraints::explain::{
    ExplanationBudget, ExplanationCompleteness, generalized_scheme_path_reaches_origin_kind,
    project_parameter_body_requirements,
};
use crate::constraints::ocast_eligibility::{
    EligibleBoundaryDiagnosticKind, EligibleBoundaryEvidence, OcastEligibilityClassification,
    OcastEligibilityOutcome, OcastEligibilityState, ReplaySourceParent,
};
use crate::constraints::{
    BodyRequirementKind, BoundRecordId, ConstraintOriginKind, ConstraintRecordId,
    ConstraintWeights, SourceBoundaryId,
};

use super::super::{AnalysisDiagnostic, AnalysisSession};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct PendingNominalCastRequest {
    pub(super) producer: ConstraintRecordId,
    pub(super) lower: PosId,
    pub(super) upper: NegId,
    pub(super) source: Vec<String>,
    pub(super) target: Vec<String>,
    pub(super) weights: ConstraintWeights,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClassifiedNominalCastRequest {
    request: PendingNominalCastRequest,
    eligibility: OcastEligibilityState,
    eligible_boundary: Option<EligibleBoundaryDiagnosticEvidence>,
}

impl ClassifiedNominalCastRequest {
    pub(super) fn new(
        request: PendingNominalCastRequest,
        classification: &OcastEligibilityClassification,
    ) -> Self {
        let eligible_boundary = match &classification.outcome {
            OcastEligibilityOutcome::EligibleSourceBoundary {
                boundary,
                kind,
                evidence,
                ..
            } => Some(EligibleBoundaryDiagnosticEvidence {
                boundary: *boundary,
                kind: *kind,
                derivation: evidence.diagnostic_kind(),
                parameter_bound: match evidence {
                    EligibleBoundaryEvidence::OneSidedReplayPair {
                        replay,
                        source_parent,
                        ..
                    } => Some(match source_parent {
                        ReplaySourceParent::Lower => replay.lower,
                        ReplaySourceParent::Upper => replay.upper,
                    }),
                    EligibleBoundaryEvidence::RootRelation { .. }
                    | EligibleBoundaryEvidence::SharedReplayPair { .. } => None,
                },
            }),
            OcastEligibilityOutcome::InternalOnly { .. }
            | OcastEligibilityOutcome::Incomplete { .. } => None,
        };
        Self {
            request,
            eligibility: classification.state(),
            eligible_boundary,
        }
    }

    #[cfg(test)]
    pub(super) fn eligibility(&self) -> OcastEligibilityState {
        self.eligibility
    }

    pub(super) fn into_eligible(self) -> Option<EligibleNominalCastRequest> {
        let evidence = self.eligible_boundary?;
        Some(EligibleNominalCastRequest {
            request: self.request,
            evidence,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EligibleBoundaryDiagnosticEvidence {
    boundary: SourceBoundaryId,
    kind: ConstraintOriginKind,
    derivation: EligibleBoundaryDiagnosticKind,
    parameter_bound: Option<BoundRecordId>,
}

pub(super) struct EligibleNominalCastRequest {
    request: PendingNominalCastRequest,
    evidence: EligibleBoundaryDiagnosticEvidence,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum OcastActivationDecision {
    NoAction,
    MissingCast {
        source: Vec<String>,
        target: Vec<String>,
    },
    AmbiguousCast {
        source: Vec<String>,
        target: Vec<String>,
        candidates: Vec<DefId>,
    },
}

pub(super) fn plan_eligible_ocast_activation(
    request: &EligibleNominalCastRequest,
    casts: &CastTable,
) -> OcastActivationDecision {
    let request = &request.request;
    match casts.resolve_value(&request.source, &request.target) {
        OrdinaryCastResolution::Missing => OcastActivationDecision::MissingCast {
            source: request.source.clone(),
            target: request.target.clone(),
        },
        OrdinaryCastResolution::Unique(_) => OcastActivationDecision::NoAction,
        OrdinaryCastResolution::Ambiguous(rules) => {
            let mut candidates = rules
                .into_iter()
                .map(|rule| {
                    rule.def
                        .expect("every production ordinary-cast rule has a definition identity")
                })
                .collect::<Vec<_>>();
            candidates.sort_by_key(|candidate| candidate.0);
            OcastActivationDecision::AmbiguousCast {
                source: request.source.clone(),
                target: request.target.clone(),
                candidates,
            }
        }
    }
}

impl AnalysisSession {
    pub(crate) fn activate_eligible_ocast_diagnostics(
        &mut self,
        classified: Vec<ClassifiedNominalCastRequest>,
    ) {
        for classified in classified {
            let Some(request) = classified.into_eligible() else {
                // Internal-only requests are not source cast boundaries. Incomplete provenance is
                // deliberately fail-open, so neither state reaches cardinality resolution.
                continue;
            };
            match plan_eligible_ocast_activation(&request, &self.casts) {
                OcastActivationDecision::NoAction => {}
                OcastActivationDecision::MissingCast { source, target } => {
                    let (source_span, explanation) =
                        self.missing_cast_explanation(&request, &source, &target);
                    self.diagnostics
                        .push(AnalysisDiagnostic::MissingImplicitCast {
                            source,
                            target,
                            source_span,
                            explanation,
                        });
                }
                OcastActivationDecision::AmbiguousCast {
                    source,
                    target,
                    candidates,
                } => {
                    self.diagnostics
                        .push(AnalysisDiagnostic::AmbiguousImplicitCast {
                            source,
                            target,
                            candidates,
                            source_span: None,
                        });
                }
            }
        }
    }

    fn missing_cast_explanation(
        &self,
        request: &EligibleNominalCastRequest,
        source: &[String],
        target: &[String],
    ) -> (Option<crate::SourceSpan>, Option<DiagnosticTypeExplanation>) {
        if request.evidence.kind != ConstraintOriginKind::ApplicationArgument {
            return (None, None);
        }
        let Some(provenance) = self
            .source_boundary_provenance
            .application_argument(request.evidence.boundary)
        else {
            return (None, None);
        };
        let derivation = match request.evidence.derivation {
            EligibleBoundaryDiagnosticKind::RootRelation => DiagnosticTypeDerivation::RootRelation,
            EligibleBoundaryDiagnosticKind::SharedReplayPair => {
                DiagnosticTypeDerivation::SharedReplayPair
            }
            EligibleBoundaryDiagnosticKind::OneSidedReplayPair => {
                DiagnosticTypeDerivation::OneSidedReplayPair
            }
        };
        let explanation = DiagnosticTypeExplanation {
            source: source.to_vec(),
            target: target.to_vec(),
            derivation,
            related_sites: vec![
                DiagnosticTypeExplanationSite {
                    role: DiagnosticTypeExplanationSiteRole::InferredExpression,
                    source_span: provenance.argument_span.clone(),
                },
                DiagnosticTypeExplanationSite {
                    role: DiagnosticTypeExplanationSiteRole::RequiredApplicationCallee,
                    source_span: provenance.callee_span.clone(),
                },
            ],
            body_use: self.missing_cast_body_use(request),
        };
        (Some(provenance.application_span.clone()), Some(explanation))
    }

    fn missing_cast_body_use(
        &self,
        request: &EligibleNominalCastRequest,
    ) -> Option<DiagnosticTypeExplanationSite> {
        let parameter_bound = request.evidence.parameter_bound?;
        let explanation = self
            .infer
            .constraints()
            .why_constraint(
                request.request.producer,
                ExplanationBudget::parameter_body_diagnostic(),
            )
            .ok()?;
        if explanation.completeness != ExplanationCompleteness::Complete {
            return None;
        }
        let projection = project_parameter_body_requirements(
            request.request.producer,
            parameter_bound,
            &explanation,
        );
        if projection.completeness != ExplanationCompleteness::Complete {
            return None;
        }
        let witness = projection.requirements.first()?;
        if generalized_scheme_path_reaches_origin_kind(
            &explanation,
            witness.generalized_witness,
            ConstraintOriginKind::Annotation,
        ) {
            return None;
        }
        let provenance = self
            .source_boundary_provenance
            .body_requirement(witness.boundary)?;
        let kind = match witness.kind {
            BodyRequirementKind::BooleanCondition => {
                BodyRequirementDiagnosticKind::BooleanCondition
            }
            BodyRequirementKind::OperatorOperand { .. } => {
                BodyRequirementDiagnosticKind::OperatorOperand
            }
            BodyRequirementKind::PatternGuard => BodyRequirementDiagnosticKind::PatternGuard,
            BodyRequirementKind::CalleeArgument { .. } => {
                BodyRequirementDiagnosticKind::CalleeArgument
            }
        };
        Some(DiagnosticTypeExplanationSite {
            role: DiagnosticTypeExplanationSiteRole::RequiredByBodyUse(kind),
            source_span: provenance.use_span.clone(),
        })
    }
}

#[cfg(test)]
mod tests {
    use poly::expr::Arena as PolyArena;
    use poly::types::{Neg, Pos, Scheme};

    use super::*;
    use crate::analysis::AnalysisSession;
    use crate::constraints::{ConstraintOriginKind, OriginId};

    const SOURCE: &[&str] = &["source"];
    const TARGET: &[&str] = &["target"];

    #[test]
    fn eligible_missing_cast_plans_missing_decision() {
        let (mut session, classified) = classified_request(TestOrigin::Eligible);
        let eligible = classified
            .clone()
            .into_eligible()
            .expect("eligible source boundary");

        assert_eq!(
            plan_eligible_ocast_activation(&eligible, &session.casts),
            OcastActivationDecision::MissingCast {
                source: path(SOURCE),
                target: path(TARGET),
            }
        );
        session.activate_eligible_ocast_diagnostics(vec![classified]);
        assert_eq!(
            session.take_diagnostics(),
            vec![AnalysisDiagnostic::MissingImplicitCast {
                source: path(SOURCE),
                target: path(TARGET),
                source_span: None,
                explanation: None,
            }]
        );
    }

    #[test]
    fn eligible_unique_cast_plans_no_action() {
        let (mut session, classified) = classified_request(TestOrigin::Eligible);
        insert_cast(&mut session, 10);
        let eligible = classified
            .clone()
            .into_eligible()
            .expect("eligible source boundary");

        assert_eq!(
            plan_eligible_ocast_activation(&eligible, &session.casts),
            OcastActivationDecision::NoAction
        );
        session.activate_eligible_ocast_diagnostics(vec![classified]);
        assert!(session.take_diagnostics().is_empty());
    }

    #[test]
    fn eligible_ambiguous_cast_candidates_are_sorted_by_definition_identity() {
        let results = [[20, 10], [10, 20]].map(|order| {
            let (mut session, classified) = classified_request(TestOrigin::Eligible);
            for def in order {
                insert_cast(&mut session, def);
            }
            let eligible = classified
                .clone()
                .into_eligible()
                .expect("eligible source boundary");
            let decision = plan_eligible_ocast_activation(&eligible, &session.casts);
            session.activate_eligible_ocast_diagnostics(vec![classified]);
            (decision, session.take_diagnostics())
        });

        let expected = OcastActivationDecision::AmbiguousCast {
            source: path(SOURCE),
            target: path(TARGET),
            candidates: vec![DefId(10), DefId(20)],
        };
        let expected_diagnostic = AnalysisDiagnostic::AmbiguousImplicitCast {
            source: path(SOURCE),
            target: path(TARGET),
            candidates: vec![DefId(10), DefId(20)],
            source_span: None,
        };
        assert_eq!(results[0].0, expected);
        assert_eq!(results[1].0, results[0].0);
        assert_eq!(
            results.map(|(_, diagnostics)| diagnostics),
            [vec![expected_diagnostic.clone()], vec![expected_diagnostic]]
        );
    }

    #[test]
    fn non_eligible_classifications_cannot_be_passed_to_the_planner() {
        let (mut internal_session, internal) = classified_request(TestOrigin::Internal);
        assert_eq!(internal.eligibility(), OcastEligibilityState::InternalOnly);
        assert!(internal.clone().into_eligible().is_none());
        internal_session.activate_eligible_ocast_diagnostics(vec![internal]);
        assert!(internal_session.take_diagnostics().is_empty());

        let (mut incomplete_session, incomplete) = classified_request(TestOrigin::Unknown);
        assert_eq!(incomplete.eligibility(), OcastEligibilityState::Incomplete);
        assert!(incomplete.clone().into_eligible().is_none());
        incomplete_session.activate_eligible_ocast_diagnostics(vec![incomplete]);
        assert!(incomplete_session.take_diagnostics().is_empty());
    }

    #[test]
    fn repeated_canonical_missing_producer_emits_one_diagnostic() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let origin = session
            .infer
            .alloc_source_boundary(ConstraintOriginKind::ApplicationArgument)
            .origin();
        let lower = session.infer.alloc_pos(Pos::Con(path(SOURCE), Vec::new()));
        let upper = session.infer.alloc_neg(Neg::Con(path(TARGET), Vec::new()));

        session.infer.subtype(lower, upper, origin);
        session.route_constraint_events();
        session.infer.subtype(lower, upper, origin);
        session.route_constraint_events();

        let classified = session.classify_pending_ocast_eligibility_at_quiescence();
        assert_eq!(classified.len(), 1);
        session.activate_eligible_ocast_diagnostics(classified);
        assert_eq!(session.take_diagnostics().len(), 1);
    }

    #[derive(Clone, Copy)]
    enum TestOrigin {
        Eligible,
        Internal,
        Unknown,
    }

    fn classified_request(origin: TestOrigin) -> (AnalysisSession, ClassifiedNominalCastRequest) {
        let mut session = AnalysisSession::new(PolyArena::new());
        let classified = classified_request_with_origin(&mut session, origin);
        (session, classified)
    }

    fn classified_request_with_origin(
        session: &mut AnalysisSession,
        origin: TestOrigin,
    ) -> ClassifiedNominalCastRequest {
        let origin = match origin {
            TestOrigin::Eligible => session
                .infer
                .alloc_source_boundary(ConstraintOriginKind::ApplicationArgument)
                .origin(),
            TestOrigin::Internal => OriginId::internal(),
            TestOrigin::Unknown => OriginId::unknown_internal(),
        };
        let lower = session.infer.alloc_pos(Pos::Con(path(SOURCE), Vec::new()));
        let upper = session.infer.alloc_neg(Neg::Con(path(TARGET), Vec::new()));
        session.infer.subtype(lower, upper, origin);
        session.route_constraint_events();
        let mut classified = session.classify_pending_ocast_eligibility_at_quiescence();
        assert_eq!(classified.len(), 1);
        classified.pop().unwrap()
    }

    fn insert_cast(session: &mut AnalysisSession, def: u32) {
        session
            .casts
            .insert_value(DefId(def), path(SOURCE), path(TARGET), empty_scheme());
    }

    fn empty_scheme() -> Scheme {
        Scheme {
            quantifiers: Vec::new(),
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate: poly::types::PosId(0),
        }
    }

    fn path(parts: &[&str]) -> Vec<String> {
        parts.iter().map(|part| (*part).to_string()).collect()
    }
}
