//! Quiescent ordinary-cast diagnostic activation.
//!
//! This module retains the exact nominal event payload beside its settled eligibility, plans the
//! cast-table cardinality outcome, and emits diagnostics only for proven source boundaries. The
//! solver's eager candidate instantiation remains unchanged; activation is a diagnostic overlay.

use poly::cast_resolution::OrdinaryCastResolution;
use poly::expr::DefId;
use poly::types::{NegId, PosId};

use crate::casts::CastTable;
use crate::constraints::ocast_eligibility::OcastEligibilityState;
use crate::constraints::{ConstraintRecordId, ConstraintWeights};

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
}

impl ClassifiedNominalCastRequest {
    pub(super) fn new(
        request: PendingNominalCastRequest,
        eligibility: OcastEligibilityState,
    ) -> Self {
        Self {
            request,
            eligibility,
        }
    }

    #[cfg(test)]
    pub(super) fn eligibility(&self) -> OcastEligibilityState {
        self.eligibility
    }

    pub(super) fn into_eligible(self) -> Option<EligibleNominalCastRequest> {
        (self.eligibility == OcastEligibilityState::EligibleSourceBoundary)
            .then_some(EligibleNominalCastRequest(self.request))
    }
}

pub(super) struct EligibleNominalCastRequest(PendingNominalCastRequest);

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
    let request = &request.0;
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
                    self.diagnostics
                        .push(AnalysisDiagnostic::MissingImplicitCast {
                            source,
                            target,
                            source_span: None,
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
