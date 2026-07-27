//! Source projection and deduplication for fixed concrete-head mismatch diagnostics.
//!
//! The constraint event carries semantic identity only. This module performs one bounded
//! provenance query, then projects exact source-boundary metadata without rescanning source text.

use super::*;

use crate::analysis::{SubtypeMismatchSite, SubtypeMismatchSiteRole};
use crate::constraints::UnsatisfiedSubtypeShapeEvent;
use crate::constraints::explain::{ExplanationBudget, ExplanationCompleteness};

const ACTUAL_SITE_PRIORITY: u8 = 0;
const EXPECTED_SITE_PRIORITY: u8 = 1;
const BOUNDARY_SITE_PRIORITY: u8 = 2;

impl AnalysisSession {
    pub(super) fn record_unsatisfied_subtype_shape(&mut self, event: UnsatisfiedSubtypeShapeEvent) {
        let key = (event.producer, event.actual.clone(), event.expected.clone());
        if !self.unsatisfied_subtype_shape_diagnostic_keys.insert(key) {
            return;
        }

        let (source_span, related) = self.project_subtype_mismatch_sites(event.producer);
        self.diagnostics
            .push(AnalysisDiagnostic::UnsatisfiedSubtypeShape {
                actual: event.actual,
                expected: event.expected,
                producer: event.producer,
                source_span,
                related,
            });
    }

    fn project_subtype_mismatch_sites(
        &self,
        producer: ConstraintRecordId,
    ) -> (Option<crate::SourceSpan>, Vec<SubtypeMismatchSite>) {
        let Ok(explanation) = self
            .infer
            .constraints()
            .why_constraint(producer, ExplanationBudget::subtype_diagnostic())
        else {
            return (None, Vec::new());
        };
        if explanation.completeness != ExplanationCompleteness::Complete
            || explanation.truncation.is_some()
        {
            return (None, Vec::new());
        }

        let mut primary_candidates = Vec::<PrimaryCandidate>::new();
        let mut related = Vec::new();
        for leaf in explanation.source_leaves {
            match leaf.kind {
                crate::constraints::ConstraintOriginKind::ApplicationArgument => {
                    let Some(provenance) = self
                        .source_boundary_provenance
                        .application_argument(leaf.boundary)
                    else {
                        continue;
                    };
                    push_primary_candidate(
                        &mut primary_candidates,
                        ACTUAL_SITE_PRIORITY,
                        provenance.argument_span.clone(),
                    );
                    push_related(
                        &mut related,
                        SubtypeMismatchSiteRole::ExpectedRequirement,
                        provenance.callee_span.clone(),
                    );
                }
                crate::constraints::ConstraintOriginKind::BodyRequirement(_) => {
                    let Some(provenance) = self
                        .source_boundary_provenance
                        .body_requirement(leaf.boundary)
                    else {
                        continue;
                    };
                    push_primary_candidate(
                        &mut primary_candidates,
                        EXPECTED_SITE_PRIORITY,
                        provenance.use_span.clone(),
                    );
                    push_related(
                        &mut related,
                        SubtypeMismatchSiteRole::ExpectedRequirement,
                        provenance.use_span.clone(),
                    );
                }
                crate::constraints::ConstraintOriginKind::Pattern => {
                    let Some(source_span) = self.source_boundary_provenance.pattern(leaf.boundary)
                    else {
                        continue;
                    };
                    push_primary_candidate(
                        &mut primary_candidates,
                        BOUNDARY_SITE_PRIORITY,
                        source_span.clone(),
                    );
                    push_related(
                        &mut related,
                        SubtypeMismatchSiteRole::PatternOrReturnBoundary,
                        source_span.clone(),
                    );
                }
                // Annotation and return origins already participate in the bounded canonical
                // query. Their current allocation sites do not retain exact SourceSpan metadata,
                // so the honest projection is no candidate rather than a nearby fabricated span.
                crate::constraints::ConstraintOriginKind::Annotation
                | crate::constraints::ConstraintOriginKind::Return
                | crate::constraints::ConstraintOriginKind::Field
                | crate::constraints::ConstraintOriginKind::Assignment
                | crate::constraints::ConstraintOriginKind::Internal
                | crate::constraints::ConstraintOriginKind::UnknownInternal => {}
            }
        }

        let source_span = choose_unique_primary(primary_candidates);
        if let Some(primary) = &source_span {
            related.retain(|site| site.source_span != *primary);
        }
        (source_span, related)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct PrimaryCandidate {
    priority: u8,
    source_span: crate::SourceSpan,
}

fn push_primary_candidate(
    candidates: &mut Vec<PrimaryCandidate>,
    priority: u8,
    source_span: crate::SourceSpan,
) {
    if candidates
        .iter()
        .any(|candidate| candidate.priority == priority && candidate.source_span == source_span)
    {
        return;
    }
    candidates.push(PrimaryCandidate {
        priority,
        source_span,
    });
}

fn push_related(
    related: &mut Vec<SubtypeMismatchSite>,
    role: SubtypeMismatchSiteRole,
    source_span: crate::SourceSpan,
) {
    let site = SubtypeMismatchSite { role, source_span };
    if !related.contains(&site) {
        related.push(site);
    }
}

fn choose_unique_primary(candidates: Vec<PrimaryCandidate>) -> Option<crate::SourceSpan> {
    let priority = candidates
        .iter()
        .map(|candidate| candidate.priority)
        .min()?;
    let mut candidates = candidates
        .into_iter()
        .filter(|candidate| candidate.priority == priority);
    let primary = candidates.next()?.source_span;
    candidates.next().is_none().then_some(primary)
}

#[cfg(test)]
mod tests {
    use poly::expr::Arena as PolyArena;
    use poly::types::{Neg, Pos, TypeVar};
    use sources::{Path, SourceRange};

    use super::*;
    use crate::analysis::ConcreteSubtypeHead;
    use crate::constraints::{
        BodyRequirementKind, ConstraintOriginKind, ConstraintWeights, OriginId,
    };
    use crate::lowering::{
        ApplicationArgumentBoundaryProvenance, BodyRequirementBoundaryProvenance,
    };

    #[test]
    fn synthetic_event_projects_primary_and_related_sites_and_deduplicates() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let application = session
            .infer
            .alloc_source_boundary(ConstraintOriginKind::ApplicationArgument);
        assert!(
            session
                .source_boundary_provenance
                .insert_application_argument(
                    application.boundary(),
                    ApplicationArgumentBoundaryProvenance {
                        application_span: span(0, 12),
                        callee_span: span(0, 4),
                        argument_span: span(8, 12),
                    },
                )
        );
        session
            .infer
            .record_source_boundary_location(application.boundary());

        let requirement =
            session
                .infer
                .alloc_source_boundary(ConstraintOriginKind::BodyRequirement(
                    BodyRequirementKind::BooleanCondition,
                ));
        assert!(session.source_boundary_provenance.insert_body_requirement(
            requirement.boundary(),
            BodyRequirementBoundaryProvenance {
                use_span: span(20, 24),
                context_span: None,
            },
        ));
        session
            .infer
            .record_source_boundary_location(requirement.boundary());

        let lower = session
            .infer
            .alloc_pos(Pos::Con(vec!["actual".into()], Vec::new()));
        let upper = session
            .infer
            .alloc_neg(Neg::Con(vec!["expected".into()], Vec::new()));
        session.infer.subtype(lower, upper, application.origin());
        session.infer.subtype(lower, upper, requirement.origin());
        let producer = session
            .infer
            .constraints()
            .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("synthetic canonical producer");
        let event = UnsatisfiedSubtypeShapeEvent {
            actual: ConcreteSubtypeHead::Tuple(2),
            expected: ConcreteSubtypeHead::Function,
            producer,
        };

        session.record_unsatisfied_subtype_shape(event.clone());
        session.record_unsatisfied_subtype_shape(event);

        assert_eq!(
            session.take_diagnostics(),
            vec![AnalysisDiagnostic::UnsatisfiedSubtypeShape {
                actual: ConcreteSubtypeHead::Tuple(2),
                expected: ConcreteSubtypeHead::Function,
                producer,
                source_span: Some(span(8, 12)),
                related: vec![
                    SubtypeMismatchSite {
                        role: SubtypeMismatchSiteRole::ExpectedRequirement,
                        source_span: span(0, 4),
                    },
                    SubtypeMismatchSite {
                        role: SubtypeMismatchSiteRole::ExpectedRequirement,
                        source_span: span(20, 24),
                    },
                ],
            }]
        );
    }

    #[test]
    fn internal_only_event_remains_a_spanless_diagnostic() {
        let mut session = AnalysisSession::new(PolyArena::new());
        let lower = session.infer.alloc_pos(Pos::Tuple(Vec::new()));
        let upper = session
            .infer
            .alloc_neg(Neg::Con(vec!["expected".into()], Vec::new()));
        session
            .infer
            .subtype(lower, upper, OriginId::unknown_internal());
        let producer = session
            .infer
            .constraints()
            .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("synthetic internal producer");

        session.record_unsatisfied_subtype_shape(UnsatisfiedSubtypeShapeEvent {
            actual: ConcreteSubtypeHead::Tuple(0),
            expected: ConcreteSubtypeHead::Constructor(vec!["expected".into()]),
            producer,
        });

        let diagnostics = session.take_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        let AnalysisDiagnostic::UnsatisfiedSubtypeShape {
            source_span,
            related,
            ..
        } = &diagnostics[0]
        else {
            panic!("expected subtype-shape diagnostic");
        };
        assert_eq!(source_span, &None);
        assert!(related.is_empty());
    }

    #[test]
    fn incomplete_provenance_event_remains_a_spanless_diagnostic() {
        let mut session = AnalysisSession::new(PolyArena::new());
        session
            .infer
            .constraints_mut()
            .set_replay_derivation_budget_for_test(0, usize::MAX);
        let origin = session
            .infer
            .alloc_source_boundary(ConstraintOriginKind::ApplicationArgument)
            .origin();
        let lower = session
            .infer
            .alloc_pos(Pos::Con(vec!["actual".into()], Vec::new()));
        let upper = session
            .infer
            .alloc_neg(Neg::Con(vec!["expected".into()], Vec::new()));
        let pivot = TypeVar(0);
        session
            .infer
            .constrain_pos_to_var_direct_many([(lower, pivot)], origin);
        let pivot_pos = session.infer.alloc_pos(Pos::Var(pivot));
        session.infer.subtype(pivot_pos, upper, origin);
        let producer = session
            .infer
            .constraints()
            .debug_constraint_record_id(lower, ConstraintWeights::empty(), upper)
            .expect("synthetic incomplete replay producer");

        session.record_unsatisfied_subtype_shape(UnsatisfiedSubtypeShapeEvent {
            actual: ConcreteSubtypeHead::Constructor(vec!["actual".into()]),
            expected: ConcreteSubtypeHead::Constructor(vec!["expected".into()]),
            producer,
        });

        let diagnostics = session.take_diagnostics();
        assert_eq!(diagnostics.len(), 1);
        let AnalysisDiagnostic::UnsatisfiedSubtypeShape {
            source_span,
            related,
            ..
        } = &diagnostics[0]
        else {
            panic!("expected subtype-shape diagnostic");
        };
        assert_eq!(source_span, &None);
        assert!(related.is_empty());
    }

    fn span(start: usize, end: usize) -> crate::SourceSpan {
        crate::SourceSpan {
            file: Path::default(),
            range: SourceRange { start, end },
        }
    }
}
