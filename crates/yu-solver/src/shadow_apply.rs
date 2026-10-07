//! Experimental value projection only; no source Apply typing or admission.
use crate::*;
use std::sync::Arc;
use yu_hir::HirErrorKind;

/// Every entry remains unresolved, including after successful structural solving.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnresolvedPremise {
    CandidatePureEffectModelUnresolved,
    ApplicationTypingRule,
    CompleteInvocationImage,
    WholeArgumentProviderCompatibility,
    SourceTypingAndAdmission,
    RoleEntryAndProtection,
    WholeTupleScopeTransport,
    GeneralizationAndFreshUseCorrespondence,
    OriginalGenCall0MembershipSourceReferenceOnly,
    CompleteFunctionInterpretation,
    QIndependentCallViewFormation,
    EventOutputCorrespondence,
    ImmediateCallEffectPositionFormation,
    TypedOccurrenceIntroduction,
    FormalApplicability,
    DirectionalProtection,
}
pub const UNRESOLVED: &[UnresolvedPremise] = &[
    UnresolvedPremise::CandidatePureEffectModelUnresolved,
    UnresolvedPremise::ApplicationTypingRule,
    UnresolvedPremise::CompleteInvocationImage,
    UnresolvedPremise::WholeArgumentProviderCompatibility,
    UnresolvedPremise::SourceTypingAndAdmission,
    UnresolvedPremise::RoleEntryAndProtection,
    UnresolvedPremise::WholeTupleScopeTransport,
    UnresolvedPremise::GeneralizationAndFreshUseCorrespondence,
    UnresolvedPremise::OriginalGenCall0MembershipSourceReferenceOnly,
    UnresolvedPremise::CompleteFunctionInterpretation,
    UnresolvedPremise::QIndependentCallViewFormation,
    UnresolvedPremise::EventOutputCorrespondence,
    UnresolvedPremise::ImmediateCallEffectPositionFormation,
    UnresolvedPremise::TypedOccurrenceIntroduction,
    UnresolvedPremise::FormalApplicability,
    UnresolvedPremise::DirectionalProtection,
];
/// Same actual returned provider/world/whole carrier/source incidence/original
/// shared scope/xi are all unresolved under WholeArgumentProviderCompatibility.
pub struct CandidateCall {
    pub occurrence: HirOccurrenceId,
    pub callee: HirOccurrenceId,
    pub argument: HirOccurrenceId,
    pub unresolved: &'static [UnresolvedPremise],
}
#[derive(Debug)]
pub enum CandidateError {
    Unsupported,
    Collection(CollectionAvailabilityError),
    Solve(SolveAvailabilityError),
}
/// Owns a private solver result which cannot be published as a SolvedModule.
/// Invocation/evaluation effects are intentionally absent from this API.
pub struct CandidateValueObservation {
    solved: SolvedModule,
    calls: Vec<CandidateCall>,
}
pub struct CandidateExport<'a> {
    pub unresolved: &'static [UnresolvedPremise],
    pub value: SolvedValue,
    scheme: crate::shadow_f5::ClosedSchemeRef<'a>,
}
impl CandidateExport<'_> {
    /// Whole four-port observation under the named unresolved effect model.
    pub fn endpoints(&self) -> yu_types::ClosedValueSchemeView<'_> {
        self.scheme.endpoints()
    }
}
/// Historical row identity within this candidate's ordinary use substitution.
pub struct CandidateFreshRow<'a> {
    capture: &'a ShadowFreshCapture,
    use_id: &'a DefinitionUseId,
    row: u32,
}
impl CandidateFreshRow<'_> {
    pub fn source_use(&self) -> &HirOccurrenceId {
        self.use_id.occurrence()
    }
    pub fn same_identity(&self, other: &Self) -> bool {
        std::ptr::eq(self.capture, other.capture) && self.row == other.row
    }
}
impl CandidateValueObservation {
    pub fn solve(hir: Arc<HirModule>) -> Result<Self, CandidateError> {
        let mut calls = Vec::new();
        let mut permitted_errors = HashSet::new();
        fn check(
            expr: &ResolvedExpr,
            calls: &mut Vec<CandidateCall>,
            errors: &mut HashSet<yu_hir::HirErrorId>,
        ) -> bool {
            match expr {
                ResolvedExpr::Integer { .. }
                | ResolvedExpr::Name {
                    resolution: NameResolution::Resolved(_),
                    ..
                } => true,
                ResolvedExpr::Group { inner, .. } => check(inner, calls, errors),
                ResolvedExpr::Apply {
                    occurrence,
                    callee,
                    argument,
                    errors: ids,
                    ..
                } => {
                    errors.extend(ids.iter().copied());
                    calls.push(CandidateCall {
                        occurrence: occurrence.clone(),
                        callee: callee.occurrence().clone(),
                        argument: argument.occurrence().clone(),
                        unresolved: UNRESOLVED,
                    });
                    check(callee, calls, errors) && check(argument, calls, errors)
                }
                ResolvedExpr::Lambda {
                    parameter, body, ..
                } => {
                    matches!(body.as_ref(), ResolvedExpr::Integer { .. })
                        || matches!(body.as_ref(), ResolvedExpr::Name { resolution: NameResolution::Parameter(p), .. } if p == parameter)
                }
                _ => false,
            }
        }
        for item in hir.items() {
            let expr = match item {
                HirItem::Binding(b) => b.value(),
                HirItem::Expression(e) if matches!(e, ResolvedExpr::Integer { .. }) => e,
                _ => return Err(CandidateError::Unsupported),
            };
            if !check(expr, &mut calls, &mut permitted_errors) {
                return Err(CandidateError::Unsupported);
            }
        }
        if hir.errors().iter().any(|e| {
            !permitted_errors.contains(&e.id()) || e.kind() != HirErrorKind::UnsupportedExpression
        }) {
            return Err(CandidateError::Unsupported);
        }
        let batch = ConstraintBatch::collect_mode(hir, true).map_err(CandidateError::Collection)?;
        if batch
            .scc_plan()
            .components_in_dependency_first_order()
            .any(|c| {
                !batch
                    .scc_plan()
                    .internal_uses(c)
                    .expect("owned SCC")
                    .is_empty()
            })
        {
            return Err(CandidateError::Unsupported);
        }
        let solved =
            SolvedModule::solve_with_shadow_fresh_capture(batch).map_err(CandidateError::Solve)?;
        Ok(Self { solved, calls })
    }
    /// Ordinary incoming source-use substitution; aliases receive one route,
    /// with no second candidate-specific freshening.
    pub fn fresh_rows(&self, occurrence: &HirOccurrenceId) -> Option<Vec<CandidateFreshRow<'_>>> {
        let capture = self.solved.shadow_fresh_capture.as_ref()?;
        let route = capture
            .routes
            .iter()
            .find(|r| r.use_id.occurrence == *occurrence && r.complete)?;
        Some(
            route
                .rows
                .iter()
                .map(|(_, _, row)| CandidateFreshRow {
                    capture,
                    use_id: &route.use_id,
                    row: *row,
                })
                .collect(),
        )
    }
    pub fn calls(&self) -> &[CandidateCall] {
        &self.calls
    }
    /// Candidate conflicts never establish source rejection.
    pub fn candidate_conflicts(&self) -> &[SolverError] {
        self.solved.errors()
    }
    pub fn export(&self, root: &DefinitionRootId) -> Result<CandidateExport<'_>, ArtifactMismatch> {
        Ok(CandidateExport {
            unresolved: UNRESOLVED,
            value: self.solved.root_value_for(root)?,
            scheme: self.solved.shadow_closed_schemes().for_root(root)?,
        })
    }
}
impl ConstraintBatch {
    fn candidate_component(
        &mut self,
        occurrence: &HirOccurrenceId,
    ) -> Result<Term, CollectionAvailabilityError> {
        self.occurrence_component(occurrence.clone(), ComponentKind::Value)?;
        self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
        let positions = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
        };
        self.occurrence_component_positions
            .insert(occurrence.clone(), positions);
        Ok(self.component_term_at(positions.value))
    }
    pub(super) fn emit_candidate_value<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        root: Option<&DefinitionRootId>,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<Term, CollectionAvailabilityError> {
        let occurrence = expr.occurrence();
        let value = match expr {
            ResolvedExpr::Integer { .. } => {
                self.emit_integer(occurrence.clone(), None)?;
                self.component_term_at(self.occurrence_component_positions[occurrence].value)
            }
            ResolvedExpr::Name {
                resolution: NameResolution::Resolved(target),
                ..
            } => {
                self.emit_resolved_binding_name(occurrence.clone(), None)?;
                uses.push(PendingDefinitionUse {
                    parent_ordinal: parent
                        .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?
                        .ordinal(),
                    target,
                    occurrence: occurrence.clone(),
                });
                self.component_term_at(self.occurrence_component_positions[occurrence].value)
            }
            ResolvedExpr::Group { inner, .. } => {
                let child = self.emit_candidate_value(inner, None, parent, uses)?;
                let value = self.candidate_component(occurrence)?;
                self.emit(occurrence.clone(), 0, child, value)?;
                value
            }
            ResolvedExpr::Apply {
                callee, argument, ..
            } => {
                let callee = self.emit_candidate_value(callee, None, parent, uses)?;
                let argument = self.emit_candidate_value(argument, None, parent, uses)?;
                let value = self.candidate_component(occurrence)?;
                let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                // Only CandidatePureEffectModelUnresolved: neither source
                // argument evaluation nor whole-Apply/invocation effect typing.
                let demand = self
                    .active_term_builder()
                    .intern(TermNode::NegativeFunction {
                        argument,
                        argument_effect: bottom,
                        result_effect: empty,
                        result: value,
                    })?;
                self.emit(occurrence.clone(), 0, callee, demand)?;
                value
            }
            _ => return Err(CollectionAvailabilityError::MissingDefinitionEndpoint),
        };
        if let Some(root) = root {
            let component = self.root_value_component_for_collect(root)?;
            self.emit(
                occurrence.clone(),
                10,
                value,
                self.term_for_component(&component),
            )?;
        }
        Ok(value)
    }
}
