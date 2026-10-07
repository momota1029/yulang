//! Experimental value projection only; no source Apply typing or admission.
use crate::*;
use std::sync::Arc;
use yu_hir::HirErrorKind;

/// Every entry remains unresolved, including after successful structural solving.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum UnresolvedPremise {
    CandidatePureEffectModelUnresolved,
    CandidateOwnRowGeneralizationModelUnresolved,
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
    UnresolvedPremise::CandidateOwnRowGeneralizationModelUnresolved,
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
        // Preflight bounds recursive emission without consuming the native stack.
        // Only retained HIR shapes are admitted; no CST reconstruction occurs.
        for item in hir.items() {
            let expr = match item {
                HirItem::Binding(b) => b.value(),
                HirItem::Expression(e) if matches!(e, ResolvedExpr::Integer { .. }) => e,
                _ => return Err(CandidateError::Unsupported),
            };
            preflight_expression(expr, &mut calls, &mut permitted_errors)?;
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
fn preflight_expression(
    expr: &ResolvedExpr,
    calls: &mut Vec<CandidateCall>,
    permitted_errors: &mut HashSet<yu_hir::HirErrorId>,
) -> Result<(), CandidateError> {
    let mut pending = Vec::new();
    pending
        .try_reserve(1)
        .map_err(|_| CandidateError::Unsupported)?;
    pending.push((expr, 1usize, None));
    while let Some((expr, depth, formal)) = pending.pop() {
        if depth > 128 {
            return Err(CandidateError::Unsupported);
        }
        pending
            .try_reserve(2)
            .map_err(|_| CandidateError::Unsupported)?;
        match expr {
            ResolvedExpr::Integer { .. }
            | ResolvedExpr::Name {
                resolution: NameResolution::Resolved(_),
                ..
            } => {}
            ResolvedExpr::Name {
                resolution: NameResolution::Parameter(p),
                ..
            } if formal == Some(p) => {}
            ResolvedExpr::Group { inner, .. } => pending.push((inner, depth + 1, formal)),
            ResolvedExpr::Apply {
                occurrence,
                callee,
                argument,
                errors,
                ..
            } => {
                permitted_errors
                    .try_reserve(errors.len())
                    .map_err(|_| CandidateError::Unsupported)?;
                permitted_errors.extend(errors.iter().copied());
                calls
                    .try_reserve(1)
                    .map_err(|_| CandidateError::Unsupported)?;
                calls.push(CandidateCall {
                    occurrence: occurrence.clone(),
                    callee: callee.occurrence().clone(),
                    argument: argument.occurrence().clone(),
                    unresolved: UNRESOLVED,
                });
                pending.push((argument, depth + 1, formal));
                pending.push((callee, depth + 1, formal));
            }
            ResolvedExpr::Lambda {
                parameter, body, ..
            } if depth == 1 => {
                pending.push((body, depth + 1, Some(parameter)));
            }
            _ => return Err(CandidateError::Unsupported),
        }
    }
    Ok(())
}

#[derive(Clone, Copy, Debug)]
pub(super) enum CandidateEndpoint {
    Component(usize),
    Parameter(usize),
}
#[derive(Clone, Debug)]
pub(super) enum CandidateRelation {
    Group {
        child: CandidateEndpoint,
        result: usize,
    },
    Apply {
        callee: CandidateEndpoint,
        argument: CandidateEndpoint,
        result: usize,
    },
}
#[derive(Clone, Debug)]
pub(super) struct CandidateConstraintRecipe {
    occurrence: HirOccurrenceId,
    relation: CandidateRelation,
    pub(super) after_collected_fact: usize,
}
impl ConstraintBatch {
    fn candidate_component(
        &mut self,
        occurrence: &HirOccurrenceId,
    ) -> Result<ComponentPositions, CollectionAvailabilityError> {
        self.occurrence_component(occurrence.clone(), ComponentKind::Value)?;
        self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
        let positions = ComponentPositions {
            value: self.components.len() - 2,
            effect: self.components.len() - 1,
        };
        self.occurrence_component_positions
            .insert(occurrence.clone(), positions);
        self.candidate_pure_effect(occurrence, positions.effect)?;
        Ok(positions)
    }
    fn candidate_pure_effect(
        &mut self,
        occurrence: &HirOccurrenceId,
        position: usize,
    ) -> Result<(), CollectionAvailabilityError> {
        // These bounds belong only to CandidatePureEffectModelUnresolved.
        let effect = self.component_term_at(position);
        let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
        let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
        self.emit(occurrence.clone(), 1, bottom, effect)?;
        self.emit(occurrence.clone(), 2, effect, empty)
    }
    fn retain_candidate_relation(
        &mut self,
        occurrence: &HirOccurrenceId,
        relation: CandidateRelation,
    ) -> Result<(), CollectionAvailabilityError> {
        self.candidate_recipes
            .try_reserve(1)
            .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.counters.emitted_facts = self
            .counters
            .emitted_facts
            .checked_add(1)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.counters.generated_work_items = self
            .counters
            .generated_work_items
            .checked_add(1)
            .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        self.candidate_recipes.push(CandidateConstraintRecipe {
            occurrence: occurrence.clone(),
            relation,
            after_collected_fact: self.occurrences.len(),
        });
        Ok(())
    }
    pub(super) fn emit_candidate_value<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        root: Option<&DefinitionRootId>,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(), CollectionAvailabilityError> {
        if let ResolvedExpr::Lambda {
            occurrence,
            parameter,
            body,
            ..
        } = expr
        {
            let root = root.ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?;
            self.parameter_recipes
                .try_reserve(1)
                .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
            let parameter_position = self.parameter_recipes.len();
            self.parameter_recipes.push(parameter.clone());
            let (value, effect) =
                self.emit_candidate_expression(body, Some(parameter_position), parent, uses)?;
            self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
            let lambda_effect_component = self.components.len() - 1;
            let lambda_effect = self.component_term_at(lambda_effect_component);
            let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
            let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
            self.emit(occurrence.clone(), 0, bottom, lambda_effect)?;
            self.emit(occurrence.clone(), 1, lambda_effect, empty)?;
            self.lambda_recipes
                .try_reserve(1)
                .map_err(|_| CollectionAvailabilityError::ComponentIdentityExhausted)?;
            self.lambda_recipes.push(LambdaRecipe {
                occurrence: occurrence.clone(),
                parameter_position,
                root_component: self.root_component_positions[root].component,
                body_value_component: match value {
                    CandidateEndpoint::Component(p) => Some(p),
                    CandidateEndpoint::Parameter(_) => None,
                },
                body_effect_component: effect,
                lambda_effect_component,
                after_collected_fact: self.occurrences.len(),
            });
            self.counters.emitted_facts = self
                .counters
                .emitted_facts
                .checked_add(1)
                .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
            self.counters.generated_work_items = self
                .counters
                .generated_work_items
                .checked_add(1)
                .ok_or(CollectionAvailabilityError::ComponentIdentityExhausted)?;
        } else {
            let (value, _) = self.emit_candidate_expression(expr, None, parent, uses)?;
            if let Some(root) = root {
                let CandidateEndpoint::Component(position) = value else {
                    return Err(CollectionAvailabilityError::MissingDefinitionEndpoint);
                };
                let component = self.root_value_component_for_collect(root)?;
                self.emit(
                    expr.occurrence().clone(),
                    10,
                    self.component_term_at(position),
                    self.term_for_component(&component),
                )?;
            }
        }
        Ok(())
    }
    fn emit_candidate_expression<'a>(
        &mut self,
        expr: &'a ResolvedExpr,
        formal: Option<usize>,
        parent: Option<&DefinitionOrderId>,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(CandidateEndpoint, usize), CollectionAvailabilityError> {
        let occurrence = expr.occurrence();
        let positions = match expr {
            ResolvedExpr::Integer { .. } => {
                self.emit_integer(occurrence.clone(), None)?;
                self.occurrence_component_positions[occurrence]
            }
            ResolvedExpr::Name {
                resolution: NameResolution::Resolved(target),
                ..
            } => {
                self.emit_resolved_binding_name(occurrence.clone(), None)?;
                let old_capacity = uses.capacity();
                uses.try_reserve(1)
                    .map_err(|_| CollectionAvailabilityError::DefinitionUseIdentityExhausted)?;
                uses.push(PendingDefinitionUse {
                    parent_ordinal: parent
                        .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?
                        .ordinal(),
                    target,
                    occurrence: occurrence.clone(),
                });
                self.counters
                    .definition_use_endpoint_workspace_peak_capacity = self
                    .counters
                    .definition_use_endpoint_workspace_peak_capacity
                    .max(uses.capacity());
                if uses.capacity() != old_capacity {
                    self.counters
                        .definition_use_endpoint_workspace_capacity_growths += 1;
                }
                self.occurrence_component_positions[occurrence]
            }
            ResolvedExpr::Name {
                resolution: NameResolution::Parameter(parameter),
                ..
            } => {
                let position = formal
                    .filter(|p| &self.parameter_recipes[*p] == parameter)
                    .ok_or(CollectionAvailabilityError::MissingDefinitionEndpoint)?;
                self.occurrence_component(occurrence.clone(), ComponentKind::Effect)?;
                let effect = self.components.len() - 1;
                let term = self.component_term_at(effect);
                let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                self.emit(occurrence.clone(), 0, bottom, term)?;
                self.emit(occurrence.clone(), 1, term, empty)?;
                return Ok((CandidateEndpoint::Parameter(position), effect));
            }
            ResolvedExpr::Group { inner, .. } => {
                let (child, _) = self.emit_candidate_expression(inner, formal, parent, uses)?;
                let positions = self.candidate_component(occurrence)?;
                self.retain_candidate_relation(
                    occurrence,
                    CandidateRelation::Group {
                        child,
                        result: positions.value,
                    },
                )?;
                positions
            }
            ResolvedExpr::Apply {
                callee, argument, ..
            } => {
                let (callee, _) = self.emit_candidate_expression(callee, formal, parent, uses)?;
                let (argument, _) =
                    self.emit_candidate_expression(argument, formal, parent, uses)?;
                let positions = self.candidate_component(occurrence)?;
                self.retain_candidate_relation(
                    occurrence,
                    CandidateRelation::Apply {
                        callee,
                        argument,
                        result: positions.value,
                    },
                )?;
                positions
            }
            _ => return Err(CollectionAvailabilityError::MissingDefinitionEndpoint),
        };
        Ok((
            CandidateEndpoint::Component(positions.value),
            positions.effect,
        ))
    }
}
impl InferenceSession {
    fn candidate_endpoint(
        &mut self,
        endpoint: CandidateEndpoint,
        polarity: Polarity,
    ) -> Result<Term, SolveAvailabilityError> {
        let row = match endpoint {
            CandidateEndpoint::Component(position) => self.live_components[position].ordinal,
            CandidateEndpoint::Parameter(position) => self
                .parameter_live_base
                .checked_add(
                    u32::try_from(position)
                        .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                )
                .ok_or(SolveAvailabilityError::IdentityExhausted)?,
        };
        self.live_value_term(polarity, row)
    }
    pub(super) fn admit_candidate_fact(
        &mut self,
        recipe: &CandidateConstraintRecipe,
    ) -> Result<(), SolveAvailabilityError> {
        let (lower, upper) = match recipe.relation {
            CandidateRelation::Group { child, result } => (
                self.candidate_endpoint(child, Polarity::Positive)?,
                self.candidate_endpoint(CandidateEndpoint::Component(result), Polarity::Negative)?,
            ),
            CandidateRelation::Apply {
                callee,
                argument,
                result,
            } => {
                let callee = self.candidate_endpoint(callee, Polarity::Positive)?;
                let argument = self.candidate_endpoint(argument, Polarity::Positive)?;
                let result = self
                    .candidate_endpoint(CandidateEndpoint::Component(result), Polarity::Negative)?;
                let bottom = self.batch.collected_leaf_term(Leaf::EffectBottomPositive);
                let empty = self.batch.collected_leaf_term(Leaf::EmptyEffectNegative);
                let demand = self.negative_function_term(argument, bottom, empty, result)?;
                (callee, demand)
            }
        };
        let id = ConstraintOccurrenceId::new(recipe.occurrence.clone(), 0);
        let occurrence = ConstraintOccurrence {
            cause: CauseId::for_occurrence(id.clone()),
            id,
            lower,
            upper,
        };
        self.store
            .admit_and_record_provenance(&occurrence)
            .map_err(SolveAvailabilityError::from)?;
        let key = CanonicalValuePairKey {
            lower: self.value_endpoint(lower, Polarity::Positive),
            upper: self.value_endpoint(upper, Polarity::Negative),
        };
        let transitions = self.constrain_live_value(key, &occurrence.id, &occurrence.cause)?;
        #[cfg(test)]
        {
            self.initial_value_pair_probes += 1;
            self.summary_false_to_true_transitions += transitions;
        }
        #[cfg(not(test))]
        let _ = transitions;
        self.sample_f4_resources(ResourceBoundary::InitialAdmission)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn module(text: &str) -> Arc<HirModule> {
        let source: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            source.clone(),
            Arc::new(yu_syntax::scan_header(source)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        Arc::new(
            yu_hir::shadow::lower_module_with_shadow_applications(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                    "candidate-internal",
                    "candidate.yu",
                ))),
                &parsed,
                yu_hir::SemanticImports::empty(),
            )
            .unwrap(),
        )
    }
    #[test]
    fn candidate_direct_chain_keeps_direction_and_bounded_shared_diagonal() {
        fn positive(value: &F5cPositive<'_>, qs: &mut HashSet<u32>) -> bool {
            match value {
                F5cPositive::Quantified(q) => {
                    qs.insert(*q);
                    false
                }
                F5cPositive::Int => true,
                F5cPositive::Union(parts) => parts
                    .iter()
                    .fold(false, |int, part| positive(part, qs) || int),
                _ => false,
            }
        }
        fn negative(value: &F5cNegative<'_>, qs: &mut HashSet<u32>) {
            match value {
                F5cNegative::Quantified(q) => {
                    qs.insert(*q);
                }
                F5cNegative::Intersection(parts) => {
                    for part in parts.iter() {
                        negative(part, qs);
                    }
                }
                _ => {}
            }
        }
        for case in [0, 1, 2] {
            let meter = DraftHeapMeter::default();
            let batch = ConstraintBatch::collect_mode(module("my f = 1"), true).unwrap();
            let mut session = InferenceSession::new(batch);
            let definition = session.batch.definitions[0].definition.clone();
            let root = session.batch.definitions[0].root.clone();
            let root_row = session.live_components
                [session.batch.root_component_positions[&root].component]
                .ordinal;
            let a = session.fresh_value_at_level(1).unwrap();
            let b = session.fresh_value_at_level(1).unwrap();
            let c = session.fresh_value_at_level(1).unwrap();
            for (lower, upper) in [(a, b), (b, c)] {
                session.bounds[lower as usize].direct_upper_rows.push(upper);
                session.bounds[upper as usize].direct_lower_rows.push(lower);
            }
            let (argument, result) = match case {
                0 => (a, c),
                1 => (c, a),
                _ => (a, a),
            };
            if case == 2 {
                session.bounds[a as usize]
                    .exact_non_variable_lowers
                    .push(ValueEndpointKey::IntPositive);
            }
            let argument = session
                .live_value_term(Polarity::Negative, argument)
                .unwrap();
            let result = session.live_value_term(Polarity::Positive, result).unwrap();
            let function = session
                .positive_function_term(
                    argument,
                    session.batch.collected_leaf_term(Leaf::EmptyEffectNegative),
                    session
                        .batch
                        .collected_leaf_term(Leaf::EffectBottomPositive),
                    result,
                )
                .unwrap();
            session.bounds[root_row as usize]
                .exact_non_variable_lowers
                .push(ValueEndpointKey::PositiveFunction(function));
            let draft = session.generalization_draft(&meter, &definition).unwrap();
            let F5cPositive::Function {
                argument, result, ..
            } = &draft.predicate
            else {
                panic!("Function")
            };
            if case == 1 {
                assert_eq!(**argument, F5cNegative::Top);
                assert_eq!(**result, F5cPositive::Bottom);
            } else {
                let mut argument_qs = HashSet::new();
                let mut result_qs = HashSet::new();
                negative(argument, &mut argument_qs);
                let has_int = positive(result, &mut result_qs);
                assert!(argument_qs.intersection(&result_qs).next().is_some());
                if case == 2 {
                    assert!(has_int);
                }
            }
        }
    }
    #[test]
    fn candidate_boxed_and_flat_sessions_preserve_whole_scheme_parity() {
        for text in [
            "my id x = x; my wrap y = id y; pub out = wrap 1",
            "my id x = x; my wrap y = id (id y); pub out = wrap 1",
            "my self x = x x",
        ] {
            let hir = module(text);
            let mut results = Vec::new();
            for flat in [false, true] {
                let batch = ConstraintBatch::collect_mode(hir.clone(), true).unwrap();
                let mut session = InferenceSession::new(batch);
                session.flat_candidate_enabled = flat;
                results.push(session.run());
            }
            match (&results[0], &results[1]) {
                (Ok(boxed), Ok(flat)) => {
                    for item in hir.items() {
                        let HirItem::Binding(binding) = item else {
                            continue;
                        };
                        assert!(
                            boxed
                                .shadow_closed_schemes()
                                .for_root(binding.definition_root())
                                .unwrap()
                                .endpoints()
                                .alpha_eq(
                                    flat.shadow_closed_schemes()
                                        .for_root(binding.definition_root())
                                        .unwrap()
                                        .endpoints()
                                )
                        );
                    }
                }
                (Err(left), Err(right)) => assert_eq!(left, right),
                _ => panic!("boxed/flat availability differs"),
            }
        }
    }
    #[test]
    fn candidate_self_application_keeps_active_admission_invariant() {
        let hir = module("my self x = x x");
        let batch = ConstraintBatch::collect_mode(hir, true).unwrap();
        let mut session = InferenceSession::new(batch);
        session.admit_all_collected_facts().unwrap();
        let root = session.batch.definitions[0].root.clone();
        let row = session.live_components[session.batch.root_component_positions[&root].component]
            .ordinal;
        let meter = DraftHeapMeter::default();
        let mut generalizer = F5cGeneralizer::with_source_meter(&session, &meter);
        generalizer.assert_admission_invariant = true;
        // This checks safe generalizer execution, never source acceptance or R meaning.
        let _ = generalizer.build_component(row);
    }
    #[test]
    fn parameter_references_reuse_actual_startup_row() {
        let hir = module("my repeated f = f f");
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let ResolvedExpr::Lambda {
            parameter, body, ..
        } = binding.value()
        else {
            panic!("lambda")
        };
        let candidate = CandidateValueObservation::solve(hir.clone()).unwrap();
        let capture = candidate.solved.shadow_fresh_capture.as_ref().unwrap();
        let rows = capture.parameter_rows.as_ref().unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(&rows[0].0, parameter);
        let row = rows[0].1;
        assert!(
            capture.routes.is_empty(),
            "formals have no definition-use substitution"
        );
        let cause =
            CauseId::for_occurrence(ConstraintOccurrenceId::new(body.occurrence().clone(), 0));
        let fact_id = candidate
            .solved
            .store
            .provenance()
            .iter()
            .find(|edge| edge.cause() == &cause)
            .expect("Apply provenance")
            .fact();
        let fact = candidate
            .solved
            .store
            .facts()
            .iter()
            .find(|fact| fact.id() == fact_id)
            .expect("Apply demand");
        let TermView::LiveVariable(callee) =
            candidate.solved.store.term_view(fact.lower()).unwrap()
        else {
            panic!("direct formal callee")
        };
        assert_eq!(callee.ordinal(), row);
        let TermView::NegativeFunction { argument, .. } =
            candidate.solved.store.term_view(fact.upper()).unwrap()
        else {
            panic!("demand")
        };
        let TermView::LiveVariable(argument) = candidate.solved.store.term_view(argument).unwrap()
        else {
            panic!("direct formal argument")
        };
        assert_eq!(argument.ordinal(), row);
        let batch = ConstraintBatch::collect_mode(hir.clone(), true).unwrap();
        assert_eq!(batch.parameter_recipes.len(), 1);
        assert!(batch.definition_uses.is_empty());
        assert!(batch.components.iter().all(|component| !matches!(component,
            ComponentId::Occurrence { occurrence, kind: ComponentKind::Value } if occurrence != body.occurrence())));
    }
    #[test]
    fn preflight_depth_counts_both_apply_children() {
        let hir = module("my f x = x 1");
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let ResolvedExpr::Lambda { body, .. } = binding.value() else {
            panic!("lambda")
        };
        for callee_side in [true, false] {
            for (groups, accepted) in [(125, true), (126, false)] {
                let mut tree = binding.value().clone();
                let ResolvedExpr::Lambda { body: apply, .. } = &mut tree else {
                    unreachable!()
                };
                let ResolvedExpr::Apply {
                    callee, argument, ..
                } = apply.as_mut()
                else {
                    panic!("apply")
                };
                let child = if callee_side { callee } else { argument };
                for _ in 0..groups {
                    **child = ResolvedExpr::Group {
                        occurrence: body.occurrence().clone(),
                        range: body.range().clone(),
                        inner: Box::new(child.as_ref().clone()),
                    };
                }
                assert_eq!(
                    preflight_expression(&tree, &mut Vec::new(), &mut HashSet::new()).is_ok(),
                    accepted
                );
            }
        }
    }
    #[test]
    fn preflight_depth_counts_root_lambda_and_every_group_child() {
        let hir = module("my f x = 1");
        let HirItem::Binding(binding) = &hir.items()[0] else {
            panic!("binding")
        };
        let ResolvedExpr::Lambda {
            occurrence,
            parameter,
            body,
            range,
        } = binding.value()
        else {
            panic!("lambda")
        };
        for (groups, accepted) in [(126, true), (127, false)] {
            let mut inner = body.as_ref().clone();
            for _ in 0..groups {
                inner = ResolvedExpr::Group {
                    occurrence: body.occurrence().clone(),
                    range: range.clone(),
                    inner: Box::new(inner),
                };
            }
            let tree = ResolvedExpr::Lambda {
                occurrence: occurrence.clone(),
                parameter: parameter.clone(),
                body: Box::new(inner),
                range: range.clone(),
            };
            let result = preflight_expression(&tree, &mut Vec::new(), &mut HashSet::new());
            assert_eq!(result.is_ok(), accepted);
        }
    }
}
