//! Bounded, private A0–A7 source-use experiment. No generic scheme is produced.
use crate::*;
use yu_hir::shadow::{
    LocalSource, LocalSourceCatchPattern as Pattern,
    LocalSourceCatchPayloadPattern as PayloadPattern, LocalSourceCatchValuePattern as ValuePattern,
    LocalSourceForm as Form, LocalSourceIndex, LocalSourceResolution as Resolution,
    SourceAnnotationValue as AnnotationValue, SourceOperationDeclaration,
    SourceOperationResolution,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ReceivingResidualOutcome {
    Suppress,
    Forward,
}

/// Owns the unpublished native graph, including the unfiltered scrutinee.
/// This is neither a module result nor an exported relay interface.
pub struct ReceivingResidualExperiment {
    session: InferenceSession,
    schema: Assembly,
    outcomes: Vec<(EffectEndpointKey, ReceivingResidualOutcome)>,
    result_row: u32,
}
impl ReceivingResidualExperiment {
    pub fn outcomes(&self) -> impl Iterator<Item = ReceivingResidualOutcome> + '_ {
        self.outcomes.iter().map(|(_, outcome)| *outcome)
    }
    pub fn catch_occurrence(&self) -> &HirOccurrenceId {
        &self.schema.catch
    }
    pub fn scrutinee_occurrence(&self) -> &HirOccurrenceId {
        &self.schema.scrutinee
    }
    /// Actual retained native lower operands, after residual admission.
    pub fn result_lower_operand_count(&self) -> usize {
        self.session.effect_bounds[self.result_row as usize]
            .exact_non_variable_lowers
            .len()
    }
    /// Families in the actual canonical native Catch-result lower graph.
    /// An unresolved row leaf or symbolic support tail makes this observation
    /// unavailable; neither the source certificate nor recorded outcomes is read.
    pub fn result_families(
        &self,
    ) -> Result<Vec<yu_hir::shadow::SourceEffectId>, SolveAvailabilityError> {
        let mut pending = vec![EffectEndpointKey::EffectRow(self.result_row)];
        let mut seen = HashSet::new();
        let mut families = Vec::new();
        let algebra = &self
            .session
            .candidate_graph
            .as_ref()
            .ok_or_else(native_unavailable)?
            .intrusion
            .effect_algebra;
        let mut work = 0usize;
        while let Some(endpoint) = pending.pop() {
            work = work.checked_add(1).ok_or_else(native_unavailable)?;
            if work > candidate_source::SCOPED_WORK_LIMIT {
                return Err(native_unavailable());
            }
            let endpoint = self.session.canonical_effect(endpoint);
            if !seen.insert(endpoint) {
                continue;
            }
            match endpoint {
                EffectEndpointKey::BottomPositive => {}
                EffectEndpointKey::EffectRow(row) => {
                    let bounds = &self.session.effect_bounds[row as usize];
                    if bounds.direct_lower_rows.is_empty()
                        && bounds.exact_non_variable_lowers.is_empty()
                        && !bounds.has_bottom_lower
                    {
                        return Err(native_unavailable());
                    }
                    pending.extend(
                        bounds
                            .direct_lower_rows
                            .iter()
                            .copied()
                            .map(EffectEndpointKey::EffectRow),
                    );
                    pending.extend(bounds.exact_non_variable_lowers.iter().copied());
                }
                EffectEndpointKey::Support(view) => {
                    let view = &algebra.views[view as usize];
                    if view.tail.is_some() {
                        return Err(native_unavailable());
                    }
                    for family in &view.allowed {
                        if !families.contains(family) {
                            families.push(family.clone());
                        }
                    }
                }
                EffectEndpointKey::AnnotationMember(view, member) => {
                    let family = algebra.views[view as usize]
                        .allowed
                        .get(member as usize)
                        .ok_or_else(native_unavailable)?;
                    if !families.contains(family) {
                        families.push(family.clone());
                    }
                }
                EffectEndpointKey::Contribution(id) => {
                    let family = &algebra.contributions[id as usize].effect;
                    if !families.contains(family) {
                        families.push(family.clone());
                    }
                }
                EffectEndpointKey::EmptyNegative | EffectEndpointKey::Allowance(_) => {
                    return Err(native_unavailable());
                }
            }
        }
        Ok(families)
    }
}

/// Immutable references to original constructors. Symbolic invocation/receipt/
/// observation binders are justified by the validated A0–A7 sequence, never by
/// ScopeState, inferred family membership, or a previous receiver activation.
struct Assembly {
    relay: DefinitionRootId,
    answer: DefinitionRootId,
    catch: HirOccurrenceId,
    scrutinee: HirOccurrenceId,
    edge_scrutinee: HirOccurrenceId,
    provider: HirOccurrenceId,
    operation: Arc<SourceOperationDeclaration>,
    selected: bool,
}
fn unavailable() -> shadow_apply::CandidateError {
    shadow_apply::CandidateError::Unsupported
}
fn native_unavailable() -> SolveAvailabilityError {
    SolveAvailabilityError::IdentityExhausted
}

fn peel<'a>(
    source: &'a LocalSource,
    mut index: &'a LocalSourceIndex,
    visited: &mut HashSet<u32>,
) -> Result<&'a yu_hir::shadow::LocalSourceExpr, shadow_apply::CandidateError> {
    loop {
        if !visited.insert(index.ordinal()) {
            return Err(unavailable());
        }
        let expression = source.expression(index).ok_or_else(unavailable)?;
        match &expression.form {
            Form::Group { inner } => index = inner,
            _ => return Ok(expression),
        }
    }
}
fn source<'a>(
    hir: &'a HirModule,
    root: &DefinitionRootId,
) -> Result<&'a LocalSource, shadow_apply::CandidateError> {
    hir.local_source(root)
        .map_err(|_| unavailable())?
        .ok_or_else(unavailable)
}
fn unit_operation(declaration: &SourceOperationDeclaration) -> bool {
    let signature = &declaration.signature;
    let AnnotationValue::Function { argument, result } = &signature.value else {
        return false;
    };
    signature.effects.is_none()
        && argument.effects.is_none()
        && result.effects.is_none()
        && matches!(argument.value, AnnotationValue::Unit)
        && matches!(result.value, AnnotationValue::Int)
}
fn assemble(
    hir: &HirModule,
    answer: &DefinitionRootId,
) -> Result<Assembly, shadow_apply::CandidateError> {
    // The complete private inventory is two definitions. No unrelated caller,
    // alias, initializer, expression item or unselected consumer is admitted.
    let bindings: Vec<_> = hir
        .items()
        .iter()
        .filter_map(|item| match item {
            HirItem::Binding(binding) => Some(binding),
            _ => None,
        })
        .collect();
    if bindings.len() != 2
        || hir
            .items()
            .iter()
            .any(|item| matches!(item, HirItem::Expression(_)))
    {
        return Err(unavailable());
    }
    let answer_binding = bindings
        .iter()
        .find(|binding| binding.definition_root() == answer)
        .ok_or_else(unavailable)?;
    let relay_binding = bindings
        .iter()
        .find(|binding| binding.definition_root() != answer)
        .ok_or_else(unavailable)?;
    let caller = source(hir, answer_binding.definition_root())?;
    let relay = source(hir, relay_binding.definition_root())?;
    if caller.expressions().len() > candidate_source::SCOPED_RECORD_LIMIT
        || relay.expressions().len() > candidate_source::SCOPED_RECORD_LIMIT
        || caller.annotation().is_some()
        || relay.annotation().is_some()
        || !caller.bindings().is_empty()
        || !relay.bindings().is_empty()
    {
        return Err(unavailable());
    }
    let mut visited = HashSet::new();
    let call = peel(caller, caller.body(), &mut visited)?;
    let Form::Apply {
        callee, argument, ..
    } = &call.form
    else {
        return Err(unavailable());
    };
    let callee = peel(caller, callee, &mut visited)?;
    if !matches!(&callee.form, Form::Name { resolution: Resolution::ModuleDef(id), .. } if id == relay_binding.id())
    {
        return Err(unavailable());
    }
    let provider_call = peel(caller, argument, &mut visited)?;
    let Form::Apply {
        callee, argument, ..
    } = &provider_call.form
    else {
        return Err(unavailable());
    };
    let provider = peel(caller, callee, &mut visited)?;
    let Form::Operation {
        resolution: SourceOperationResolution::Resolved(operation),
    } = &provider.form
    else {
        return Err(unavailable());
    };
    if !unit_operation(operation)
        || !matches!(peel(caller, argument, &mut visited)?.form, Form::Unit)
        || visited.len() != caller.expressions().len()
    {
        return Err(unavailable());
    }
    visited.clear();
    let lambda = peel(relay, relay.body(), &mut visited)?;
    let Form::Lambda { parameter, body } = &lambda.form else {
        return Err(unavailable());
    };
    let annotation = parameter.annotation.as_ref().ok_or_else(unavailable)?;
    let row = annotation.ty.effects.as_ref().ok_or_else(unavailable)?;
    if row.concrete.len() != 1
        || !row.variables.is_empty()
        || !matches!(annotation.ty.value, AnnotationValue::Int)
    {
        return Err(unavailable());
    }
    let catch = peel(relay, body, &mut visited)?;
    let Form::Catch { scrutinee, arms } = &catch.form else {
        return Err(unavailable());
    };
    let edge_scrutinee = relay
        .expression(scrutinee)
        .ok_or_else(unavailable)?
        .occurrence
        .clone();
    let scrutinee = peel(relay, scrutinee, &mut visited)?;
    if !matches!(&scrutinee.form, Form::Name { resolution: Resolution::Parameter(id), .. } if id == &parameter.id)
        || arms.len() != 2
    {
        return Err(unavailable());
    }
    let Pattern::Operation {
        resolution: SourceOperationResolution::Resolved(handled),
        payloads,
        continuation,
        ..
    } = &arms[0].pattern
    else {
        return Err(unavailable());
    };
    if !unit_operation(handled)
        || handled.id.family != row.concrete[0]
        || payloads.len() != 1
        || !matches!(payloads[0], PayloadPattern::Unit { .. })
        || !matches!(continuation, ValuePattern::Wildcard)
        || !matches!(
            peel(relay, &arms[0].body, &mut visited)?.form,
            Form::Integer(_)
        )
    {
        return Err(unavailable());
    }
    let Pattern::Value(ValuePattern::Binder(binder)) = &arms[1].pattern else {
        return Err(unavailable());
    };
    if !matches!(&peel(relay, &arms[1].body, &mut visited)?.form,
        Form::Name { resolution: Resolution::CatchBinder(id), .. } if id == &binder.id)
        || visited.len() != relay.expressions().len()
    {
        return Err(unavailable());
    }
    Ok(Assembly {
        relay: relay.definition_root().ok_or_else(unavailable)?.clone(),
        answer: answer.clone(),
        catch: catch.occurrence.clone(),
        scrutinee: scrutinee.occurrence.clone(),
        edge_scrutinee,
        provider: provider.occurrence.clone(),
        operation: Arc::clone(operation),
        selected: handled.id == operation.id,
    })
}

/// Source-shaped admission failure means this private attempt is unavailable;
/// it never rejects source from the ordinary compiler or changes its solver.
pub fn solve_receiving_residual_experiment(
    hir: Arc<HirModule>,
    answer: DefinitionRootId,
) -> Result<ReceivingResidualExperiment, shadow_apply::CandidateError> {
    let schema = assemble(&hir, &answer)?;
    let batch = ConstraintBatch::collect_candidate_mode(hir, true, true)
        .map_err(shadow_apply::CandidateError::Collection)?;
    let mut session =
        InferenceSession::try_new_candidate(batch).map_err(shadow_apply::CandidateError::Solve)?;
    let (outcomes, result_row) = session
        .execute_receiving_assembly(&schema)
        .map_err(shadow_apply::CandidateError::Solve)?;
    Ok(ReceivingResidualExperiment {
        session,
        schema,
        outcomes,
        result_row,
    })
}

impl InferenceSession {
    fn execute_receiving_assembly(
        &mut self,
        schema: &Assembly,
    ) -> Result<(Vec<(EffectEndpointKey, ReceivingResidualOutcome)>, u32), SolveAvailabilityError>
    {
        // Route the unique original module use directly. This is an assembly
        // inventory, not an SCC: do not populate intrusion active_roots/uses.
        if !self.batch.candidate_source.loose.is_empty() || self.batch.definition_uses().len() != 1
        {
            return Err(native_unavailable());
        }
        let usage = &self.batch.definition_uses()[0];
        let SourceReceiver::Definition(parent) = &usage.parent else {
            return Err(native_unavailable());
        };
        if self.batch.definitions[parent.ordinal() as usize].root != schema.answer
            || self.batch.definitions[usage.target.ordinal() as usize].root != schema.relay
        {
            return Err(native_unavailable());
        }
        let mut residual = None;
        for root in [&schema.relay, &schema.answer] {
            let actions = self
                .batch
                .candidate_source
                .schedules
                .get(root)
                .ok_or_else(native_unavailable)?
                .clone();
            for action in actions {
                if let candidate_source::Action::Fact(index) = &action {
                    let fact = &self.batch.occurrences[*index];
                    if fact.id.occurrence() == &schema.edge_scrutinee && fact.id.local_slot() == 51
                    {
                        if residual.replace(*index).is_some() {
                            return Err(native_unavailable());
                        }
                        continue;
                    }
                }
                if let candidate_source::Action::Module(occurrence) = &action {
                    let id = DefinitionUseId::new(
                        self.batch.collection_artifact.clone(),
                        occurrence.clone(),
                    );
                    self.route_internal(&id)?;
                } else {
                    self.execute_candidate_action(&action)?;
                }
            }
        }
        let fact = self.batch.occurrences[residual.ok_or_else(native_unavailable)?].clone();
        let lower = self.effect_endpoint(fact.lower, Polarity::Positive);
        let upper = self.effect_endpoint(fact.upper, Polarity::Negative);
        let EffectEndpointKey::EffectRow(result_row) = self.canonical_effect(upper) else {
            return Err(native_unavailable());
        };
        let mut pending = vec![lower];
        let mut seen = HashSet::new();
        let mut terminals = Vec::new();
        let mut work = 0usize;
        while let Some(endpoint) = pending.pop() {
            work = work.checked_add(1).ok_or_else(native_unavailable)?;
            if work > candidate_source::SCOPED_WORK_LIMIT {
                return Err(native_unavailable());
            }
            let endpoint = self.canonical_effect(endpoint);
            if !seen.insert(endpoint) {
                continue;
            }
            match endpoint {
                EffectEndpointKey::BottomPositive => {}
                EffectEndpointKey::EffectRow(row) => {
                    let bounds = &self.effect_bounds[row as usize];
                    // No terminal evidence is not evidence of an empty row.
                    if bounds.direct_lower_rows.is_empty()
                        && bounds.exact_non_variable_lowers.is_empty()
                        && !bounds.has_bottom_lower
                    {
                        return Err(native_unavailable());
                    }
                    pending.extend(
                        bounds
                            .direct_lower_rows
                            .iter()
                            .copied()
                            .map(EffectEndpointKey::EffectRow),
                    );
                    pending.extend(bounds.exact_non_variable_lowers.iter().copied());
                }
                EffectEndpointKey::Support(view) => {
                    let view_data = &self
                        .candidate_graph
                        .as_ref()
                        .unwrap()
                        .intrusion
                        .effect_algebra
                        .views[view as usize];
                    // An unresolved tail is Pending; never publish a partial
                    // certificate from the concrete members beside that tail.
                    if view_data.tail.is_some() {
                        return Err(native_unavailable());
                    }
                    for member in 0..view_data.allowed.len() {
                        pending.push(EffectEndpointKey::AnnotationMember(
                            view,
                            u32::try_from(member).map_err(|_| native_unavailable())?,
                        ));
                    }
                }
                _ => terminals.push(endpoint),
            }
        }
        if terminals.is_empty() {
            return Err(native_unavailable());
        }
        let mut outcomes = Vec::new();
        for endpoint in terminals {
            let suppress = if let EffectEndpointKey::AnnotationMember(view, member) = endpoint {
                let view = &self
                    .candidate_graph
                    .as_ref()
                    .unwrap()
                    .intrusion
                    .effect_algebra
                    .views[view as usize];
                schema.selected
                    && view.tail.is_none()
                    && view.allowed.get(member as usize) == Some(&schema.operation.id.family)
                    && matches!(&view.provenance, candidate_effect::ViewOrigin::Operation(origin)
                        if origin.occurrence == schema.provider && origin.declaration.id == schema.operation.id)
            } else {
                false
            };
            let outcome = if suppress {
                ReceivingResidualOutcome::Suppress
            } else {
                // Unknown original terminal evidence forwards unchanged. The
                // original row, arms and raw continuation are never rewritten.
                self.constrain_live_effect(endpoint, upper, &fact.id, &fact.cause)?;
                ReceivingResidualOutcome::Forward
            };
            outcomes.push((endpoint, outcome));
        }
        Ok((outcomes, result_row))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DECLARATIONS: &str =
        "act signal:\n    our ping: () -> int\nact write:\n    our ping: () -> int\n";
    const RELAY: &str =
        "my relay(thunk: [signal] int) = catch thunk { signal::ping(), _ -> 1, v -> v }\n";

    fn lower(text: &str) -> (Arc<HirModule>, DefinitionRootId) {
        let text: Arc<yu_syntax::SourceText> = Arc::from(text);
        let parsed = yu_syntax::parse_file(
            text.clone(),
            Arc::new(yu_syntax::scan_header(text)),
            Arc::new(yu_syntax::SyntaxEnvironment::empty()),
        );
        assert!(
            parsed.structural_recoveries().is_empty(),
            "{:?}",
            parsed.structural_recoveries()
        );
        let hir = Arc::new(
            yu_hir::shadow::lower_module_with_local_source(
                yu_hir::ModuleIdentity::source_root(yu_hir::FileId::new(yu_hir::FileKey::new(
                    "receiving-residual",
                    "source.yu",
                ))),
                &parsed,
                yu_hir::SemanticImports::empty(),
            )
            .unwrap(),
        );
        let answer = hir
            .items()
            .iter()
            .find_map(|item| match item {
                HirItem::Binding(binding) if binding.name().spelling() == "answer" => {
                    Some(binding.definition_root().clone())
                }
                _ => None,
            })
            .unwrap();
        (hir, answer)
    }

    fn permission_family(hir: &HirModule) -> yu_hir::shadow::SourceEffectId {
        hir.items()
            .iter()
            .find_map(|item| {
                let HirItem::Binding(binding) = item else {
                    return None;
                };
                let local = source(hir, binding.definition_root()).ok()?;
                local
                    .expressions()
                    .iter()
                    .find_map(|expression| match &expression.form {
                        Form::Lambda { parameter, .. } => parameter
                            .annotation
                            .as_ref()
                            .and_then(|annotation| annotation.ty.effects.as_ref())
                            .and_then(|row| row.concrete.first())
                            .cloned(),
                        _ => None,
                    })
            })
            .unwrap()
    }

    #[test]
    fn exact_signal_use_suppresses_actual_native_result_family() {
        let (hir, answer) = lower(&format!(
            "{DECLARATIONS}{RELAY}my answer = relay signal::ping()"
        ));
        let signal = permission_family(&hir);
        let result = solve_receiving_residual_experiment(hir, answer).unwrap();
        assert!(
            result
                .outcomes()
                .any(|outcome| outcome == ReceivingResidualOutcome::Suppress)
        );
        assert!(!result.result_families().unwrap().contains(&signal));
    }

    #[test]
    fn same_spelling_write_operation_remains_in_actual_native_result() {
        let (hir, answer) = lower(&format!(
            "{DECLARATIONS}{RELAY}my answer = relay write::ping()"
        ));
        let signal = permission_family(&hir);
        let write = source(&hir, &answer)
            .unwrap()
            .expressions()
            .iter()
            .find_map(|expression| match &expression.form {
                Form::Operation {
                    resolution: SourceOperationResolution::Resolved(operation),
                } => Some(operation.id.family.clone()),
                _ => None,
            })
            .unwrap();
        assert_ne!(signal, write);
        let result = solve_receiving_residual_experiment(hir, answer).unwrap();
        assert!(
            result
                .outcomes()
                .any(|outcome| outcome == ReceivingResidualOutcome::Forward)
        );
        let actual = result.result_families().unwrap();
        assert!(actual.contains(&write));
        assert!(!actual.contains(&signal));
    }

    #[test]
    fn grouped_scrutinee_uses_its_original_parent_edge() {
        let relay = RELAY.replace("catch thunk", "catch (thunk)");
        let (hir, answer) = lower(&format!(
            "{DECLARATIONS}{relay}my answer = relay signal::ping()"
        ));
        let signal = permission_family(&hir);
        let result = solve_receiving_residual_experiment(hir, answer).unwrap();
        assert!(
            result
                .outcomes()
                .any(|outcome| outcome == ReceivingResidualOutcome::Suppress)
        );
        assert!(!result.result_families().unwrap().contains(&signal));
    }

    #[test]
    fn private_envelope_controls_preserve_ordinary_candidate_admission() {
        let controls = [
            format!(
                "{DECLARATIONS}{RELAY}my answer = relay signal::ping()\nmy another = relay signal::ping()"
            ),
            format!("{DECLARATIONS}{RELAY}my alias = relay\nmy answer = alias signal::ping()"),
            format!(
                "{DECLARATIONS}my relay(thunk: [signal] int) = {{ my ignored = write::ping(); catch thunk {{ signal::ping(), _ -> 1, v -> v }} }}\nmy answer = relay signal::ping()"
            ),
            format!(
                "{DECLARATIONS}my relay(thunk: [signal] int) = catch thunk {{ signal::ping(), k -> k 0, v -> v }}\nmy answer = relay signal::ping()"
            ),
            format!(
                "{DECLARATIONS}my relay(thunk: [signal] int) = catch thunk {{ signal::ping(), _ -> write::ping(), v -> v }}\nmy answer = relay signal::ping()"
            ),
        ];
        for text in controls {
            let (hir, answer) = lower(&text);
            assert!(
                matches!(
                    solve_receiving_residual_experiment(hir.clone(), answer),
                    Err(shadow_apply::CandidateError::Unsupported)
                ),
                "{text}"
            );
            assert!(
                shadow_apply::CandidateInference::solve(hir).is_ok(),
                "{text}"
            );
        }
    }
}
