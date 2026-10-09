//! Private, sequential source inference. Planning does not admit constraints.
use crate::*;
use crate::shadow_apply::{CandidateEndpoint, CandidateRelation};
use yu_hir::shadow::{LocalSource, LocalSourceForm, LocalSourceResolution};
use yu_hir::HirLocalId;

#[derive(Clone, Debug, Default)]
pub(super) struct Plan {
    pub active: bool,
    pub schedules: HashMap<DefinitionRootId, Vec<Action>>,
    pub loose: Vec<Action>,
    pub component_levels: HashMap<usize, u32>,
    pub parameter_levels: HashMap<usize, u32>,
    pub locals: Vec<HirLocalId>,
}
#[derive(Clone, Debug)]
pub(super) enum Action {
    FormalAnnotation { annotation: Arc<yu_hir::shadow::SourceAnnotation>, parameter: usize, occurrence: HirOccurrenceId },
    Fact(usize),
    Link { occurrence: HirOccurrenceId, endpoint: CandidateEndpoint, target: usize },
    Candidate(usize),
    Lambda(usize),
    Module(HirOccurrenceId),
    Local { slot: usize, occurrence: HirOccurrenceId, value: usize, level: u32 },
    Install { slot: usize, initializer: CandidateEndpoint, boundary: u32 },
    Operation { declaration: Arc<yu_hir::shadow::SourceOperationDeclaration>, owner: DefinitionRootId, occurrence: HirOccurrenceId, target: usize, level: u32 },
    Annotation { annotation: Arc<yu_hir::shadow::SourceAnnotation>, endpoint: CandidateEndpoint, target: usize, occurrence: HirOccurrenceId, level: u32 },
}
impl Plan {
    pub fn bytes(&self) -> usize {
        checked_usize_sum([
            checked_capacity_bytes::<(DefinitionRootId, Vec<Action>)>(self.schedules.capacity(), "source schedules"),
            checked_usize_sum(self.schedules.values().map(|actions| checked_capacity_bytes::<Action>(actions.capacity(), "source actions")), "source action storage"),
            checked_capacity_bytes::<Action>(self.loose.capacity(), "source loose actions"),
            checked_usize_sum(self.schedules.values().flat_map(|actions| actions.iter()).chain(self.loose.iter()).map(|action| {
                if let Action::Annotation { annotation, .. } | Action::FormalAnnotation { annotation, .. } = action { std::mem::size_of::<yu_hir::shadow::SourceAnnotation>() + annotation.retained_arena_bytes() } else if let Action::Operation { declaration, .. } = action { std::mem::size_of::<yu_hir::shadow::SourceOperationDeclaration>() + declaration.retained_arena_bytes() } else { 0 }
            }), "source annotation storage"),
            checked_capacity_bytes::<(usize, u32)>(self.component_levels.capacity(), "source component levels"),
            checked_capacity_bytes::<(usize, u32)>(self.parameter_levels.capacity(), "source parameter levels"),
            checked_capacity_bytes::<HirLocalId>(self.locals.capacity(), "source local identities"),
        ], "candidate source plan")
    }
}
fn unavailable() -> CollectionAvailabilityError {
    CollectionAvailabilityError::ComponentIdentityExhausted
}
fn invalid() -> CollectionAvailabilityError {
    CollectionAvailabilityError::MissingDefinitionEndpoint
}
fn push<T>(values: &mut Vec<T>, value: T) -> Result<(), CollectionAvailabilityError> {
    values.try_reserve(1).map_err(|_| unavailable())?;
    values.push(value);
    Ok(())
}
pub(super) fn preflight(source: &LocalSource) -> Result<(), shadow_apply::CandidateError> {
    if source.annotation().is_some_and(|annotation| annotation.ty.effects.is_some() || !preflight_annotation(&annotation.ty, true)) {
        return Err(shadow_apply::CandidateError::Unsupported);
    }
    for expr in source.expressions() {
        if let LocalSourceForm::Lambda { parameter, .. } = &expr.form {
            if parameter.annotation.as_ref().is_some_and(|a| a.ty.effects.is_some() || !matches!(a.ty.value, yu_hir::shadow::SourceAnnotationValue::Int | yu_hir::shadow::SourceAnnotationValue::Unit)) {
                return Err(shadow_apply::CandidateError::Unsupported);
            }
        }
        if let LocalSourceForm::Operation { resolution } = &expr.form {
            match resolution {
                yu_hir::shadow::SourceOperationResolution::Resolved(declaration) if declaration.signature.effects.is_none() && matches!(declaration.signature.value, yu_hir::shadow::SourceAnnotationValue::Function { .. }) && preflight_annotation(&declaration.signature, true) => {},
                _ => return Err(shadow_apply::CandidateError::Unsupported),
            }
        }
        if matches!(&expr.form, LocalSourceForm::Name { resolution: LocalSourceResolution::Unresolved | LocalSourceResolution::Ambiguous, .. }) {
            return Err(shadow_apply::CandidateError::Unsupported);
        }
    }
    Ok(())
}
fn preflight_annotation(ty: &yu_hir::shadow::SourceAnnotationType, positive: bool) -> bool {
    if let Some(row) = &ty.effects {
        if row.variables.len() > 1 || (!positive && !row.concrete.is_empty()) { return false; }
    }
    match &ty.value {
        yu_hir::shadow::SourceAnnotationValue::Function { argument, result } =>
            preflight_annotation(argument, !positive) && preflight_annotation(result, positive),
        _ => true,
    }
}

fn annotation_contains_unit(ty: &yu_hir::shadow::SourceAnnotationType) -> bool {
    match &ty.value {
        yu_hir::shadow::SourceAnnotationValue::Unit => true,
        yu_hir::shadow::SourceAnnotationValue::Function { argument, result } =>
            annotation_contains_unit(argument) || annotation_contains_unit(result),
        _ => false,
    }
}

pub(super) fn retain_placeholder_errors(expr: &ResolvedExpr, permitted: &mut HashSet<yu_hir::HirErrorId>) -> Result<(), shadow_apply::CandidateError> {
    // The HIR carrier owns this unsupported legacy placeholder. Its successful
    // source formation is checked separately; unrelated diagnostics stay visible.
    let mut current = expr;
    loop {
        match current {
            ResolvedExpr::Lambda { body, .. } => current = body,
            ResolvedExpr::Error { errors, .. } => {
                permitted.try_reserve(errors.len()).map_err(|_| shadow_apply::CandidateError::Unsupported)?;
                permitted.extend(errors.iter().copied());
                break;
            }
            _ => break,
        }
    }
    Ok(())
}
#[derive(Clone, Copy)]
enum Work {
    Visit(usize, u32),
    Finish(usize, u32),
    Install(usize, usize, u32),
}
impl ConstraintBatch {
    pub(super) fn emit_candidate_source<'a>(
        &mut self,
        source: &'a LocalSource,
        parent: &DefinitionOrderId,
        uses: &mut Vec<PendingDefinitionUse<'a>>,
    ) -> Result<(), CollectionAvailabilityError> {
        let mut positions = Vec::new();
        positions.try_reserve_exact(source.expressions().len()).map_err(|_| unavailable())?;
        let mut parameters = HashMap::new();
        let mut local_slots = HashMap::new();
        let mut lambdas = HashMap::new();
        let mut formal_registrations = HashMap::new();
        for (index, expr) in source.expressions().iter().enumerate() {
            positions.push(self.candidate_component(&expr.occurrence)?);
            if let LocalSourceForm::Lambda { parameter, .. } = &expr.form {
                let position = self.parameter_recipes.len();
                push(&mut self.parameter_recipes, parameter.id.clone())?;
                parameters.try_reserve(1).map_err(|_| unavailable())?;
                parameters.insert(parameter.id.clone(), position);
                let registration = self.candidate_calls.formals.len();
                push(&mut self.candidate_calls.formals, candidate_call::FormalRegistrationInput {
                    owner: source.definition_root().clone(), lambda: index,
                    parameter: parameter.id.clone(), recipe_position: position,
                })?;
                formal_registrations.try_reserve(1).map_err(|_| unavailable())?;
                formal_registrations.insert(parameter.id.clone(), registration);
            }
        }
        for binding in source.bindings() {
            let slot = self.candidate_source.locals.len();
            push(&mut self.candidate_source.locals, binding.id.clone())?;
            local_slots.try_reserve(1).map_err(|_| unavailable())?;
            local_slots.insert(binding.id.clone(), slot);
        }
        let mut endpoints = Vec::new();
        endpoints.try_reserve_exact(positions.len()).map_err(|_| unavailable())?;
        for (index, expr) in source.expressions().iter().enumerate() {
            let endpoint = match &expr.form {
                LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(parameter), .. } =>
                    CandidateEndpoint::Parameter(*parameters.get(parameter).ok_or_else(invalid)?),
                _ => CandidateEndpoint::Component(positions[index].value),
            };
            endpoints.push(endpoint);
        }
        let mut formal_names = Vec::new();
        formal_names.try_reserve_exact(positions.len()).map_err(|_| unavailable())?;
        formal_names.resize(positions.len(), None);
        for (index, expr) in source.expressions().iter().enumerate() {
            if let LocalSourceForm::Name { resolution: LocalSourceResolution::Parameter(parameter), .. } = &expr.form {
                let name = self.candidate_calls.names.len();
                push(&mut self.candidate_calls.names, candidate_call::FormalNameInput {
                    owner: source.definition_root().clone(), expression: index,
                    registration: *formal_registrations.get(parameter).ok_or_else(invalid)?,
                })?;
                formal_names[index] = Some(name);
            }
        }
        let mut actions = Vec::new();
        let mut work = Vec::new();
        push(&mut work, Work::Visit(source.body().ordinal() as usize, 1))?;
        while let Some(next) = work.pop() {
            match next {
                Work::Visit(index, level) => {
                    let expr = source.expressions().get(index).ok_or_else(invalid)?;
                    let pos = positions[index];
                    self.candidate_source.component_levels.try_reserve(2).map_err(|_| unavailable())?;
                    self.candidate_source.component_levels.insert(pos.value, level);
                    self.candidate_source.component_levels.insert(pos.effect, level);
                    push(&mut work, Work::Finish(index, level))?;
                    match &expr.form {
                        LocalSourceForm::Apply { callee, argument, .. } => {
                            push(&mut work, Work::Visit(argument.ordinal() as usize, level))?;
                            push(&mut work, Work::Visit(callee.ordinal() as usize, level))?;
                        }
                        LocalSourceForm::Group { inner } => push(&mut work, Work::Visit(inner.ordinal() as usize, level))?,
                        LocalSourceForm::Lambda { parameter, body } => {
                            let position = *parameters.get(&parameter.id).ok_or_else(invalid)?;
                            self.candidate_source.parameter_levels.try_reserve(1).map_err(|_| unavailable())?;
                            self.candidate_source.parameter_levels.insert(position, level);
                            lambdas.try_reserve(1).map_err(|_| unavailable())?;
                            lambdas.insert(index, position);
                            if let Some(annotation) = &parameter.annotation {
                                for leaf in [Leaf::IntPositive, Leaf::IntNegative] { self.term_for_leaf(leaf)?; }
                                if annotation_contains_unit(&annotation.ty) {
                                    self.term_for_leaf(Leaf::UnitPositive)?;
                                    self.term_for_leaf(Leaf::UnitNegative)?;
                                }
                                push(&mut actions, Action::FormalAnnotation { annotation: Arc::new(annotation.clone()), parameter: position, occurrence: expr.occurrence.clone() })?;
                                self.counters.emitted_facts = self.counters.emitted_facts.checked_add(2).ok_or_else(unavailable)?;
                                self.counters.generated_work_items = self.counters.generated_work_items.checked_add(2).ok_or_else(unavailable)?;
                            }
                            push(&mut work, Work::Visit(body.ordinal() as usize, level))?;
                        }
                        LocalSourceForm::Block { bindings, final_expression } => {
                            push(&mut work, Work::Visit(final_expression.ordinal() as usize, level))?;
                            let child = level.checked_add(1).ok_or_else(unavailable)?;
                            for &binding in bindings.iter().rev() {
                                let data = source.bindings().get(binding as usize).ok_or_else(invalid)?;
                                push(&mut work, Work::Install(binding as usize, index, level))?;
                                push(&mut work, Work::Visit(data.initializer.ordinal() as usize, child))?;
                            }
                        }
                        _ => {}
                    }
                }
                Work::Install(binding, block, boundary) => {
                    let binding = &source.bindings()[binding];
                    let init = positions[binding.initializer.ordinal() as usize];
                    let occurrence = &source.expressions()[binding.initializer.ordinal() as usize].occurrence;
                    // Initialization effects are one-shot computation, outside
                    // the generalized value interface and every later fresh use.
                    let start = self.occurrences.len();
                    self.emit(occurrence.clone(), 20, self.component_term_at(init.effect), self.component_term_at(positions[block].effect))?;
                    self.append_source_facts(start, &mut actions)?;
                    push(&mut actions, Action::Install { slot: local_slots[&binding.id], initializer: endpoints[binding.initializer.ordinal() as usize], boundary })?;
                }
                Work::Finish(index, level) => {
                    let expr = &source.expressions()[index];
                    let pos = positions[index];
                    let occurrence = &expr.occurrence;
                    let start = self.occurrences.len();
                    match &expr.form {
                        LocalSourceForm::Integer(_) | LocalSourceForm::Unit => {
                            let (positive_leaf, negative_leaf) = if matches!(&expr.form, LocalSourceForm::Unit) {
                                (Leaf::UnitPositive, Leaf::UnitNegative)
                            } else {
                                (Leaf::IntPositive, Leaf::IntNegative)
                            };
                            let positive = self.term_for_leaf(positive_leaf)?;
                            let negative = self.term_for_leaf(negative_leaf)?;
                            self.emit(occurrence.clone(), 0, positive, self.component_term_at(pos.value))?;
                            self.emit(occurrence.clone(), 1, self.component_term_at(pos.value), negative)?;
                            let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                            let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                            self.emit(occurrence.clone(), 2, bottom, self.component_term_at(pos.effect))?;
                            self.emit(occurrence.clone(), 3, self.component_term_at(pos.effect), empty)?;
                        }
                        LocalSourceForm::Operation { resolution: yu_hir::shadow::SourceOperationResolution::Resolved(declaration) } => {
                            self.term_for_leaf(Leaf::IntPositive)?;
                            self.term_for_leaf(Leaf::IntNegative)?;
                            if annotation_contains_unit(&declaration.signature) {
                                self.term_for_leaf(Leaf::UnitPositive)?;
                                self.term_for_leaf(Leaf::UnitNegative)?;
                            }
                            let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                            let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                            self.emit(occurrence.clone(), 1, bottom, self.component_term_at(pos.effect))?;
                            self.emit(occurrence.clone(), 2, self.component_term_at(pos.effect), empty)?;
                            self.append_source_facts(start, &mut actions)?;
                            push(&mut actions, Action::Operation { declaration: Arc::clone(declaration), owner: source.definition_root().clone(), occurrence: occurrence.clone(), target: pos.value, level })?;
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(1).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(1).ok_or_else(unavailable)?;
                            continue;
                        }
                        LocalSourceForm::Operation { .. } => return Err(invalid()),
                        LocalSourceForm::Name { resolution, .. } => {
                            let bottom = self.term_for_leaf(Leaf::EffectBottomPositive)?;
                            let empty = self.term_for_leaf(Leaf::EmptyEffectNegative)?;
                            self.emit(occurrence.clone(), 1, bottom, self.component_term_at(pos.effect))?;
                            self.emit(occurrence.clone(), 2, self.component_term_at(pos.effect), empty)?;
                            self.append_source_facts(start, &mut actions)?;
                            match resolution {
                                LocalSourceResolution::ModuleDef(target) => {
                                    push(uses, PendingDefinitionUse { parent_ordinal: parent.ordinal(), target, occurrence: occurrence.clone() })?;
                                    push(&mut actions, Action::Module(occurrence.clone()))?;
                                }
                                LocalSourceResolution::Parameter(_) => {}
                                LocalSourceResolution::Local(local) => push(&mut actions, Action::Local { slot: *local_slots.get(local).ok_or_else(invalid)?, occurrence: occurrence.clone(), value: pos.value, level })?,
                                _ => return Err(invalid()),
                            }
                            continue;
                        }
                        LocalSourceForm::Apply { callee, argument, .. } => {
                            let c = positions[callee.ordinal() as usize];
                            let a = positions[argument.ordinal() as usize];
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::Apply { callee: endpoints[callee.ordinal() as usize], callee_effect: c.effect, argument: endpoints[argument.ordinal() as usize], argument_effect: a.effect, result: pos.value, result_effect: pos.effect })?;
                            let source_input = self.candidate_calls.calls.len();
                            let checking = ConstraintOccurrenceId::new(occurrence.clone(), 0);
                            push(&mut self.candidate_calls.calls, candidate_call::ApplySourceInput {
                                owner: source.definition_root().clone(), expression: index,
                                callee: callee.clone(), argument: argument.clone(), level, recipe,
                                callee_value: endpoints[callee.ordinal() as usize], callee_effect: c.effect,
                                argument_value: endpoints[argument.ordinal() as usize], argument_effect: a.effect,
                                result: pos.value, application_effect: pos.effect,
                                cause: CauseId::for_occurrence(checking.clone()), checking,
                                formal_name: formal_names[callee.ordinal() as usize], native: None,
                            })?;
                            self.candidate_recipes[recipe].source_input = Some(source_input);
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                        LocalSourceForm::Group { inner } => {
                            formal_names[index] = formal_names[inner.ordinal() as usize];
                            let child = positions[inner.ordinal() as usize];
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::Group { child: endpoints[inner.ordinal() as usize], child_effect: child.effect, result: pos.value, result_effect: pos.effect })?;
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                        LocalSourceForm::Lambda { body, .. } => {
                            self.candidate_local_lambda_effect(occurrence, pos.effect)?;
                            self.append_source_facts(start, &mut actions)?;
                            let body_index = body.ordinal() as usize;
                            let body = positions[body_index];
                            let recipe = self.lambda_recipes.len();
                            self.lambda_recipes.try_reserve(1).map_err(|_| unavailable())?;
                            self.lambda_recipes.push(LambdaRecipe {
                                occurrence: occurrence.clone(), parameter_position: lambdas[&index],
                                root_component: pos.value, body_value_endpoint: endpoints[body_index], body_effect_component: body.effect, lambda_effect_component: pos.effect,
                                after_collected_fact: self.occurrences.len(),
                            });
                            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(3).ok_or_else(unavailable)?;
                            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(3).ok_or_else(unavailable)?;
                            push(&mut actions, Action::Lambda(recipe))?;
                            continue;
                        }
                        LocalSourceForm::Block { final_expression, .. } => {
                            formal_names[index] = formal_names[final_expression.ordinal() as usize];
                            let child = positions[final_expression.ordinal() as usize];
                            let recipe = self.candidate_recipes.len();
                            self.retain_candidate_relation(occurrence, CandidateRelation::Group {
                                child: endpoints[final_expression.ordinal() as usize], child_effect: child.effect,
                                result: pos.value, result_effect: pos.effect,
                            })?;
                            push(&mut actions, Action::Candidate(recipe))?;
                        }
                    }
                    self.append_source_facts(start, &mut actions)?;
                }
            }
        }
        let root = self.root_component_positions[source.definition_root()].component;
        let body = source.body().ordinal() as usize;
        if let Some(annotation) = source.annotation() {
            // Prepare the annotation constructor's primitives before sealing,
            // including bodies whose source expressions contain no literals.
            for leaf in [Leaf::IntPositive, Leaf::IntNegative, Leaf::EffectBottomPositive, Leaf::EmptyEffectNegative] {
                self.term_for_leaf(leaf)?;
            }
            if annotation_contains_unit(&annotation.ty) {
                self.term_for_leaf(Leaf::UnitPositive)?;
                self.term_for_leaf(Leaf::UnitNegative)?;
            }
            push(&mut actions, Action::Annotation { annotation: Arc::new(annotation.clone()), endpoint: endpoints[body], target: root, occurrence: source.expressions()[body].occurrence.clone(), level: self.candidate_source.component_levels[&positions[body].value] })?;
            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(2).ok_or_else(unavailable)?;
            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(2).ok_or_else(unavailable)?;
        } else {
            push(&mut actions, Action::Link { occurrence: source.expressions()[body].occurrence.clone(), endpoint: endpoints[body], target: root })?;
            self.counters.emitted_facts = self.counters.emitted_facts.checked_add(1).ok_or_else(unavailable)?;
            self.counters.generated_work_items = self.counters.generated_work_items.checked_add(1).ok_or_else(unavailable)?;
        }
        self.candidate_source.schedules.try_reserve(1).map_err(|_| unavailable())?;
        self.candidate_source.schedules.insert(source.definition_root().clone(), actions);
        self.candidate_source.active = true;
        Ok(())
    }
    fn append_source_facts(&self, start: usize, actions: &mut Vec<Action>) -> Result<(), CollectionAvailabilityError> {
        for index in start..self.occurrences.len() { push(actions, Action::Fact(index))?; }
        Ok(())
    }
    pub(super) fn candidate_legacy_actions(&self, start: usize, end: usize, candidate_start: usize, lambda_start: usize) -> Result<Vec<Action>, CollectionAvailabilityError> {
        let mut actions = Vec::new();
        let mut routed = HashSet::new();
        let mut candidate = candidate_start;
        let mut lambda = lambda_start;
        for index in start..=end {
            while self.candidate_recipes.get(candidate).is_some_and(|r| r.after_collected_fact == index) {
                push(&mut actions, Action::Candidate(candidate))?;
                candidate += 1;
            }
            while self.lambda_recipes.get(lambda).is_some_and(|r| r.after_collected_fact == index) {
                push(&mut actions, Action::Lambda(lambda))?;
                lambda += 1;
            }
            if index < end {
                let occurrence = self.occurrences[index].id.occurrence();
                routed.try_reserve(1).map_err(|_| unavailable())?;
                if routed.insert(occurrence.clone()) { push(&mut actions, Action::Module(occurrence.clone()))?; }
                push(&mut actions, Action::Fact(index))?;
            }
        }
        Ok(actions)
    }

}
impl InferenceSession {
    pub(super) fn initialize_candidate_source_levels(&mut self) -> Result<(), SolveAvailabilityError> {
        for (&component, &level) in &self.batch.candidate_source.component_levels {
            let endpoint = self.live_components[component];
            match endpoint.kind {
                ComponentKind::Value => self.value_levels[endpoint.ordinal as usize] = level,
                ComponentKind::Effect => self.effect_levels[endpoint.ordinal as usize] = level,
            }
        }
        for (&parameter, &level) in &self.batch.candidate_source.parameter_levels {
            self.value_levels[self.parameter_live_base as usize + parameter] = level;
        }
        Ok(())
    }
    pub(super) fn execute_candidate_loose(&mut self) -> Result<(), SolveAvailabilityError> {
        let actions = std::mem::take(&mut self.batch.candidate_source.loose);
        let result = self.execute_candidate_actions(&actions);
        self.batch.candidate_source.loose = actions;
        result
    }
    pub(super) fn execute_candidate_source_root(&mut self, root: &DefinitionRootId) -> Result<(), SolveAvailabilityError> {
        let actions = self.batch.candidate_source.schedules.remove(root).ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let result = self.execute_candidate_actions(&actions);
        self.batch.candidate_source.schedules.insert(root.clone(), actions);
        result
    }
    fn execute_candidate_actions(&mut self, actions: &[Action]) -> Result<(), SolveAvailabilityError> {
        for action in actions {
            match action {
                Action::FormalAnnotation { annotation, parameter, occurrence } => self.candidate_formal_annotation(annotation, *parameter, occurrence)?,
                Action::Fact(index) => self.admit_collected_fact(*index)?,
                Action::Link { occurrence, endpoint, target } => {
                    let lower = self.candidate_endpoint(*endpoint, Polarity::Positive)?;
                    let upper = self.batch.component_term_at(*target);
                    self.admit_candidate_value_link(occurrence, 30, lower, upper)?;
                }
                Action::Candidate(index) => { let recipe = self.batch.candidate_recipes[*index].clone(); self.admit_candidate_fact(&recipe)?; }
                Action::Lambda(index) => { let recipe = self.batch.lambda_recipes[*index].clone(); self.admit_lambda_fact(&recipe)?; }
                Action::Module(occurrence) => {
                    let id = DefinitionUseId::new(self.batch.collection_artifact.clone(), occurrence.clone());
                    if self.batch.definition_use_positions.contains_key(&id) {
                        if self.candidate_graph.as_ref().is_some_and(|state| state.intrusion.active_uses.contains(&id)) { self.route_candidate_open_use(&id)?; }
                        else { self.route_incoming(&id)?; }
                    }
                }
                Action::Local { slot, occurrence, value, level } => self.route_candidate_local(*slot, occurrence, *value, *level)?,
                Action::Install { slot, initializer, boundary } => self.install_candidate_local(*slot, *initializer, *boundary)?,
                Action::Operation { declaration, owner, occurrence, target, level } => self.candidate_operation(declaration, owner, occurrence, *target, *level)?,
                Action::Annotation { annotation, endpoint, target, occurrence, level } => self.candidate_annotation(annotation, *endpoint, *target, occurrence, *level)?,
            }
        }
        Ok(())
    }
}
