# R55 Rust implementation handoff

Assignment: `EFFECT-PERMISSION-SOURCE-INTERNAL-CONTEXT/20261031-R55`
Contract SHA-256: `6583202e628a854dfeade9834788de76f2fad8422335383dd54884e9c35646bc`
Admission SHA-256: `cc5e0a773bdd2b60f43eb3dcc79b32485f86b430043f3f71df30247d37348f59`
Requested model/effort: Luna/high. Observed model/effort: UNKNOWN.

## Bounded source/Internal contribution

Added a private feature-gated `SourceInternalProjection` query to `ReceivingResidualExperiment`. It first obtains the R54 borrowed projection, so the fragment remains anchored to the same experiment, Assembly, batch, session, whole-publication record, and live State. Every vector inventory is captured in original owner order with dense indices and fallible reservation. Capture returns `None` on missing or ambiguous owners and does not participate in inference or forwarding.

The fragment retains complete candidate formal registrations, lexical names, source Apply calls, parameter recipes, LambdaRecipes, formal-entry permissions, lambda-argument origins, DefinitionUses, routed uses, source schedules, source-owner map, component/term pairs, and admitted semantic facts. It retains each exact registration-owner HIR Arc and LocalSource, checks the Lambda expression at the original `registration.lambda` index and formal identity, checks exact source-owner lookup, and checks the source-owner map’s unique occurrence mapping. Each complete formal-entry permission is joined to its unique FormalEntry schedule action and to the exact source Lambda parameter annotation, including owner, source position, effect-row position, and concrete members.

Round-trip validation also rejects duplicate registration coordinates for the same `(owner, lambda index)`, and re-queries every captured LocalSource through the same batch HIR lookup, requiring pointer identity for both the HIR Arc and LocalSource.

The original relay Catch expression is recovered from the retained relay LocalSource by exact occurrence. The projection retains its original scrutinee expression and complete ordered arm slice, and checks the edge-scrutinee occurrence and the selected resolved declaration/source key/identity/family against Assembly. It does not infer an entire Catch table from selected-arm evidence.

The R45 internal incidence is tied back to its unique DefinitionUse, Internal routed-use record and admitted fact, lambda origin, and both admitted facts in the complete inventory. The exact positive Function term is re-read from the owning store; its argument-effect child must be the expected negative live Effect variable at the retained permission’s entry ordinal.

The R45 registered root is represented separately from `FormalRegistrationInput.native_root`. `InternalRegisteredRootJoin` retains the original registration index, unique LambdaRecipe index, `root_component`, parameter native root, and registered root term. Capture requires the recipe occurrence to match the retained lambda origin and the recipe root component to equal the exact Internal use’s target-root component; it derives the registered root only via `batch.component_term_at(root_component)`. Both the lambda fact upper and Internal fact lower must equal that root. No global inequality premise is imposed between the two root terms.

No ordinary forwarding behavior was changed. The observer remains private and best-effort; no public API, new global identifier, producer history, or semantic authorization was added.

## Source/native boundary and unresolved premises

The admitted contract says the R54 owner does not retain a HIR Arc. Frozen source inspection found that `ConstraintBatch` retains `hir: Arc<HirModule>` and `hirs`, exposes `hir_for_source_root`, and the R54 owner retains the batch. This existing exact owner path supplies source HIR without a producer/constructor edit or lease expansion; the parent was notified of the contract/source discrepancy. If the R54 owner’s runtime-retained HIR behavior differs from those frozen source APIs, projection fails closed.

This produces only the bounded R39/R45/R49 source/Internal fragment. It does not construct a complete R49 Context or R50 interpretation, prove faithful extraction of every Rust read into all source-level primitive tables, or establish the parent theorem, runtime, soundness, principality, termination, complete hygiene, or production readiness. R39/R45/R49 Lean/model construction and reader equations remain under the proof lane’s review. No Rust execution or type-check is claimed.

## Reused evidence, checks, and frozen outputs

The full admitted R54 and R39/R45/R47–R54 source/model cone was rehashed before author edits and matched its R55 pins. The earlier R54 owner-preserving projection and exact Internal-incidence source method were reused; the disputed HIR premise was not repaired by adding retention or changing a producer.

- `git diff --check`: PASS.
- `python3 tools/agent_sprint.py check`: STATIC CHECK PASS (not execution or independent review).
- No build, tests, Cargo, Lake, formatter, project execution, cache, scratch, or new environment was used.
- `crates/yu-solver/src/candidate_receiver.rs`: SHA-256 `befdb77ea88becca357f83914f61ade7e09bf93bd33e5adb2ee017d0e51a76aa`.
- `crates/yu-solver/src/candidate_effect.rs`: SHA-256 `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909`.

`candidate_effect.rs` was already dirty at its admitted R55 baseline. Its existing contents were preserved; this assignment added only a crate-subtree visibility bridge for `FormalEntryPermission` and a complete borrowed owner iterator. The primary must preserve the pre-existing delta and stage only intended R55 hunks.

Only the two leased Rust files and this leased handoff were written by this worker. No scratch or disposable path was created. No Git mutation was performed. Requested model/effort was Luna/high; runtime observation remains UNKNOWN.

STOP: scoped source review and the two permitted checks are complete. No further writes will be made in this assignment.

## R55 source revision archive: rejected receiver snapshot

The preceding handoff revision described the exact rejected receiver snapshot SHA-256 `befdb77ea88becca357f83914f61ade7e09bf93bd33e5adb2ee017d0e51a76aa`. The following is its exact diff against immutable accepted R54 checkpoint `7e3e48703469250d37ecf2119e7d96fcc0107433` (whose receiver file hash is `cd914826f79cec065af2dbba7bb79d0ddc7681080e12a0e974738186118e769f`). This archived revision had two lexical construction defects corrected below; its prior source and handoff content are retained here for review.

```diff
diff --git a/crates/yu-solver/src/candidate_receiver.rs b/crates/yu-solver/src/candidate_receiver.rs
index a68a90e5a..b1b650414 100644
--- a/crates/yu-solver/src/candidate_receiver.rs
+++ b/crates/yu-solver/src/candidate_receiver.rs
@@ -410,6 +410,60 @@ pub(super) struct OwnedResidualProjection<'a> {
     pub(super) emissions: Vec<(usize, &'a candidate_context::BoundEmission)>,
 }
 #[cfg(feature = "shadow-apply-candidate")]
+#[allow(dead_code, reason = "bounded source/Internal fragment owned by R55")]
+pub(super) struct OwnedLocalSource<'a> {
+    pub(super) registration_owner: &'a SourceRootId,
+    pub(super) hir: &'a Arc<HirModule>,
+    pub(super) source: &'a LocalSource,
+}
+#[cfg(feature = "shadow-apply-candidate")]
+#[allow(dead_code, reason = "bounded source/Internal fragment owned by R55")]
+pub(super) struct SourceInternalProjection<'a> {
+    pub(super) native: OwnedResidualProjection<'a>,
+    pub(super) local_sources: Vec<OwnedLocalSource<'a>>,
+    pub(super) catch_source: &'a LocalSource,
+    pub(super) catch_expression: &'a yu_hir::shadow::LocalSourceExpr,
+    pub(super) catch_scrutinee: &'a yu_hir::shadow::LocalSourceExpr,
+    pub(super) catch_arms: &'a [yu_hir::shadow::LocalSourceCatchArm],
+    pub(super) resolved_operations: Vec<(usize, &'a SourceNodeKey, &'a Arc<SourceOperationDeclaration>)>,
+    pub(super) formal_registrations: Vec<(usize, &'a candidate_call::FormalRegistrationInput)>,
+    pub(super) formal_names: Vec<(usize, &'a candidate_call::FormalNameInput)>,
+    pub(super) calls: Vec<(usize, &'a candidate_call::ApplySourceInput)>,
+    pub(super) parameter_recipes: Vec<(usize, &'a HirParameterId)>,
+    pub(super) lambda_recipes: Vec<(usize, &'a LambdaRecipe)>,
+    /// The registration's parameter native root and the R45 registered root
+    /// are different coordinates. The former addresses the formal parameter;
+    /// the latter is joined through the unique LambdaRecipe and its root
+    /// component for this exact Internal use.
+    pub(super) internal_root_join: InternalRegisteredRootJoin,
+    pub(super) internal_function_witness: InternalFunctionWitness,
+    pub(super) formal_entry_permissions: Vec<(usize, &'a candidate_effect::FormalEntryPermission)>,
+    pub(super) lambda_origins: Vec<(usize, &'a candidate_context::LambdaArgumentEffectOrigin)>,
+    pub(super) definition_uses: Vec<(usize, &'a DefinitionUse)>,
+    pub(super) routed_uses: Vec<(usize, &'a RoutedUseProvenance)>,
+    pub(super) schedules: Vec<(&'a DefinitionRootId, &'a Vec<candidate_source::Action>)>,
+    pub(super) source_owners: Vec<(&'a HirOccurrenceId, &'a SourceRootId)>,
+    pub(super) component_terms: Vec<(usize, &'a ComponentId, Term)>,
+    pub(super) semantic_facts: Vec<(usize, &'a SemanticFact)>,
+    pub(super) internal_incidence: InternalFormalPermissionIncidence<'a>,
+}
+#[cfg(feature = "shadow-apply-candidate")]
+#[allow(dead_code, reason = "keeps parameter-root and Internal registered-root coordinates distinct")]
+pub(super) struct InternalRegisteredRootJoin {
+    pub(super) registration: usize,
+    pub(super) recipe_index: usize,
+    pub(super) root_component: usize,
+    pub(super) parameter_native_root: Option<Term>,
+    pub(super) registered_root: Term,
+}
+#[cfg(feature = "shadow-apply-candidate")]
+#[allow(dead_code, reason = "retains the actual positive Function child used by the Internal incidence")]
+pub(super) struct InternalFunctionWitness {
+    pub(super) function: Term,
+    pub(super) argument_effect: Term,
+    pub(super) entry_effect: u32,
+}
+#[cfg(feature = "shadow-apply-candidate")]
 fn collect_owned_borrowed_inventory<'a, T>(
     items: impl Iterator<Item = (usize, &'a T)>,
 ) -> Option<Vec<(usize, &'a T)>> {
@@ -493,6 +547,11 @@ impl ReceivingResidualExperiment {
         OwnedResidualProjection::capture(self)
     }
     #[cfg(feature = "shadow-apply-candidate")]
+    #[allow(dead_code, reason = "private R55 source/Internal owner projection")]
+    pub(super) fn source_internal_projection(&self) -> Option<SourceInternalProjection<'_>> {
+        SourceInternalProjection::capture(self)
+    }
+    #[cfg(feature = "shadow-apply-candidate")]
     #[allow(dead_code, reason = "selected by the private proof correspondence query")]
     pub(super) fn native_publication_call(
         &self,
@@ -1654,6 +1713,50 @@ impl<'a> OwnedResidualProjection<'a> {
         let mut source_drains = Vec::new();
         source_drains.try_reserve_exact(origins.len()).ok()?;
         source_drains.extend(origins.iter().map(|(_, origin)| origin.source_drain_receipt.as_ref()));
+        let internal_incidence = owner.internal_formal_permission_incidence()?;
+        let registration_index = internal_incidence.permission.registration;
+        let registration = batch.candidate_calls.formals.get(registration_index)?;
+        let mut matching_recipes = batch.lambda_recipes.iter().enumerate().filter(|(_, recipe)| {
+            recipe.formal_registration == Some(registration_index)
+        });
+        let (recipe_index, recipe) = matching_recipes.next()?;
+        if matching_recipes.next().is_some()
+            || recipe.occurrence != internal_incidence.lambda_origin.lambda
+            || recipe.root_component != internal_incidence.use_record.target_root_component
+            || recipe.root_component >= batch.component_terms.len()
+        {
+            return None;
+        }
+        let registered_root = batch.component_term_at(recipe.root_component);
+        if registered_root != batch.component_terms[recipe.root_component]
+            || internal_incidence.lambda_fact.upper() != registered_root
+            || internal_incidence.internal_fact.lower() != registered_root
+        {
+            return None;
+        }
+        let TermView::PositiveFunction { argument_effect, .. } =
+            owner.session.store.term_view(internal_incidence.lambda_origin.function).ok()?
+        else { return None; };
+        let TermView::LiveVariable(argument_view) = owner.session.store.term_view(argument_effect).ok()?
+        else { return None; };
+        if argument_view.kind() != ComponentKind::Effect
+            || argument_view.polarity() != Polarity::Negative
+            || argument_view.ordinal() != internal_incidence.permission.entry_effect
+        {
+            return None;
+        }
+        let internal_root_join = InternalRegisteredRootJoin {
+            registration: registration_index,
+            recipe_index,
+            root_component: recipe.root_component,
+            parameter_native_root: registration.native_root,
+            registered_root,
+        };
+        let internal_function_witness = InternalFunctionWitness {
+            function: internal_incidence.lambda_origin.function,
+            argument_effect,
+            entry_effect: argument_view.ordinal(),
+        };
         let projection = Self {
             owner,
             schema: &owner.schema,
@@ -1973,6 +2076,345 @@ impl<'a> OwnedResidualProjection<'a> {
     }
 }
 
+#[cfg(feature = "shadow-apply-candidate")]
+impl<'a> SourceInternalProjection<'a> {
+    fn capture(owner: &'a ReceivingResidualExperiment) -> Option<Self> {
+        let native = owner.native_owned_projection()?;
+        let batch = native.batch;
+        let effect_state = &owner.session.candidate_graph.as_ref()?.intrusion.effect_algebra;
+        let registrations = collect_owned_borrowed_inventory(batch.candidate_calls.formals.iter().enumerate())?;
+        let mut local_sources = Vec::new();
+        local_sources.try_reserve_exact(registrations.len()).ok()?;
+        for (_, registration) in &registrations {
+            if local_sources.iter().any(|source: &OwnedLocalSource<'_>| source.registration_owner == &registration.owner) {
+                continue;
+            }
+            let hir = batch.hir_for_source_root(&registration.owner)?;
+            let source = hir.local_source_for(&registration.owner).ok().flatten()?;
+            if source.source_root() != &registration.owner { return None; }
+            local_sources.try_reserve(1).ok()?;
+            local_sources.push(OwnedLocalSource {
+                registration_owner: &registration.owner,
+                hir,
+                source,
+            });
+        }
+        let relay_source = local_sources.iter().find_map(|source| {
+            matches!(source.registration_owner, SourceRootId::Definition(root) if root == &owner.schema.relay)
+                .then_some(source.source)
+        })?;
+        let mut catch_expressions = relay_source.expressions().iter().filter(|expression| {
+            expression.occurrence == owner.schema.catch
+        });
+        let catch_expression = catch_expressions.next()?;
+        if catch_expressions.next().is_some() { return None; }
+        let Form::Catch { scrutinee, arms } = &catch_expression.form else { return None; };
+        let catch_scrutinee = relay_source.expression(scrutinee)?;
+        if catch_scrutinee.occurrence != owner.schema.edge_scrutinee || arms.len() != 2 {
+            return None;
+        }
+        let mut resolved_operations = Vec::new();
+        resolved_operations.try_reserve_exact(arms.len()).ok()?;
+        for (arm_index, arm) in arms.iter().enumerate() {
+            if let Pattern::Operation {
+                resolution: yu_hir::shadow::SourceOperationResolution::Resolved(declaration),
+                operation_source,
+                ..
+            } = &arm.pattern
+            {
+                resolved_operations.try_reserve(1).ok()?;
+                resolved_operations.push((arm_index, operation_source, declaration));
+            }
+        }
+        let (selected_index, selected_source, selected_declaration) = resolved_operations.iter()
+            .find(|record| record.0 == owner.schema.selected_arm.arm_ordinal as usize)
+            .copied()?;
+        if selected_index != owner.schema.selected_arm.arm_ordinal as usize
+            || selected_source != &owner.schema.selected_arm.operation_source
+            || !Arc::ptr_eq(selected_declaration, &owner.schema.selected_arm.operation)
+            || selected_declaration.id != owner.schema.selected_arm.operation_identity
+            || selected_declaration.id.family != owner.schema.provider_identity.family
+        {
+            return None;
+        }
+
+        let graph = owner.session.candidate_graph.as_ref()?;
+        let context = &graph.intrusion.effect_algebra.context;
+        let projection = Self {
+            native,
+            local_sources,
+            catch_source: relay_source,
+            catch_expression,
+            catch_scrutinee,
+            catch_arms: arms,
+            resolved_operations,
+            formal_registrations: registrations,
+            formal_names: collect_owned_borrowed_inventory(batch.candidate_calls.names.iter().enumerate())?,
+            calls: collect_owned_borrowed_inventory(batch.candidate_calls.calls.iter().enumerate())?,
+            parameter_recipes: collect_owned_borrowed_inventory(batch.parameter_recipes.iter().enumerate())?,
+            lambda_recipes: collect_owned_borrowed_inventory(batch.lambda_recipes.iter().enumerate())?,
+            internal_root_join,
+            internal_function_witness,
+            formal_entry_permissions: collect_owned_borrowed_inventory(
+                graph.intrusion.effect_algebra.owned_projection_entry_permissions(),
+            )?,
+            lambda_origins: collect_owned_borrowed_inventory(context.lambda_argument_effects.iter().enumerate())?,
+            definition_uses: collect_owned_borrowed_inventory(batch.definition_uses().iter().enumerate())?,
+            routed_uses: collect_owned_borrowed_inventory(owner.session.routed_uses.iter().enumerate())?,
+            schedules: {
+                let mut inventory = Vec::new();
+                inventory.try_reserve_exact(batch.candidate_source.schedules.len()).ok()?;
+                inventory.extend(batch.candidate_source.schedules.iter());
+                inventory
+            },
+            source_owners: {
+                let mut inventory = Vec::new();
+                inventory.try_reserve_exact(batch.candidate_source.source_owners.len()).ok()?;
+                inventory.extend(batch.candidate_source.source_owners.iter());
+                inventory
+            },
+            component_terms: {
+                if batch.components.len() != batch.component_terms.len() { return None; }
+                let mut inventory = Vec::new();
+                inventory.try_reserve_exact(batch.components.len()).ok()?;
+                inventory.extend(batch.components.iter().zip(&batch.component_terms).enumerate()
+                    .map(|(index, (component, term))| (index, component, *term)));
+                inventory
+            },
+            semantic_facts: collect_owned_borrowed_inventory(owner.session.store.facts().iter().enumerate())?,
+            internal_incidence,
+        };
+        projection.verify_owner_round_trips().then_some(projection)
+    }
+
+    fn verify_owner_round_trips(&self) -> bool {
+        let owner = self.native.owner;
+        let batch = self.native.batch;
+        let Some(graph) = owner.session.candidate_graph.as_ref() else { return false; };
+        let effect_state = &graph.intrusion.effect_algebra;
+        if !borrowed_inventory_matches(batch.candidate_calls.formals.iter().enumerate(), &self.formal_registrations)
+            || !borrowed_inventory_matches(batch.candidate_calls.names.iter().enumerate(), &self.formal_names)
+            || !borrowed_inventory_matches(batch.candidate_calls.calls.iter().enumerate(), &self.calls)
+            || !borrowed_inventory_matches(batch.parameter_recipes.iter().enumerate(), &self.parameter_recipes)
+            || !borrowed_inventory_matches(batch.lambda_recipes.iter().enumerate(), &self.lambda_recipes)
+            || !borrowed_inventory_matches(effect_state.owned_projection_entry_permissions(), &self.formal_entry_permissions)
+            || !borrowed_inventory_matches(effect_state.context.lambda_argument_effects.iter().enumerate(), &self.lambda_origins)
+            || !borrowed_inventory_matches(batch.definition_uses().iter().enumerate(), &self.definition_uses)
+            || !borrowed_inventory_matches(owner.session.routed_uses.iter().enumerate(), &self.routed_uses)
+            || !borrowed_inventory_matches(owner.session.store.facts().iter().enumerate(), &self.semantic_facts)
+        {
+            return false;
+        }
+        for (index, (_, registration)) in self.formal_registrations.iter().enumerate() {
+            if self.formal_registrations[..index].iter().any(|(_, prior)| {
+                prior.owner == registration.owner && prior.lambda == registration.lambda
+            }) {
+                return false;
+            }
+        }
+        for source in &self.local_sources {
+            let Some(hir) = batch.hir_for_source_root(source.registration_owner) else { return false; };
+            if !Arc::ptr_eq(hir, source.hir)
+                || !hir.local_source_for(source.registration_owner).is_ok_and(|retained| {
+                    retained.is_some_and(|retained| std::ptr::eq(retained, source.source))
+                })
+            {
+                return false;
+            }
+        }
+        if self.schedules.len() != batch.candidate_source.schedules.len()
+            || self.schedules.iter().any(|(root, actions)| {
+                !batch.candidate_source.schedules.get(*root).is_some_and(|current| std::ptr::eq(*actions, current))
+            })
+            || self.source_owners.len() != batch.candidate_source.source_owners.len()
+            || self.source_owners.iter().any(|(occurrence, root)| {
+                !batch.candidate_source.source_owners.get(*occurrence).is_some_and(|current| std::ptr::eq(*root, current))
+            })
+            || self.component_terms.len() != batch.components.len()
+            || self.component_terms.iter().enumerate().any(|(index, (owner_index, component, term))| {
+                *owner_index != index || !std::ptr::eq(*component, &batch.components[index])
+                    || *term != batch.component_terms[index]
+            })
+        {
+            return false;
+        }
+        for (registration_index, registration) in &self.formal_registrations {
+            let Some(local_source) = self.local_sources.iter().find(|source| source.registration_owner == &registration.owner) else { return false; };
+            let root_is_owned = match &registration.owner {
+                SourceRootId::Definition(root) => local_source.hir.owns_definition_root(root),
+                SourceRootId::Expression(root) => local_source.hir.owns_expression_root(root),
+            };
+            if !root_is_owned {
+                return false;
+            }
+            let Some(expression) = local_source.source.expressions().get(registration.lambda) else { return false; };
+            if !local_source.hir.owns_occurrence(&expression.occurrence)
+                || !matches!(&expression.form, Form::Lambda { parameter, .. }
+                    if parameter.id == registration.parameter && parameter.id.source_root() == &registration.owner)
+                || batch.parameter_recipes.get(registration.recipe_position) != Some(&registration.parameter)
+            {
+                return false;
+            }
+            if self.source_owners.iter().filter(|(occurrence, root)| {
+                **occurrence == expression.occurrence && **root == registration.owner
+            }).count() != 1
+                || self.source_owners.iter().find(|(occurrence, _)| **occurrence == expression.occurrence)
+                    .is_none_or(|(_, root)| **root != registration.owner)
+            {
+                return false;
+            }
+            let _ = registration_index;
+        }
+        for (permission_index, permission) in &self.formal_entry_permissions {
+            if *permission_index >= self.formal_entry_permissions.len() { return false; }
+            let Some((registration_index, registration)) = self.formal_registrations.get(permission.registration) else { return false; };
+            if *registration_index != permission.registration
+                || registration.role != candidate_call::FormalRole::Computation
+                || registration.recipe_position != permission.parameter
+                || registration.parameter != permission.formal
+                || registration.owner != permission.source_owner
+                || registration.scope != permission.scope
+                || registration.entry_effect != Some(permission.entry_effect)
+            {
+                return false;
+            }
+            let SourceRootId::Definition(root) = &permission.source_owner else { return false; };
+            let Some(actions) = batch.candidate_source.schedules.get(root) else { return false; };
+            let mut matching_actions = actions.iter().filter_map(|action| match action {
+                candidate_source::Action::FormalEntry { registration: index, annotation, occurrence, scope }
+                    if *index == permission.registration => Some((annotation, occurrence, scope)),
+                _ => None,
+            });
+            let Some((annotation, occurrence, scope)) = matching_actions.next() else { return false; };
+            if matching_actions.next().is_some()
+                || annotation.owner != permission.source_owner
+                || annotation.position != permission.annotation_position
+                || occurrence != &permission.occurrence
+                || scope != &permission.scope
+                || annotation.ty.effects.as_ref().is_none_or(|row| {
+                    row.position != permission.source_row || row.concrete != permission.concrete
+                })
+            {
+                return false;
+            }
+            let Some(local_source) = self.local_sources.iter().find(|source| {
+                source.registration_owner == &registration.owner
+            }) else { return false; };
+            let Some(expression) = local_source.source.expressions().get(registration.lambda) else { return false; };
+            let Form::Lambda { parameter, .. } = &expression.form else { return false; };
+            if parameter.id != permission.formal {
+                return false;
+            }
+            let Some(source_annotation) = parameter.annotation.as_ref() else { return false; };
+            if source_annotation.owner != permission.source_owner
+                || source_annotation.position != permission.annotation_position
+                || source_annotation.ty.effects.as_ref().is_none_or(|row| {
+                    row.position != permission.source_row || row.concrete != permission.concrete
+                })
+            {
+                return false;
+            }
+        }
+        let Form::Catch { scrutinee, arms } = &self.catch_expression.form else { return false; };
+        if !self.local_sources.iter().any(|source| {
+            std::ptr::eq(self.catch_source, source.source)
+                && matches!(source.registration_owner, SourceRootId::Definition(root) if root == &owner.schema.relay)
+        })
+            || self.catch_expression.occurrence != owner.schema.catch
+            || !std::ptr::eq(self.catch_scrutinee, match self.catch_source.expression(scrutinee) { Some(value) => value, None => return false })
+            || self.catch_scrutinee.occurrence != owner.schema.edge_scrutinee
+            || !std::ptr::eq(self.catch_arms, arms.as_slice())
+            || arms.len() != 2
+        {
+            return false;
+        }
+        let Some((selected_index, arm)) = arms.iter().enumerate().find(|(index, _)| *index == owner.schema.selected_arm.arm_ordinal as usize) else { return false; };
+        if selected_index != owner.schema.selected_arm.arm_ordinal as usize { return false; }
+        let Pattern::Operation {
+            resolution: yu_hir::shadow::SourceOperationResolution::Resolved(declaration),
+            operation_source,
+            ..
+        } = &arm.pattern else { return false; };
+        if operation_source != &owner.schema.selected_arm.operation_source
+            || !Arc::ptr_eq(declaration, &owner.schema.selected_arm.operation)
+            || declaration.id != owner.schema.selected_arm.operation_identity
+        {
+            return false;
+        }
+        let Some(definition_index) = self.definition_uses.iter().position(|(_, use_record)| {
+            std::ptr::eq(*use_record, self.internal_incidence.use_record)
+        }) else { return false; };
+        let Some((owner_index, use_record)) = self.definition_uses.get(definition_index) else { return false; };
+        if *owner_index != definition_index || !std::ptr::eq(*use_record, self.internal_incidence.use_record)
+            || self.internal_incidence.target_owner != &owner.schema.relay
+            || self.internal_incidence.receiving_owner != &owner.schema.answer
+            || !self.routed_uses.iter().any(|(index, route)| {
+                std::ptr::eq(*route, self.internal_incidence.internal_route)
+                    && route.kind == RoutedUseKind::Internal
+                    && route.fact == Some(self.internal_incidence.internal_fact.id())
+                    && *index < self.routed_uses.len()
+            })
+        {
+            return false;
+        }
+        let Ok(TermView::PositiveFunction { argument_effect, .. }) =
+            owner.session.store.term_view(self.internal_function_witness.function)
+        else { return false; };
+        let Ok(TermView::LiveVariable(argument_view)) =
+            owner.session.store.term_view(argument_effect)
+        else { return false; };
+        if argument_effect != self.internal_function_witness.argument_effect
+            || argument_view.kind() != ComponentKind::Effect
+            || argument_view.polarity() != Polarity::Negative
+            || argument_view.ordinal() != self.internal_function_witness.entry_effect
+            || argument_view.ordinal() != permission.entry_effect
+            || self.internal_function_witness.function != self.internal_incidence.lambda_origin.function
+        {
+            return false;
+        }
+        let permission = &self.internal_incidence.permission;
+        let Some((root_registration_index, root_registration)) =
+            self.formal_registrations.get(self.internal_root_join.registration)
+        else { return false; };
+        let Some((recipe_index, recipe)) = self.lambda_recipes.get(self.internal_root_join.recipe_index)
+        else { return false; };
+        if *root_registration_index != self.internal_root_join.registration
+            || *recipe_index != self.internal_root_join.recipe_index
+            || recipe.formal_registration != Some(self.internal_root_join.registration)
+            || recipe.root_component != self.internal_root_join.root_component
+            || self.internal_root_join.parameter_native_root != root_registration.native_root
+            || self.internal_root_join.registered_root != batch.component_term_at(recipe.root_component)
+            || self.internal_incidence.lambda_fact.upper() != self.internal_root_join.registered_root
+            || self.internal_incidence.internal_fact.lower() != self.internal_root_join.registered_root
+        {
+            return false;
+        }
+        let mut permissions = self.formal_entry_permissions.iter().filter(|(_, retained)| {
+            retained.registration == permission.registration
+        });
+        let Some((_, retained_permission)) = permissions.next() else { return false; };
+        if permissions.next().is_some()
+            || retained_permission.formal != *permission.formal
+            || retained_permission.occurrence != *permission.occurrence
+            || retained_permission.source_owner != *permission.source_owner
+            || retained_permission.scope != *permission.scope
+            || retained_permission.annotation_position != *permission.annotation_position
+            || retained_permission.source_row != *permission.source_row
+            || retained_permission.entry_effect != permission.entry_effect
+            || retained_permission.concrete.as_slice().as_ptr() != permission.concrete.as_ptr()
+        {
+            return false;
+        }
+        if !self.lambda_origins.iter().any(|(_, origin)| std::ptr::eq(*origin, self.internal_incidence.lambda_origin))
+            || !self.semantic_facts.iter().any(|(_, fact)| std::ptr::eq(*fact, self.internal_incidence.lambda_fact))
+            || !self.semantic_facts.iter().any(|(_, fact)| std::ptr::eq(*fact, self.internal_incidence.internal_fact))
+        {
+            return false;
+        }
+        true
+    }
+}
+
 #[cfg(feature = "shadow-apply-candidate")]
 fn raw_source_effect_endpoint(
     session: &InferenceSession,
```

## Dispatcher-approved B1/B2 lexical repair

The rejected receiver snapshot above had hash `befdb77ea88becca357f83914f61ade7e09bf93bd33e5adb2ee017d0e51a76aa`. B1 moved the complete Internal incidence, unique LambdaRecipe/root-component join, positive Function child lookup, and retained witness construction from `OwnedResidualProjection::capture` into `SourceInternalProjection::capture`, after that constructor binds its exact borrowed R54 projection, batch, registration-owner LocalSources, and relay LocalSource. B2 binds `let permission = &internal_incidence.permission` before reading its `entry_effect`. The selections, checks, and resulting fields were preserved; no semantic or producer change was made.

`candidate_effect.rs` and Lean files remain frozen. No build, tests, or type-check was run. The two permitted checks were run after the repair: `git diff --check` PASS; `python3 tools/agent_sprint.py check` STATIC CHECK PASS (not execution or independent review).

Repaired receiver SHA-256: `7b0698e6ac26ec1ba983d83006ef14d14a600b37e805ec0455120f24e2f6f224`.
