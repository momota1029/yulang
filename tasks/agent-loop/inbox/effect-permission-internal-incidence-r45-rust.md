# R45 Rust handoff — Internal permission incidence

Sprint / contract: `EFFECT-PERMISSION-INTERNAL-INCIDENCE/20261031-R45`, contract SHA-256 `c866a7ecc4c80df8b1345a89e6733650ddb334f35b7d3a79f4e825e134d2847a`.

Assignment / handoff: Rust implementation lane; handoff revision 1. Parent baseline requested for this resumed lane: `b5f9a785d7839d172e4c3873f51f9303574cdf1d`. Frozen R45 admission records the earlier R44 baseline `1bbb0459f8f98e0803469c6942900f047c5edebe`; Luna supplied the active R45 baseline above. Contract and admission hashes were read as pinned in the parent task.

## Outcome and source path

Outcome class: **source-native-evidence candidate; provisional, uncompiled**. Added a private borrowed `InternalFormalPermissionIncidence` query. The query is separate from `candidate_scheme::FreshRoute` and has no consumer.

The accepted source/native chain is joined from existing owner records:

1. `DefinitionUseId` is resolved through `CollectionBatch::definition_use`; the complete branded ID, cause ID, and occurrence must agree. Its `SourceReceiver::Definition` and target resolve to the exact collected receiving and target definitions.
2. The retained `RoutedUseProvenance` must be the unique record with that complete ID, must be present in the routed-use identity set, and must have kind `Internal`. Its fact must be the unique admitted source fact at the use occurrence's slot 0, with endpoints `target_root_component -> use_value_component`.
3. A unique computation `FormalRegistrationInput` owned by the target `DefinitionRootId` joins to the unique `LambdaRecipe` with that registration and target root component. The original local-source expression at the registered Lambda index must be a Lambda with the registered parameter.
4. The actual `LambdaArgumentEffectOrigin` for that registration must be unique and use that Lambda occurrence. Its constructed `function` must be a positive Function whose actual argument-effect child is a negative live effect variable with the retained entry ordinal. The unique admitted Lambda slot-2 fact must have endpoints `function -> original target root component`.
5. `State::internal_formal_entry_permission` borrows the unique retained `FormalEntryPermission` for this same registration. It checks computation role, formal/parameter recipe position, source owner and target root, scope, Lambda occurrence and entry ordinal. Its borrowed view preserves registration, formal, owner, occurrence, scope, annotation position, source row, entry port and the concrete payload's original order and duplicates.

No row, Term, spelling or provider equality selects identity. Equality is used only to validate endpoints of already-selected owner records. The certificate does not establish FreshRoute, provider arrival, `arrivalAtEntry`, Catch choice or residual subtraction.

## Files and hashes

Exact writes were confined to the admitted source lease and this handoff. `candidate_context.rs` required no change. `candidate_scheme.rs` remained read-only.

| Path | Before SHA-256 (R45 frozen input) | Frozen SHA-256 |
|---|---|---|
| `crates/yu-solver/src/candidate_receiver.rs` | `620b09011ec4dc4bfa71998e2b6fc1498b9299b3056662fdaa80b17376ba23c3` | `f5bff0d8aa7a20551fb2c5ad60b7b2b41907f471a55068a9ec1ae61ceba02911` |
| `crates/yu-solver/src/candidate_effect.rs` (dirty R43 input) | `73ad01324356672f1e45e56ea18d6f5bf0ded8628cce56e884960eb29bd5786d` | `2a86befde95581decef8fe01698961062bd22388cff2459e9611570a20b9fba3` |
| `crates/yu-solver/src/candidate_context.rs` | `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38` | `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38` |
| `crates/yu-solver/src/lib.rs` | `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce` | `7bff32f03def005688b37bcc4f81423f0a19cc2a2b8c0970f723a2973ac54499` |
| `crates/yu-solver/src/candidate_scheme.rs` (read-only) | `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631` | `bf8f5c80ce2761dc2a1235d2e02e348a91bc9e8965653db26b9abd4c8d6ca631` |

Source delta isolation: the R45 additions in `candidate_receiver.rs` are the `ReceivingResidualExperiment::internal_formal_permission_incidence` method; the R45 additions in `lib.rs` are `InternalFormalPermissionIncidence`, `InferenceSession::internal_formal_permission_incidence`, and its private `admitted_source_fact` lookup. In `candidate_effect.rs`, R45 adds `InternalFormalEntryPermission` and `State::internal_formal_entry_permission` on top of the explicitly frozen dirty R43 snapshot. That file's complete working-tree delta against committed HEAD also contains the pre-existing R43 bytes; do not treat those R43 hunks as R45 or normalize them. The exact R45 hunks are the two named additions above. No R45 allocation/retained-state changes were made.

### Isolated R45 patch inventory against `b5f9a785d`

This is the complete R45-only added source (the R43/R41 dirty context is excluded). Each block is verbatim from the frozen files; it can be applied at the named item/anchor against the corresponding R45 frozen input. `candidate_context.rs` has an empty R45 delta. `candidate_effect.rs` blocks are additive to the pinned dirty R43 snapshot, not a replacement for it.

`candidate_receiver.rs`, inside `impl ReceivingResidualExperiment` after `outcomes`:

```rust
    /// Reconstruct the private Internal-specific permission incidence from
    /// this experiment's already-admitted complete use. This does not borrow
    /// or substitute any candidate_scheme FreshRoute.
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "source evidence remains provisional and has no permission consumer")]
    pub(super) fn internal_formal_permission_incidence(
        &self,
    ) -> Option<InternalFormalPermissionIncidence<'_>> {
        let [use_record] = self.session.batch.definition_uses() else {
            return None;
        };
        let incidence = self.session
            .internal_formal_permission_incidence(use_record.id())?;
        (incidence.target_owner == &self.schema.relay
            && incidence.receiving_owner == &self.schema.answer)
            .then_some(incidence)
    }
```

`candidate_effect.rs`, after `FormalEntryPermissionUse`:

```rust
/// Internal-route counterpart to the R43 FreshRoute binding. It contains only
/// the actual source permission view; route and constructor receipts are
/// joined by the caller and never manufactured here.
#[derive(Debug)]
pub(super) struct InternalFormalEntryPermission<'a> {
    pub registration: usize,
    pub parameter: usize,
    pub formal: &'a yu_hir::HirParameterId,
    pub source_owner: &'a SourceRootId,
    pub occurrence: &'a HirOccurrenceId,
    pub scope: &'a AnnotationScope,
    pub annotation_position: &'a SourceNodeKey,
    pub source_row: &'a SourceNodeKey,
    pub entry_effect: u32,
    pub concrete: &'a [SourceEffectId],
}
```

`candidate_effect.rs`, in `impl State` after `bind_formal_entry_permission_use`:

```rust
    /// Select the actual retained permission for the same registered source
    /// Lambda. The caller independently authenticates its Internal route and
    /// constructor-to-target owner link; this lookup never infers identity
    /// from a row, native Term, or provider value.
    pub(super) fn internal_formal_entry_permission<'a>(
        &'a self,
        registration: usize,
        registered_formals: &'a [candidate_call::FormalRegistrationInput],
        occurrence: &'a HirOccurrenceId,
        target_root: &yu_hir::DefinitionRootId,
        entry_effect: u32,
    ) -> Option<InternalFormalEntryPermission<'a>> {
        let registered = registered_formals.get(registration)?;
        if registered.role != candidate_call::FormalRole::Computation
            || registered.entry_effect != Some(entry_effect)
            || !matches!(&registered.owner, SourceRootId::Definition(root) if root == target_root)
        {
            return None;
        }
        let mut matching = self.formal_entry_permissions.iter()
            .filter(|permission| permission.registration == registration);
        let permission = matching.next()?;
        if matching.next().is_some()
            || permission.parameter != registered.recipe_position
            || permission.formal != registered.parameter
            || permission.source_owner != registered.owner
            || !matches!(&permission.source_owner, SourceRootId::Definition(root) if root == target_root)
            || permission.scope != registered.scope
            || permission.occurrence != *occurrence
            || permission.entry_effect != entry_effect
            || permission.concrete.is_empty()
        {
            return None;
        }
        Some(InternalFormalEntryPermission {
            registration,
            parameter: permission.parameter,
            formal: &permission.formal,
            source_owner: &permission.source_owner,
            occurrence: &permission.occurrence,
            scope: &permission.scope,
            annotation_position: &permission.annotation_position,
            source_row: &permission.source_row,
            entry_effect: permission.entry_effect,
            concrete: &permission.concrete,
        })
    }
```

`lib.rs`, after `SemanticFact`:

```rust
/// Borrowed source/native evidence for one already-admitted Internal use.
/// This is deliberately disjoint from candidate_scheme::FreshRoute evidence.
#[derive(Debug)]
pub(super) struct InternalFormalPermissionIncidence<'a> {
    pub(super) use_record: &'a DefinitionUse,
    pub(super) target_owner: &'a DefinitionRootId,
    pub(super) receiving_owner: &'a DefinitionRootId,
    pub(super) lambda_origin: &'a candidate_context::LambdaArgumentEffectOrigin,
    pub(super) permission: candidate_effect::InternalFormalEntryPermission<'a>,
    pub(super) lambda_fact: &'a SemanticFact,
    pub(super) internal_route: &'a RoutedUseProvenance,
    pub(super) internal_fact: &'a SemanticFact,
}
```

`lib.rs`, after `route_internal_inner` (the query is feature-gated):

```rust
    #[cfg(feature = "shadow-apply-candidate")]
    #[allow(dead_code, reason = "Internal permission incidence is evidence only; no consumer is connected")]
    pub(crate) fn internal_formal_permission_incidence(
        &self,
        id: &DefinitionUseId,
    ) -> Option<InternalFormalPermissionIncidence<'_>> {
        let use_record = self.batch.definition_use(id).ok()?;
        if use_record.id != *id
            || use_record.cause.id() != id
            || use_record.occurrence != *id.occurrence()
        {
            return None;
        }
        let (receiving_owner, target_owner) = match &use_record.parent {
            SourceReceiver::Definition(parent) => {
                let parent = self.batch.definitions.get(parent.ordinal() as usize)?;
                (parent, self.batch.definitions.get(use_record.target.ordinal() as usize)?)
            }
            SourceReceiver::Expression(_) | SourceReceiver::Member(_) => return None,
        };
        if receiving_owner.definition != use_record.parent.definition()?
            || target_owner.definition != use_record.target
        {
            return None;
        }

        if !self.routed_use_positions.contains(id) {
            return None;
        }
        let mut routes = self.routed_uses.iter().filter(|route| route.use_id == *id);
        let internal_route = routes.next()?;
        if routes.next().is_some() || internal_route.kind != RoutedUseKind::Internal {
            return None;
        }
        let internal_fact_id = internal_route.fact?;
        let internal_fact = self.admitted_source_fact(&use_record.occurrence, 0)?;
        if internal_fact.id() != internal_fact_id
            || internal_fact.lower() != self.batch.component_term_at(use_record.target_root_component)
            || internal_fact.upper() != self.batch.component_term_at(use_record.use_value_component)
        {
            return None;
        }

        let effect_state = &self.candidate_graph.as_ref()?.intrusion.effect_algebra;
        let registered_formals = &self.batch.candidate_calls.formals;
        let mut registrations = effect_state.context.lambda_argument_effects.iter()
            .filter(|origin| origin.registration < registered_formals.len());
        // The registration label and source recipe/root coordinate select the
        // constructor. Do not select by its shared Function Term or row image.
        let mut selected = None;
        for origin in registrations.by_ref() {
            let registered = registered_formals.get(origin.registration)?;
            if registered.role == candidate_call::FormalRole::Computation
                && matches!(&registered.owner,
                    candidate_source::SourceRootId::Definition(root) if root == &target_owner.root)
            {
                let mut recipes = self.batch.lambda_recipes.iter()
                    .filter(|recipe| recipe.formal_registration == Some(origin.registration));
                let recipe = recipes.next()?;
                if recipes.next().is_some() {
                    return None;
                }
                if recipe.root_component != use_record.target_root_component {
                    continue;
                }
                if selected.replace((origin.registration, origin)).is_some() {
                    return None;
                }
            }
        }
        let (registration, lambda_origin) = selected?;
        let registered = registered_formals.get(registration)?;
        let mut recipes = self.batch.lambda_recipes.iter()
            .filter(|recipe| recipe.formal_registration == Some(registration));
        let recipe = recipes.next()?;
        if recipes.next().is_some()
            || recipe.occurrence != lambda_origin.lambda
            || recipe.root_component != use_record.target_root_component
            || self.batch.parameter_recipes.get(registered.recipe_position)
                != Some(&registered.parameter)
        {
            return None;
        }
        let exact_source_lambda = self.batch.hir_for_source_root(&registered.owner)
            .and_then(|hir| hir.local_source_for(&registered.owner).ok().flatten())
            .and_then(|source| source.expressions().get(registered.lambda))
            .is_some_and(|expression| expression.occurrence == lambda_origin.lambda
                && matches!(&expression.form,
                    yu_hir::shadow::LocalSourceForm::Lambda { parameter, .. }
                        if parameter.id == registered.parameter));
        if !exact_source_lambda {
            return None;
        }

        let mut origins = effect_state.context.lambda_argument_effects.iter()
            .filter(|origin| origin.registration == registration);
        let exact_origin = origins.next()?;
        if origins.next().is_some()
            || !std::ptr::eq(exact_origin, lambda_origin)
            || exact_origin.lambda != recipe.occurrence
        {
            return None;
        }
        let EffectEndpointKey::EffectRow(entry_effect) = exact_origin.entry else {
            return None;
        };
        let TermView::PositiveFunction { argument_effect, .. } =
            self.store.term_view(exact_origin.function).ok()? else { return None; };
        let TermView::LiveVariable(entry) = self.store.term_view(argument_effect).ok()? else {
            return None;
        };
        if entry.kind() != ComponentKind::Effect
            || entry.polarity() != Polarity::Negative
            || entry.ordinal() != entry_effect
        {
            return None;
        }
        let lambda_fact = self.admitted_source_fact(&exact_origin.lambda, 2)?;
        if lambda_fact.lower() != exact_origin.function
            || lambda_fact.upper() != self.batch.component_term_at(recipe.root_component)
        {
            return None;
        }
        let permission = effect_state.internal_formal_entry_permission(
            registration,
            registered_formals,
            &exact_origin.lambda,
            &target_owner.root,
            entry_effect,
        )?;
        Some(InternalFormalPermissionIncidence {
            use_record,
            target_owner: &target_owner.root,
            receiving_owner: &receiving_owner.root,
            lambda_origin: exact_origin,
            permission,
            lambda_fact,
            internal_route,
            internal_fact,
        })
    }

    fn admitted_source_fact(
        &self,
        occurrence: &HirOccurrenceId,
        slot: u8,
    ) -> Option<&SemanticFact> {
        let mut edges = self.store.provenance().iter().filter(|edge| {
            edge.cause().occurrence().occurrence() == occurrence
                && edge.cause().occurrence().local_slot() == u32::from(slot)
        });
        let edge = edges.next()?;
        if edges.next().is_some() {
            return None;
        }
        let fact = self.store.facts().get(edge.fact().index() as usize)?;
        (fact.id() == edge.fact()).then_some(fact)
    }
```

The pin/diff boundary is important: the blocks above are R45 deltas relative to the R45 frozen working inputs (for `candidate_effect.rs`, the R43-dirty frozen input); committed-HEAD diff for `candidate_effect.rs` additionally contains those pre-existing R43 bytes. Luna owns integration against `b5f9a785d` and should take only these R45 additions from that file, preserving the admitted R41/R43 baseline unchanged.

## Failure behavior, checks, resources

Absent, duplicate, foreign, or mismatched evidence returns `None`: unowned/foreign use ID; wrong receiver or target; missing or duplicate route/fact; non-Internal route; missing/ambiguous registration recipe/origin/permission; wrong source Lambda/formal/root; wrong constructor/entry child; or endpoint mismatch. The query adds no persistent state, so it adds no rollback owner or retained/scratch byte accounting. Existing constructor-origin retention remains unchanged and retains its existing owner/accounting behavior.

Checks: source-only inspection of the exact owner fields, constructor path, admission path and current diff. No build, test, Cargo, Lake, formatter or compiler command was run; these are prohibited by the contract. No tests are claimed. Runtime spent/remaining was not instrumented by this worker; exact elapsed time is **UNKNOWN** and the primary must reconcile it against the ≤1,200s assignment envelope.

Prior evidence reused: R43 R39 permission retention and R43 borrowed FreshRoute view; R44 source finding that the Internal receipt cannot furnish or be substituted for FreshRoute. The new type does not alter those semantics. No source-owner ambiguity was inferred away; all selected root/formal links are explicit retained records.

Omissions / open boundary: no compile evidence; no consumer, route construction, propagation, inference, suppression, Catch/subtraction or expected-output changes; no claim of provider arrival or parent theorem closure. Independent review and Lean characterization remain outstanding. Handoff is commit-ready only as the exact R45 hunks on the pinned dirty inputs; primary must preserve and separately account for R43 dirty bytes during integration.

Requested model/effort: Luna/high implementer lane. Observed model/effort: **UNKNOWN** in this worker runtime. Worker state: writes stopped; no descendants or generated/scratch paths created. Commit/push: pending primary review/integration.

STOP.
