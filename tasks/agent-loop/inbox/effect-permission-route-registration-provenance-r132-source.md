# R132 source handoff — route/registration provenance

Sprint-ID / contract revision and SHA-256:
- `effect-permission-route-registration-provenance-20261102-r132`, revision 1
- Contract SHA-256: `61b03747aa51f1659162b365b6a3d238c64fbe62df98d36f091ada09847f3e26`

Assignment-ID / handoff revision: `r132-route-provenance-source`, revision 1.

Parent gate / original theorem and scope:
- Original Simple-sub A/B, source/native correspondence, effect hygiene, and production gates remain OPEN.
- This is a provisional source adapter candidate. It does not change handler/solver semantics or claim a theorem.

Baseline / direct dependency hashes:
- Committed HEAD: `559021b7157b5f1fea949d08228aad13171d07b8` (`yulang3`, equal to `origin/yulang3` at admission).
- All source reads below used `git show HEAD:<path>`. Each source hash matched the frozen R132 contract pin.
- `crates/yu-solver/src/lib.rs` `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`
- `crates/yu-solver/src/candidate_effect.rs` `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`
- `crates/yu-solver/src/candidate_receiver.rs` `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`
- `crates/yu-solver/src/candidate_scheme.rs` `064df99d57aa657f6f1491f16b249403d2ee155b36142e15ca67cafb070df070`
- `crates/yu-solver/src/candidate_source.rs` `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `crates/yu-solver/src/candidate_context.rs` `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
- `crates/yu-solver/src/candidate_call.rs` `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
- `crates/yu-solver/src/candidate_intrusion.rs` `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
- `crates/yu-solver/src/term.rs` `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`

Role / worker / model:
- Role requested: `implementer`, Luna/high. Worker: `/root/r132_route_provenance`.
- Observed model and effort: UNKNOWN to this worker; no runtime model metadata was provided. No substitution is claimed.
- No descendants.

Exact leased path:
- `tasks/agent-loop/inbox/effect-permission-route-registration-provenance-r132-source.md` only.
- No source file was written or materialized. The candidate below was formed and hashed in memory from the pinned committed blob.

## End-to-end source/native correspondence found

The committed path already retains each transition up to the route adapter:

1. `candidate_source.rs:1104–1118` allocates one `FormalRegistrationInput` per Lambda, with owner, source expression index, parameter ID, recipe position, role, and initially empty `entry_effect`. `candidate_source.rs:1324–1334` emits `Action::FormalEntry` for an effect-annotated computation formal. The owner consumer `candidate_effect.rs:1763–1819` validates the exact source Lambda/formal and retains the permission by registration, raw entry row, source annotation occurrence, and concrete atom list.
2. `candidate_source.rs:2092–2111` creates `LambdaRecipe` with that same formal-registration index and Lambda occurrence. `lib.rs:2300–2327` assigns the native root and allocates the computation entry row. `lib.rs:11328–11780` constructs a positive Function whose argument effect is the negative live entry row, checks that polarity/kind, and calls the context retainer with registration, Lambda occurrence, Function term, and raw entry ordinal.
3. `candidate_context.rs:1644–1652` retains `LambdaArgumentEffectOrigin`; its `checkpoint`/`rollback` at `2157`/`2224` includes the origin-vector length. The origin keeps raw `entry_effect` distinct from later canonicalization.
4. `candidate_scheme.rs:2870–2899` captures only origins whose positive Function endpoint is in the graph, reads Function child 1 structurally, and checks that the graph row key is the live algebra representative of the origin's raw entry row. `LambdaArgumentEffectCapture` retains registration, Lambda occurrence, Function node, child index/node, and graph-row index.
5. `candidate_scheme.rs:4442–4468` maps that exact graph-row index through the same `FreshUse.rows` vector and retains `LambdaArgumentEffectFreshUse`. The resulting distinctions are: raw row `e`; captured representative `rep(e)`; graph row index `j`; fresh image `FreshUse.rows[j]`; registration `r`; Lambda occurrence `λ`; and the retained incidence. The existing `extract_native_lambda_argument_effect_incidence` at `451–493` validates child 1, graph-row index, mapped image, and the native positive Function in the completed module route.
6. `candidate_effect.rs:397–442` already has a permission binder that selects a unique permission by registration and checks registration/formal/owner/scope/occurrence/raw entry, then returns a borrowed permission view tied to a DefinitionUse and context-use ID. The patch joins that binder to an explicitly selected module route and incidence through one `InferenceSession`.

The selected annotation policy remains the policy in `notes/design/2026-10-10-annotation-effect-hygiene-integration.md`: a contravariant concrete annotation grants local subtraction permission; the actual handler performs subtraction. This candidate returns permission evidence only; it does not consume it.

## Candidate patch

Only `candidate_scheme.rs` changes. The existing capture/FreshUse constructors already retain the required raw-to-representative-to-image path, so duplicating their state or adding another row identity would be unnecessary and unsafe.

Old file: 503,780 bytes, SHA-256 `064df99d57aa657f6f1491f16b249403d2ee155b36142e15ca67cafb070df070`.
Candidate file: 508,232 bytes, SHA-256 `3ccd2cd3de1107ca66a52ebcedfc5276c0311bc49edc71ff8a966fd9025ad143`.

```diff
--- a/crates/yu-solver/src/candidate_scheme.rs
+++ b/crates/yu-solver/src/candidate_scheme.rs
@@ -490,6 +490,94 @@
         definition_use: route.use_id.clone(),
         context_use: route.retained.context_use,
     })
+}
+
+/// Bind one selected module FreshUse incidence to its source permission using
+/// only state owned by the same inference session. Numeric row equality never
+/// selects a registration, Lambda, route, or incidence.
+#[allow(dead_code, reason = "session-owned permission binding remains a provisional source adapter")]
+pub(super) fn bind_native_formal_entry_permission_use<'a>(
+    session: &'a InferenceSession,
+    route_index: usize,
+    incidence_index: usize,
+) -> Option<(NativeLambdaArgumentEffectIncidence, candidate_effect::FormalEntryPermissionUse<'a>)> {
+    let graph_state = session.candidate_graph.as_ref()?;
+    let route = graph_state.routes.get(route_index)?;
+    let native = extract_native_lambda_argument_effect_incidence(route, incidence_index, &session.store)?;
+    let registered = session.batch.candidate_calls.formals.get(native.registration)?;
+    if registered.role != candidate_call::FormalRole::Computation
+        || registered.owner != SourceRootId::Definition(route.provider.clone())
+    {
+        return None;
+    }
+
+    // Rejoin the retained context origin by its registration label and exact
+    // Lambda occurrence. The raw entry row is kept separate from its captured
+    // representative and FreshUse image; the original Function Term may differ
+    // from the fresh Function Term retained by this route.
+    let mut origins = graph_state.intrusion.effect_algebra.context.lambda_argument_effects.iter()
+        .filter(|origin| origin.registration == native.registration);
+    let origin = origins.next()?;
+    if origins.next().is_some() || origin.lambda != native.lambda {
+        return None;
+    }
+    let EffectEndpointKey::EffectRow(raw_entry) = origin.entry else { return None; };
+    if registered.entry_effect != Some(raw_entry) {
+        return None;
+    }
+    let TermView::PositiveFunction { argument_effect: raw_argument_effect, .. } =
+        session.store.term_view(origin.function).ok()? else { return None; };
+    let TermView::LiveVariable(raw_view) = session.store.term_view(raw_argument_effect).ok()? else { return None; };
+    if raw_view.kind() != ComponentKind::Effect
+        || raw_view.polarity() != Polarity::Negative
+        || raw_view.ordinal() != raw_entry
+    {
+        return None;
+    }
+
+    // The registration's source recipe and source Lambda must be unique in
+    // this session; matching row numbers or a shared Function node is not enough.
+    let mut recipes = session.batch.lambda_recipes.iter()
+        .filter(|recipe| recipe.formal_registration == Some(native.registration));
+    let recipe = recipes.next()?;
+    if recipes.next().is_some() || recipe.occurrence != native.lambda {
+        return None;
+    }
+    let source = session.batch.hir_for_source_root(&registered.owner)?
+        .local_source_for(&registered.owner).ok().flatten()?;
+    let expression = source.expressions().get(registered.lambda)?;
+    if expression.occurrence != native.lambda
+        || !matches!(&expression.form,
+            yu_hir::shadow::LocalSourceForm::Lambda { parameter, .. }
+                if parameter.id == registered.parameter)
+    {
+        return None;
+    }
+
+    // Capture stores the canonical representative at graph_row; FreshUse maps
+    // that position through route.rows. The native fresh Function must carry
+    // the mapped effect variable, which can differ from the raw row and rep.
+    let representative = graph_state.intrusion.rep(RowKey::Effect(raw_entry));
+    if route.graph.rows.get(native.argument_effect_graph_row).map(|row| row.key)
+        != Some(representative)
+    {
+        return None;
+    }
+    let RowKey::Effect(mapped_entry) = native.mapped_argument_effect_row else { return None; };
+    let TermView::PositiveFunction { argument_effect: mapped_argument_effect, .. } =
+        session.store.term_view(native.function).ok()? else { return None; };
+    let TermView::LiveVariable(mapped_view) = session.store.term_view(mapped_argument_effect).ok()? else { return None; };
+    if mapped_view.kind() != ComponentKind::Effect
+        || mapped_view.polarity() != Polarity::Negative
+        || mapped_view.ordinal() != mapped_entry
+    {
+        return None;
+    }
+    let permission = graph_state.intrusion.effect_algebra.bind_formal_entry_permission_use(
+        native.registration, registered, &native.lambda, raw_entry,
+        native.mapped_argument_effect_row, &route.use_id, native.context_use,
+    )?;
+    Some((native, permission))
 }
```

## Cases and failure behavior

- **Two Lambdas in one session:** `registration` chooses the source record and `lambda` is checked against both the unique `LambdaRecipe` and actual source expression/parameter. If registrations, recipes, or permission records are duplicated or disagree, the adapter returns `None`. Function or row equality cannot choose which Lambda owns the permission.
- **Canonicalized unequal raw rows:** `raw_entry` remains the `FormalRegistrationInput`/context-origin row. The graph row must equal `rep(raw_entry)` at the recorded graph position. Its FreshUse image is read from the same route's row map and checked against the fresh Function's negative argument-effect variable. `raw_entry`, representative, graph position, and fresh image are not conflated.
- **Repeated FreshUse:** each call selects a module route by index; each retained route has its own FreshUse map and context-use identity. Thus two uses of the same captured graph can have equal source coordinates and still return distinct route/use bindings. Reusing an old incidence index under another route is rejected unless that selected route actually retains the structurally corresponding incidence and row map.
- **Capture failure:** capture constructs a local graph and publishes a completed module route only after construction succeeds. A failed capture cannot be selected as a route. The session context checkpoint is owned by the enclosing route transaction; transaction rollback restores the context checkpoint and removes additions after it.
- **FreshUse failure/interruption:** freshening builds `FreshUse` maps before route publication. Failed route transactions roll back the context journal and truncate newly published module routes to the journal length. A paused/incomplete source or route has no completed `state.routes[route_index]` to select; it must not be passed to this adapter. On a stale/cross-Lambda mismatch every guard returns `None`, never a permission inferred from numeric equality.
- **Rollback boundary:** `candidate_context::Checkpoint` records `lambda_argument_effects.len()` and `rollback` truncates to that length. `RouteMutationJournal` snapshots candidate intrusion/context state and candidate route count in `lib.rs:9336–9560`; failure calls `rollback_route_transaction` at `9711ff`, which restores intrusion and truncates routes. A committed source origin remains valid across later failed captures because it predates that capture transaction; it is not mistaken for a partially published route.

## First missing source equation / remaining owners

This candidate establishes a session-owned evidence join, not the behavior that consumes the permission. The first missing source/native equation after this join is at the actual handler consumer:

`residual_effect = subtract(actual_same_provider_inflow, handled_concrete_atoms ∩ bound_permission.concrete)`

with symbolic variables and independent same-row contributions retained, and with the handler operation tied to this same registration/provider/call. The current adapter has no Catch/provider consumer; no equation proves that an actual Catch performs that subtraction. `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` keeps that consumer gate OPEN. Source/native correspondence, original A/B quantifiers, soundness, hygiene, and production remain OPEN.

## Checks, limits, prior evidence, and next step

- Exact source-pin SHA checks: all nine pins matched at intake.
- Candidate diff: one additive function in `candidate_scheme.rs`; byte count/SHA above were computed from the committed blob plus patch entirely in memory.
- No compiler, Cargo, build, test, formatter, Lean, checker, storage/environment probe, scratch file, source materialization, or Git operation ran.
- Prior implementation reused: committed Lambda registration, context retention/checkpoint, capture incidence, FreshUse map, native incidence extractor, and candidate_effect permission binder. No dirty observer/test changes were read or imported. The exact R132 baseline excludes quarantined runtime files, which were not read.
- No source-owner mismatch or missing raw/canonical/FreshUse equation was found in the pinned path. No claim is made that the additive Rust function compiles; it was not compiled.
- New repository path: this handoff only. Disposable scratch paths: none.
- Budget: within the 600-second author cap; no build/probe budget consumed. Exact worker active seconds unavailable from the runtime interface. Astra/descendant usage: zero.
- Frozen handoff ID/revision/hash: `r132-route-provenance-source` / 1 / SHA-256 to be computed by Luna at freeze.
- Requested model/effort: implementer Luna/high. Observed model/effort: UNKNOWN.
- Worker state / STOP: STOPPED after this frozen handoff; no descendants or outstanding writes.
- Next related in-envelope step: fresh independent `compiler_referee` review of this exact patch and the two-Lambda/canonicalized-row/repeated-FreshUse/failure cases. Only after review, Luna may decide whether a coherent source integration is authorized; this packet itself authorizes no source write or push.

---

# Revision 2 — lifetime and canonical-representative repair

Assignment-ID / handoff revision: `r132-route-provenance-source`, revision 2.
Revision 1 is preserved verbatim above as the prior frozen receipt, SHA-256 `509bdcc749b43033c588a33396c5d031a9ac6a8f023a27fbd0e50fa3979a46a1`. This revision supersedes only its candidate patch and contract-hash claim; the evidence scope and OPEN parent gates remain unchanged.

Correct R132 contract SHA-256: `ba88ab578b9a851181eb603283fc80823eab7f4ed0b878df2103e1faa6a2519e`.

## Revalidated source pins

Recomputed from the frozen baseline commit `559021b7157b5f1fea949d08228aad13171d07b8` using `git show <commit>:<path> | sha256sum`. All nine matched the R132 contract:

- `crates/yu-solver/src/lib.rs` — `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f`
- `crates/yu-solver/src/candidate_effect.rs` — `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`
- `crates/yu-solver/src/candidate_receiver.rs` — `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`
- `crates/yu-solver/src/candidate_scheme.rs` — `064df99d57aa657f6f1491f16b249403d2ee155b36142e15ca67cafb070df070`
- `crates/yu-solver/src/candidate_source.rs` — `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a`
- `crates/yu-solver/src/candidate_context.rs` — `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
- `crates/yu-solver/src/candidate_call.rs` — `fdc39e01fa3665b4dc14e167973de63b275eb0280b831e340b6cdcee5ed0fc3f`
- `crates/yu-solver/src/candidate_intrusion.rs` — `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
- `crates/yu-solver/src/term.rs` — `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1`

## Repairs and source-grounded rationale

1. **Permission-binder lifetime.** The old candidate passed `&native.lambda`, then moved `native` into the return tuple. The binder's signature ties `occurrence: &'a HirOccurrenceId` to its returned view lifetime, although the current implementation stores a reference to `permission.occurrence`. Revision 2 instead passes `&origin.lambda`, where `origin` is borrowed from `session.candidate_graph...context.lambda_argument_effects`; this borrow is owned by the same `session` for `'a`. The registration and exact occurrence are checked against `native.lambda` before the borrow is passed. The permission record itself remains the authoritative occurrence source. This removes the local-value borrow from the returned lifetime graph without weakening identity checks.
2. **Representative changes after capture.** At capture, `candidate_scheme.rs:2892–2896` compares the graph row key with the current representative of the raw entry. Later row equality can change representatives, so comparing the stored capture key directly with a newly computed `rep(raw_entry)` can reject a still-equal row. Revision 2 obtains the selected incidence's exact graph-row key and compares `intrusion.rep(captured_row)` with `intrusion.rep(Effect(raw_entry))` at lookup time. Capture's structural registration/Lambda/function-child/graph-row incidence still selects the evidence; representative equality is only a consistency check after that selection and is never used to discover a registration or permission. FreshUse still maps that selected graph-row position through this route's own `rows` vector.

These repairs are justified by the frozen source: `candidate_effect.rs:397–442` requires the occurrence reference to have the returned borrow lifetime; `candidate_intrusion.rs:165–175` defines `rep` through the current value/effect representative maps; and `candidate_scheme.rs:2870–2899` records the structural incidence and capture-time representative. No additional source premise is imported.

## Revision 2 complete candidate patch

The base file remains 503,780 bytes, SHA-256 `064df99d57aa657f6f1491f16b249403d2ee155b36142e15ca67cafb070df070`. The complete candidate target is 508,255 bytes, SHA-256 `9cb8349a6ad43ddde8f54ae04ea464a61781b626b25917e928d45d49de3b2012`; formed and hashed in memory from that pinned blob.

```diff
--- a/crates/yu-solver/src/candidate_scheme.rs
+++ b/crates/yu-solver/src/candidate_scheme.rs
@@ -490,6 +490,93 @@
         definition_use: route.use_id.clone(),
         context_use: route.retained.context_use,
     })
+}
+
+/// Bind one selected module FreshUse incidence to its source permission using
+/// only state owned by the same inference session. Numeric row equality never
+/// selects a registration, Lambda, route, or incidence.
+#[allow(dead_code, reason = "session-owned permission binding remains a provisional source adapter")]
+pub(super) fn bind_native_formal_entry_permission_use<'a>(
+    session: &'a InferenceSession,
+    route_index: usize,
+    incidence_index: usize,
+) -> Option<(NativeLambdaArgumentEffectIncidence, candidate_effect::FormalEntryPermissionUse<'a>)> {
+    let graph_state = session.candidate_graph.as_ref()?;
+    let route = graph_state.routes.get(route_index)?;
+    let native = extract_native_lambda_argument_effect_incidence(route, incidence_index, &session.store)?;
+    let registered = session.batch.candidate_calls.formals.get(native.registration)?;
+    if registered.role != candidate_call::FormalRole::Computation
+        || registered.owner != SourceRootId::Definition(route.provider.clone())
+    {
+        return None;
+    }
+
+    // Rejoin the retained context origin by its registration label and exact
+    // Lambda occurrence. The raw entry row is kept separate from its captured
+    // representative and FreshUse image; the original Function Term may differ
+    // from the fresh Function Term retained by this route.
+    let mut origins = graph_state.intrusion.effect_algebra.context.lambda_argument_effects.iter()
+        .filter(|origin| origin.registration == native.registration);
+    let origin = origins.next()?;
+    if origins.next().is_some() || origin.lambda != native.lambda {
+        return None;
+    }
+    let EffectEndpointKey::EffectRow(raw_entry) = origin.entry else { return None; };
+    if registered.entry_effect != Some(raw_entry) {
+        return None;
+    }
+    let TermView::PositiveFunction { argument_effect: raw_argument_effect, .. } =
+        session.store.term_view(origin.function).ok()? else { return None; };
+    let TermView::LiveVariable(raw_view) = session.store.term_view(raw_argument_effect).ok()? else { return None; };
+    if raw_view.kind() != ComponentKind::Effect
+        || raw_view.polarity() != Polarity::Negative
+        || raw_view.ordinal() != raw_entry
+    {
+        return None;
+    }
+
+    // The registration's source recipe and source Lambda must be unique in
+    // this session; matching row numbers or a shared Function node is not enough.
+    let mut recipes = session.batch.lambda_recipes.iter()
+        .filter(|recipe| recipe.formal_registration == Some(native.registration));
+    let recipe = recipes.next()?;
+    if recipes.next().is_some() || recipe.occurrence != native.lambda {
+        return None;
+    }
+    let source = session.batch.hir_for_source_root(&registered.owner)?
+        .local_source_for(&registered.owner).ok().flatten()?;
+    let expression = source.expressions().get(registered.lambda)?;
+    if expression.occurrence != native.lambda
+        || !matches!(&expression.form,
+            yu_hir::shadow::LocalSourceForm::Lambda { parameter, .. }
+                if parameter.id == registered.parameter)
+    {
+        return None;
+    }
+
+    // Compare current canonical representatives because later equality
+    // propagation can merge rows after this graph was captured. Incidence
+    // registration/Lambda identity, not row equality, selects the permission.
+    let captured_row = route.graph.rows.get(native.argument_effect_graph_row)?.key;
+    let representative = graph_state.intrusion.rep(RowKey::Effect(raw_entry));
+    if graph_state.intrusion.rep(captured_row) != representative {
+        return None;
+    }
+    let RowKey::Effect(mapped_entry) = native.mapped_argument_effect_row else { return None; };
+    let TermView::PositiveFunction { argument_effect: mapped_argument_effect, .. } =
+        session.store.term_view(native.function).ok()? else { return None; };
+    let TermView::LiveVariable(mapped_view) = session.store.term_view(mapped_argument_effect).ok()? else { return None; };
+    if mapped_view.kind() != ComponentKind::Effect
+        || mapped_view.polarity() != Polarity::Negative
+        || mapped_view.ordinal() != mapped_entry
+    {
+        return None;
+    }
+    let permission = graph_state.intrusion.effect_algebra.bind_formal_entry_permission_use(
+        native.registration, registered, &origin.lambda, raw_entry,
+        native.mapped_argument_effect_row, &route.use_id, native.context_use,
+    )?;
+    Some((native, permission))
 }
```

## Distinguishing scenarios

- **Two Lambdas, same session:** each incidence retains registration and Lambda occurrence. Recipe and source expression/parameter uniqueness are checked before permission lookup. A shared Function term or equal rows cannot select the other Lambda's permission.
- **Unequal raw rows later canonicalized together:** the incidence selects the captured graph row structurally; current `rep(captured_row) == rep(raw_entry)` checks the relation after union-find representative changes. The permission lookup remains keyed by registration/occurrence/raw entry. Thus canonicalization can preserve the valid binding without becoming provenance.
- **Repeated FreshUse:** route index selects one completed module route; its incidence index and `rows[graph_row]` select that route's own mapped image and `context_use`. A sibling use is not selected by matching numeric row IDs.
- **Failure/interruption/rollback:** graph capture and FreshUse mappings remain unpublished until their enclosing operation completes. A failed route transaction restores the intrusion/context checkpoint and truncates routes; the context checkpoint includes `lambda_argument_effects`. An incomplete suspended route has no selectable completed route entry. A committed origin predating a later failed capture remains valid for a later fresh use; failure does not make that origin stale. Any disagreement returns `None`.

The missing next equation remains at the actual handler consumer: the source does not establish `residual_effect = subtract(actual_same_provider_inflow, handled_concrete_atoms ∩ bound_permission.concrete)` while preserving symbolic variables and independent contributions. This candidate still has no Catch/provider consumer and changes no semantics. Original A/B, source/native correspondence, hygiene proof, and production remain OPEN.

## Revision 2 receipt

- Exact revision delta: corrected contract SHA; passed `&origin.lambda` to the long-lived permission binder; replaced capture-time representative equality with equality of current representatives for the incidence-selected graph row and raw entry row; added scenario/rationale above. Revision 1 content remains unchanged and is retained above.
- Changed candidate source path: none. Sole repository write remains this handoff file.
- Checks and resource use: no compiler, Cargo, build, tests, formatter, Lean, checker, scratch, storage/environment probe, or Git operation. Pin hashes and candidate byte count/SHA were computed from committed blobs in memory as requested. No test/probe budget consumed; no descendants/Astra.
- Requested model/effort: implementer Luna/high. Observed model/effort UNKNOWN. Exact active seconds UNKNOWN; assignment stayed within its 600-second cap.
- Worker state: STOPPED after revision 2 freeze; no descendants and no outstanding writes.
- Frozen handoff ID/revision: `r132-route-provenance-source` / 2. Entire handoff SHA-256 is reported in the worker STOP message after freeze.
- Review boundary: revision 1's independent review receipt is acknowledged by Luna. Revision 2 bytes require fresh independent review; this worker does not self-certify. No source integration or push is authorized by this assignment.
