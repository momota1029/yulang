# R135 source reconstruction — revision 1

Sprint / contract: `tasks/agent-loop/sprints/effect-permission-consumer-checkpoint-20261102-r135.md`, SHA-256 `749c187c326296ac6c5e124fb14f75b8218abce16fb17554cf835a6e997a1596`.
Assignment: R135 receiver candidate reconstruction; this is revision 1 of the sole leased handoff.
Parent gate: original Yulang soundness and Simple-sub A/B; this packet closes no theorem, source/native correspondence, or production gate.

## Runtime, lease and disposition

- Requested model/effort: `gpt-6-luna` / `high`. Observed model/effort: `UNKNOWN` in available runtime evidence.
- Worker identity: `/root/r135_receiver_candidate`; session and separate launch/active-work receipt: `UNKNOWN`.
- Sole write lease: this handoff. Source inputs were read only as immutable committed Git blobs and approved artifacts.
- Outcome class: `source-native-evidence` / exact in-memory candidate reconstruction; not source integration, compilation, test evidence, proof closure or production approval.
- No compiler, Cargo, tests, Lean, checker, storage/environment probe, scratch, source materialization, staging or Git mutation was used. No descendants. Writes stop with this frozen handoff.

## Baseline, exact target and dependencies

Baseline source commit: `ff3751ea588ad5840d49fc0fb0e23c71215766d7`.
Committed `candidate_receiver.rs` base SHA-256: `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`.
Exact reconstructed target: `crates/yu-solver/src/candidate_receiver.rs`, 296,602 bytes / 5,872 newline-terminated lines, SHA-256 `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`.

The target was reconstructed in process memory from the baseline blob by applying the frozen R117 rev-2 patch (`c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`) followed by the corrected R119 patch (`5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a`). The R127 ordered composition receipt `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e` records the same reviewed order and target. Each hunk's complete old payload had one exact match; no context was dropped and no fuzzy application used. R119's earlier malformed patch revision was rejected and not used.

Pinned committed dependencies were independently hash-checked at the baseline:

| Dependency | SHA-256 | Static compatibility observation |
|---|---|---|
| `crates/yu-solver/src/lib.rs` | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` | R134's committed test-only trace target; no receiver API introduced or changed by R134. |
| `crates/yu-solver/src/candidate_scheme.rs` | `9cb8349a6ad43ddde8f54ae04ea464a61781b626b25917e928d45d49de3b2012` | Existing provider and selected-arm operation identity fields used by the receiver remain the referenced scheme API. |
| `crates/yu-solver/src/candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` | Defines the retained `FormalEntryPermission` fields, `concrete: Vec<SourceEffectId>`, views and operation-view provenance read by the receiver. |

Static symbol/field inspection found the candidate's references in these pinned blobs and no R134 receiver-interface change. This is not compiler evidence or a borrow/type check.

## Complete receiver hunk inventory

R117 adds provider member/family plus permission index/reference to the captured projection and request; makes registration lookup unique and validates retained permission identity, owner, occurrence, annotation/source rows and entry effect; validates provider/member/view/selected-arm links; and adds owner, batch, live-state, provider-origin and retained-permission capture guards.

R119 adds `permission_member_index: Option<usize>` to projection and request. Capture records the first matching concrete permission position with `.position(...)`; the request transports that field; the existing consumer validates the value by `.get(index)` against the provider family. Six R117 and six R119 hunks were applied in order. Their complete frozen unified hunks are the patch artifacts identified above; the exact added/replaced payloads are reproduced below.

```diff
@@ -231,4 +231,8 @@ pub(super) struct ProviderNativeContextProjection<'a> {
     /// can collide while naming different fact owners.
     pub(super) catch_fact_owner: ProviderFactOwner,
     pub(super) provider_view_index: usize,
+    pub(super) provider_member_index: usize,
+    pub(super) provider_family: &'a yu_hir::shadow::SourceEffectId,
+    pub(super) permission_index: usize,
+    pub(super) permission: &'a candidate_effect::FormalEntryPermission,
@@ -603,7 +607,11 @@ struct InventoryCatchRequest<'a> {
     collected_fact_index: usize,
     provider_view_index: usize,
     selected_arm_index: usize,
+    provider_member_index: usize,
+    provider_family: &'a yu_hir::shadow::SourceEffectId,
+    permission_index: usize,
+    permission: &'a candidate_effect::FormalEntryPermission,
     raw_input: EffectEndpointKey,
     canonical_input: EffectEndpointKey,
     raw_output: EffectEndpointKey,
     canonical_output: EffectEndpointKey,
@@ -1860,12 +1868,32 @@ impl<'a> InventoryPackage<'a> {
-        let (permission_index, permission) = self.permissions.get(request.registration)?;
-        if *permission_index != request.registration
-            || permission.registration != request.registration
-            || &permission.source_owner != request.target_owner
-            || permission.occurrence != *request.lambda_occurrence
-            || permission.annotation_position != *request.annotation_position
-            || permission.source_row != *request.source_row
-            || permission.entry_effect != request.raw_entry
-        {
-            return None;
-        }
+        let mut matching_permissions = self.permissions.iter().filter(|(_, permission)| {
+            permission.registration == request.registration
+        });
+        let (permission_index, permission) = matching_permissions.next()?;
+        if matching_permissions.next().is_some() {
+            return None;
+        }
+        if *permission_index != self.catch.permission_index
+            || !std::ptr::eq(*permission, self.catch.permission)
+            || permission.registration != request.registration
+            || &permission.source_owner != request.target_owner
+            || permission.occurrence != *request.lambda_occurrence
+            || permission.annotation_position != *request.annotation_position
+            || permission.source_row != *request.source_row
+            || permission.entry_effect != request.raw_entry
+            || !self.catch.permission.concrete.iter().any(|family| family == self.catch.provider_family)
+            || self.catch.provider_view_index != self.provider_view_index
+            || self.catch.selected_arm_index != self.owner_call.selected_arm_index
+            || self.owner_call.provider_identity != self.owner_call.operation_identity
+            || self.owner_call.provider_identity.family != *self.catch.provider_family
+            || !matches!(self.provider_endpoint,
+                EffectEndpointKey::AnnotationMember(view, member)
+                    if usize::try_from(view).ok() == Some(self.catch.provider_view_index)
+                        && usize::try_from(member).ok() == Some(self.catch.provider_member_index))
+            || self.views.get(self.catch.provider_view_index)
+                .is_none_or(|(index, view)| *index != self.catch.provider_view_index
+                    || view.allowed.get(self.catch.provider_member_index)
+                        != Some(self.catch.provider_family))
+        {
+            return None;
+        }
@@ -4844,3 +4872,7 @@ impl<'a> InventoryPackage<'a> {
             provider_view_index: provider.provider_view_index,
             selected_arm_index,
+            provider_member_index: provider.provider_member_index,
+            provider_family: provider.provider_family,
+            permission_index: provider.permission_index,
+            permission: provider.permission,
             raw_input: native.raw_lower_endpoint,
@@ -5052,4 +5084,10 @@ impl<'a> ProviderNativeContextProjection<'a> {
         let effect_state = &graph.intrusion.effect_algebra;
         let views = collect_owned_borrowed_inventory(effect_state.views.iter().enumerate())
             .ok_or(candidate_context::CurrentEmissionGap::SearchLimit)?;
+        if !std::ptr::eq(source_internal.native.owner, owner)
+            || !std::ptr::eq(source_internal.native.batch, &owner.session.batch)
+            || !std::ptr::eq(source_internal.native.live_state, &effect_state.context)
+        {
+            return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
+        }
@@ -5106,12 +5144,43 @@ impl<'a> ProviderNativeContextProjection<'a> {
         if origin.occurrence != owner.schema.provider
             || !Arc::ptr_eq(&origin.declaration, &owner.schema.operation)
+            || origin.declaration.id != owner.schema.provider_identity
+            || owner.schema.provider_identity != owner.schema.operation.id
+            || owner.schema.selected_arm.operation_identity != owner.schema.selected_arm.operation.id
+            || owner.schema.selected_arm.operation_identity != owner.schema.provider_identity
         {
             return Err(candidate_context::CurrentEmissionGap::MissingProviderOrigin);
         }
+        let retained = &source_internal.internal_incidence.permission;
+        let mut matching_permissions = source_internal.formal_entry_permissions.iter().filter(|(_, permission)| {
+            permission.registration == retained.registration
+        });
+        let Some((permission_index, permission)) = matching_permissions.next() else {
+            return Err(candidate_context::CurrentEmissionGap::MissingInternalCertificate);
+        };
+        if matching_permissions.next().is_some()
+            || permission.parameter != retained.parameter
+            || permission.formal != *retained.formal
+            || permission.occurrence != *retained.occurrence
+            || permission.source_owner != *retained.source_owner
+            || permission.scope != *retained.scope
+            || permission.annotation_position != *retained.annotation_position
+            || permission.source_row != *retained.source_row
+            || permission.entry_effect != retained.entry_effect
+            || permission.concrete.as_slice().as_ptr() != retained.concrete.as_ptr()
+            || !permission.concrete.iter().any(|family| family == &owner.schema.provider_identity.family)
+            || owner.schema.selected_arm.operation_identity.family != owner.schema.provider_identity.family
+        {
+            return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
+        }
         let result = Self {
             source_internal,
             provider,
             views,
             catch_fact_owner: ProviderFactOwner::BatchOccurrence(catch_fact_index),
             provider_view_index: view_index as usize,
+            provider_member_index: member_index as usize,
+            provider_family: owner_view.allowed.get(member_index as usize)
+                .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?,
+            permission_index: *permission_index,
+            permission,
         };
```

```diff
@@ -237,5 +237,6 @@ pub(super) struct ProviderNativeContextProjection<'a> {
     pub(super) provider_member_index: usize,
     pub(super) provider_family: &'a yu_hir::shadow::SourceEffectId,
     pub(super) permission_index: usize,
+    pub(super) permission_member_index: Option<usize>,
     pub(super) permission: &'a candidate_effect::FormalEntryPermission,
@@ -610,4 +611,5 @@ struct InventoryCatchRequest<'a> {
     provider_family: &'a yu_hir::shadow::SourceEffectId,
     permission_index: usize,
+    permission_member_index: Option<usize>,
     permission: &'a candidate_effect::FormalEntryPermission,
     raw_input: EffectEndpointKey,
@@ -1878,7 +1880,9 @@ impl<'a> InventoryPackage<'a> {
             || permission.occurrence != *request.lambda_occurrence
             || permission.annotation_position != *request.annotation_position
             || permission.source_row != *request.source_row
             || permission.entry_effect != request.raw_entry
-            || !self.catch.permission.concrete.iter().any(|family| family == self.catch.provider_family)
+            || self.catch.permission_member_index
+                .and_then(|index| self.catch.permission.concrete.get(index))
+                != Some(self.catch.provider_family)
             || self.catch.provider_view_index != self.provider_view_index
             || self.catch.selected_arm_index != self.owner_call.selected_arm_index
@@ -4880,4 +4884,5 @@ impl<'a> InventoryPackage<'a> {
             provider_family: provider.provider_family,
             permission_index: provider.permission_index,
+            permission_member_index: provider.permission_member_index,
             permission: provider.permission,
             raw_input: native.raw_lower_endpoint,
@@ -5145,13 +5150,19 @@ impl<'a> ProviderNativeContextProjection<'a> {
             || permission.scope != *retained.scope
             || permission.annotation_position != *retained.annotation_position
             || permission.source_row != *retained.source_row
             || permission.entry_effect != retained.entry_effect
             || permission.concrete.as_slice().as_ptr() != retained.concrete.as_ptr()
-            || !permission.concrete.iter().any(|family| family == &owner.schema.provider_identity.family)
+            || permission.concrete.iter()
+                .position(|family| family == &owner.schema.provider_identity.family)
+                .is_none()
             || owner.schema.selected_arm.operation_identity.family != owner.schema.provider_identity.family
         {
             return Err(candidate_context::CurrentEmissionGap::BoundMismatch);
         }
+        let provider_family = owner_view.allowed.get(member_index as usize)
+            .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?;
+        let permission_member_index = permission.concrete.iter()
+            .position(|family| family == provider_family);
         let result = Self {
             source_internal,
             provider,
@@ -5158,8 +5169,8 @@ impl<'a> ProviderNativeContextProjection<'a> {
             catch_fact_owner: ProviderFactOwner::BatchOccurrence(catch_fact_index),
             provider_view_index: view_index as usize,
             provider_member_index: member_index as usize,
-            provider_family: owner_view.allowed.get(member_index as usize)
-                .ok_or(candidate_context::CurrentEmissionGap::BoundMismatch)?,
+            provider_family,
             permission_index: *permission_index,
+            permission_member_index,
             permission,
         };
```

## Capture → request → indexed consumer audit

R117 capture binds the source-internal retained permission to exactly one registered permission entry and rejects duplicate registration matches. It preserves checks for native owner/batch/live-state identity, selected provider/declaration/arm identity, matching family, and provider view/member coordinates. `ProviderNativeContextProjection` retains the permission reference and its packed `permission_index`, separately from `provider_view_index` / `provider_member_index`.

R119 capture finds the first matching concrete permission position by `.position(...)`, stores it as `permission_member_index: Option<usize>`, and carries it unchanged into `InventoryCatchRequest`. At the consumer, `.get(index)` must produce the captured provider family. The packed permission index, native view/member indices, concrete-vector index, and family value are distinct coordinates. `None` and out-of-range indices fail the indexed check. Unique registration lookup rejects duplicate registration entries. Foreign source owner, occurrence, row, entry effect, native owner/batch/state, and provider identity mismatches remain guarded by the surrounding checks. Request-construction fallback/early-return behavior is unchanged; the new predicates only preserve the existing `None` rejection/fallback path.

First-position preservation is source-level transport: for duplicate values such as `[4,9,9]`, `.position(9)` yields 1 and the candidate copies that exact `Option<usize>` through the request. The local consumer check alone is weaker: substituting index 2 still reads an equal `9` and can pass. Thus this static inspection does not establish protection against arbitrary in-memory tampering; it observes the direct field transport in this candidate. Nor does it establish execution reachability, borrow checking, vector provenance/length from pointer comparison, the Rust-to-Lean operational relation, or the original A/B/effect-hygiene theorem.

R134 changed only committed `lib.rs` and `candidate_source.rs` test-observation instrumentation, plus relies on the pinned test-only recorder in `candidate_effect.rs`. Its source trace records action/constraint/propagation/diagnostic observations and does not change `candidate_receiver.rs` APIs. The R134 trace is provisional source evidence and does not establish this receiver path's execution.

## Prior evidence and boundaries

Reused R127's reviewed ordered-composition receipt and implementation handoff revision 2, including the exact target hash, 296,602-byte count, hunk map, and warning that `[4,9,9]` exposes a local index-substitution weakness. Reused the accepted R117 revision-2 patch and R119 corrected patch. Rejected R119's malformed earlier patch, R120's receiver hash based on an unmodified pre-R111 base, and any inference from static source checks or R134 traces to compiled/executed behavior or theorem closure.

Checks performed: read-only committed blob and patch reads; in-memory exact-context sequential reconstruction with unique-match checks; final byte-count, newline-line-count and SHA-256 comparison; static API field/reference inspection against the three pinned dependencies. No tests/build/Lean/checker were run, as prohibited by the contract. Active wall/CPU/RSS telemetry is `UNKNOWN`; assignment maximum is 240 seconds, and the work stopped after this single reconstruction/handoff.

No source constructor, expected output, diagnostic, source domain, natural inference or fallback behavior was altered. No Simple-sub bypass was restored. R111's private compile/resource gate remains unmet; this candidate remains uncompiled and untested. The original A/B, Rust-to-Lean correspondence, effect hygiene and production gates remain OPEN.

New repository path: this leased handoff only. Generated/scratch paths: none. No other paths were written. Worker state: `STOPPED_WRITING`; no descendant or disposable output lease remains.

Frozen handoff revision: 1. SHA-256 is to be computed over these exact frozen file bytes by Luna after intake. Required next step: fresh independent compiler-referee review of this handoff and the pinned committed dependencies, max 240 seconds; this producer does not self-certify. A PASS can permit Luna to apply only the exact target after all separate R111 gates and integration conditions are met.
