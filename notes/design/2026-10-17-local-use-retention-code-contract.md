# Local-use FreshUse retention code contract

Status: Draft; unapplied proposal repair, pending independent architect/spec
review and explicit user approval. No compiler source has been changed.
Sprint: `local-use-retention-proposal-repair-20261017`, revision 1.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.

## Decision requested

At successful `commit_local_use`, keep `FreshUse.rows` as the existing
`LocalFreshRoute.rows` owner and move every other `FreshUse` field exactly once
into a separate retained-maps record owned by that route. Keep the captured
`Graph` and existing `rows` field unchanged. This is a representation proposal
only. It neither adds semantic NPAIR evidence nor authorizes a subtraction or
receive consumer.

The exact patch below changes only `crates/yu-solver/src/candidate_scheme.rs`
if approved. It adds no public API and preserves the existing `rows` field used
by `shadow_apply::fresh_use` and tests. It retains the other maps for finite
registered structural queries at the pinned precommit version, subject to M2's
validity and lifetime conditions. The proof uses `v0` as a logical parameter;
this patch does not add a version field, historical snapshot protocol, or
`Invalid(v0)` checker.

Retaining construction maps increases session memory and may cause earlier
resource-limit rejection. The practical envelope and overhead are unmeasured; no
unchanged resource-acceptance claim is made.

## Chosen proposal and alternatives

1. **Split and retain the non-row maps once (proposed).** Keep the existing
   `LocalFreshRoute.rows` owner. Move `scope_remap`, `scoped_relations`,
   `context_use`, `terms`, `effect_operands`, `bundle_remap`, `context_remap`
   and `evidence_remap` into one route-owned record. This preserves current
   `rows` consumers without duplicating its vector. It retains more session
   memory than current code.
2. **Build a compact immutable Qmap projection.** This could retain fewer
   bytes, but first needs a concrete registered-query type and a reviewed proof
   that the projection preserves every required key, miss, membership bit and
   use association. No such type exists in the inspected code.
3. **Create a session-owned semantic Use ledger.** This is the broader NPAIR
   architecture candidate. It can eventually own descriptors, derivations,
   providers, use identities and pending subscriptions, but current producers
   do not supply all those facts. It is not implemented by this patch.

The requested decision is option 1 only as a bounded structural-retention
step. Choosing a compact projection, a semantic ledger, or their future
invalidation API remains a separate design decision. The retained maps alone
cannot authenticate descriptor/Permission, At, provider lineage, consumer
selection or future absence. The increased-memory and possible earlier
resource-rejection tradeoff above is part of option 1.

## Source correspondence and publication boundary

At the frozen source baseline, `FreshUse` owns `scope_remap`,
`scoped_relations`, `context_use`, `rows`, `terms`, `effect_operands`,
`bundle_remap`, `context_remap` and `evidence_remap`. The revision-2 proof
inventory identifies their constructor/restoration coordinates and its exact
finite Qmap subset. Current `commit_local_use` moves `graph` and `rows`, then
drops the other maps.

The caller in `lib.rs::finish_route_transaction_with_candidate_accounting`
calls `commit_local_use` only after the operation succeeds and after the last
fallible route work. Before that call, `step_candidate_local_use` reserves
`local_routes` capacity and records the old allocation in the route journal.
On failure, rollback restores the cursor, truncates new routes and restores the
old allocation. On success, the journal is discarded. The proposal therefore
moves already allocated maps at this existing boundary; it does not add a
fallible publication step or require exact restoration of private capacities.

The precommit-state theorem is revision 2's M2, not a stronger claim:

- For a registered query `q` whose retained postcommit evaluation is valid at
  pinned precommit version `v0`, its answer equals `q(v0)`.
- An unavailable or changed projection is outside the equality conclusion.
  A future checking protocol may report `Invalid(v0)` separately; this patch
  does not implement that protocol.
- A query that dereferences a native ID still requires the original owner,
  non-reuse, relocation safety and unchanged read projection premises.
- Only the immediate Graph/rows movement is a current-code corollary. The
  current source does not retain the other maps after commit.

## Exact unapplied patch

```diff
diff --git a/crates/yu-solver/src/candidate_scheme.rs b/crates/yu-solver/src/candidate_scheme.rs
--- a/crates/yu-solver/src/candidate_scheme.rs
+++ b/crates/yu-solver/src/candidate_scheme.rs
@@
 pub(super) struct LocalFreshRoute {
     pub slot: usize,
     pub local: yu_hir::HirLocalId,
     pub occurrence: HirOccurrenceId,
     pub graph: Graph,
     pub rows: Vec<RowKey>,
+    retained: RetainedFreshUseMaps,
 }
@@
+#[derive(Debug)]
+struct RetainedFreshUseMaps {
+    scope_remap: candidate_source::ScopeRemap,
+    scoped_relations: HashMap<candidate_context::RelationId, candidate_context::ScopedFlow>,
+    #[allow(dead_code)]
+    context_use: usize,
+    terms: Vec<Option<Term>>,
+    effect_operands: HashMap<usize, EffectEndpointKey>,
+    bundle_remap: HashMap<candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId>,
+    context_remap: HashMap<candidate_context::ContextId, candidate_context::ContextId>,
+    evidence_remap: Vec<candidate_context::EvidenceSnapshotId>,
+}
+impl RetainedFreshUseMaps {
+    fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
+        sum(&[
+            self.scope_remap.bytes()?,
+            bytes::<(candidate_context::RelationId, candidate_context::ScopedFlow)>(self.scoped_relations.capacity())?,
+            bytes::<Option<Term>>(self.terms.capacity())?,
+            bytes::<(usize, EffectEndpointKey)>(self.effect_operands.capacity())?,
+            bytes::<(candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId)>(self.bundle_remap.capacity())?,
+            bytes::<(candidate_context::ContextId, candidate_context::ContextId)>(self.context_remap.capacity())?,
+            bytes::<candidate_context::EvidenceSnapshotId>(self.evidence_remap.capacity())?,
+        ])
+    }
+}
@@
 impl FreshUse {
@@
     fn bytes(&self) -> Result<usize, SolveAvailabilityError> {
         sum(&[self.scope_remap.bytes()?, bytes::<(candidate_context::RelationId, candidate_context::ScopedFlow)>(self.scoped_relations.capacity())?, bytes::<RowKey>(self.rows.capacity())?, bytes::<Option<Term>>(self.terms.capacity())?,
             bytes::<(usize, EffectEndpointKey)>(self.effect_operands.capacity())?,
             bytes::<(candidate_context::AttachmentBundleId, candidate_context::AttachmentBundleId)>(self.bundle_remap.capacity())?,
             bytes::<(candidate_context::ContextId, candidate_context::ContextId)>(self.context_remap.capacity())?,
             bytes::<candidate_context::EvidenceSnapshotId>(self.evidence_remap.capacity())?])
     }
+    fn into_retained_parts(self) -> (Vec<RowKey>, RetainedFreshUseMaps) {
+        let FreshUse { scope_remap, scoped_relations, context_use, rows, terms,
+            effect_operands, bundle_remap, context_remap, evidence_remap } = self;
+        (rows, RetainedFreshUseMaps { scope_remap, scoped_relations, context_use,
+            terms, effect_operands, bundle_remap, context_remap, evidence_remap })
+    }
 }
@@
-        // All capacities and arithmetic were preflighted by frame accounting and
-        // final route reservation. Only construction maps are released here.
-        let released = frame.fresh.bytes().expect("accounted fresh storage")
-            - bytes::<RowKey>(frame.fresh.rows.capacity()).expect("accounted rows");
+        // All capacities and arithmetic were preflighted by frame accounting and
+        // final route reservation. Move retained maps without allocation.
+        let (rows, retained) = frame.fresh.into_retained_parts();
         self.local_routes.push(LocalFreshRoute { slot: frame.slot, local: frame.local,
-            occurrence: frame.occurrence, graph: frame.graph, rows: frame.fresh.rows });
-        self.retained_bytes -= released;
+            occurrence: frame.occurrence, graph: frame.graph, rows, retained });
@@
         for route in &self.local_routes {
-            total = sum(&[total, route.graph.bytes()?, bytes::<RowKey>(route.rows.capacity())?])?;
+            total = sum(&[total, route.graph.bytes()?, bytes::<RowKey>(route.rows.capacity())?, route.retained.bytes()?])?;
         }
```

The real patch should be emitted by normal diff tooling after approval; this
proposal file remains the only artifact containing it. The existing
`shadow_apply::fresh_use` adapter and tests retain their current `route.rows`
access unchanged. The `refresh_bytes`
census counts the inline `RetainedFreshUseMaps` header and unchanged route
`rows` field through `size_of::<LocalFreshRoute>()`, then counts the row vector
and retained map backing capacities separately. `retained.bytes()` excludes
rows, so every backing allocation is counted exactly once. `retained_bytes`
already includes all `FreshUse` backing allocations before commit. No backing
allocation is released after the split, so commit must not subtract that charge.
Route-slot growth uses `size_of::<LocalFreshRoute>()` and remains preflighted and
included in journal resource accounting. The additional retained storage may
cause earlier resource-limit rejection; practical overhead and acceptance limits
are unmeasured.

No `lib.rs` patch is proposed: the transaction already has the required
success publication point and rollback boundary. If review finds that its
reservation or accounting omits the changed route element size, stop and revise
the proposal before any source write.

## Required review and post-approval checks

Architect review must validate the exact moved fields, infallible publication,
rollback/truncation lifetime, vector growth accounting and native-ID lifetime
limits. Spec review must check that the representation does not promote
structural maps into semantic evidence or change the adopted NPAIR boundaries.
Both reviews must use the pinned proof revision and this exact unapplied patch.
Architect review must confirm `LocalFreshRoute.rows` remains the sole row-vector
owner and current consumers continue to use it.

Only after both reviews are CLEAN and the user approves this exact option may a
separate code sprint be opened. That sprint must review call sites, adapt tests
without changing expected outputs, and implement the single-file patch. It must
also define the consumer API and lifetime/invalidation before allowing later
dereferences. Suggested focused cases: successful commit then each map lookup;
failure before publication; rollback and retry; stale/reused IDs; relocation;
and resource accounting with large map capacities. These checks are not run or
authorized in this proposal sprint.

Not proved or selected here: whole native `rho_u`, source/native adequacy,
formal negative-pair formation, ingress/At lineage, provider identity,
future scheduling/progress, receive subtraction, principality, source
completeness or production authority.

## Provenance and pins

Corrected proof artifact:
`notes/theory/2026-10-17-local-use-existing-map-retention.md`, SHA-256
`f214960d2e1ac04f361a01f0802539ea9c961099fc9b55faa93d023f8cabac2e`.
Correction handoff:
`tasks/agent-loop/inbox/20261017-local-use-map-version-repair.md`, SHA-256
`2d3ca0ff0115f4098dd763b8c9ec3d8468d00c47007f51cca66d93bbad0218e2`.
Previous proof sprint contract revision 3 SHA-256
`be13224abe1dcfbcbc9e1c9eea8bfb83e9b2192854e8bdfb9e28ba4ed584e049`.
Compiler baseline `candidate_scheme.rs` SHA-256
`2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`.
R1 SHA-256 `c5c069798cd5822918e09438ac7e82e627d562ba0b13f8233ca5709e43f9c922`.

The v2 M2 correction received a fresh CLEAN compiler_referee delta review. The
reviewer verified those hashes, the immutable v1 snapshot, R1 and the exact
`candidate_scheme.rs` source pin, and STOPPED. Full details are in
`tasks/agent-loop/current.json`. Review scope was only the M2 correction and
dependent statements; it did not certify the proposed patch or broader proof.

Correction sprint: `local-use-retention-proposal-repair-20261017`, revision 1.
Previous design snapshot SHA-256
`a346ef6812109eb181cf160127959ac8320389b1a8a2d52e566464039601fb55`; previous
handoff snapshot SHA-256
`572e06a32b268dc3d089c5b4d27b4361fa194ca133857dc6bb2da8c7edec14ad`.
Author: Luna / primary; exact writes limited to this design and the new repair
handoff. No source edits, tests, probes, builds, Cargo, compiler execution or
external contact.
