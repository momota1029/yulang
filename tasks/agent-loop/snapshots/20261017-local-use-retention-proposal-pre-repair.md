# Local-use FreshUse retention code contract

Status: Draft; unapplied proposal, pending independent architect/spec review and
explicit user approval. No compiler source has been changed.
Sprint: `local-use-existing-map-retention-20261017`, revision 3.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`, OPEN.

## Decision requested

At successful `commit_local_use`, move the complete already-built `FreshUse`
value into its `LocalFreshRoute`, alongside the captured `Graph`. Keep the
existing per-use maps intact for later structural lookup. This is a
representation proposal only. It neither adds semantic NPAIR evidence nor
authorizes a subtraction or receive consumer.

The exact patch below changes only `crates/yu-solver/src/candidate_scheme.rs`
if approved. It adds no public API and no new source behavior. It keeps the
existing maps available for finite registered structural queries at the pinned
precommit version, subject to M2's validity and lifetime conditions. The proof
uses `v0` as a logical parameter; this patch does not add a version field,
historical snapshot protocol, or `Invalid(v0)` checker.

## Chosen proposal and alternatives

1. **Move all of `FreshUse` into `LocalFreshRoute` (proposed).** This is the
   smallest source change and preserves exact map domains, misses and values.
   Its cost is retaining maps that a future consumer may not need.
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
selection or future absence.

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
-    pub rows: Vec<RowKey>,
+    pub fresh: FreshUse,
 }
@@
-        // All capacities and arithmetic were preflighted by frame accounting and
-        // final route reservation. Only construction maps are released here.
+        // All capacities and arithmetic were preflighted by frame accounting and
+        // final route reservation. Move the existing maps into the committed route.
-        let released = frame.fresh.bytes().expect("accounted fresh storage")
-            - bytes::<RowKey>(frame.fresh.rows.capacity()).expect("accounted rows");
         self.local_routes.push(LocalFreshRoute { slot: frame.slot, local: frame.local,
-            occurrence: frame.occurrence, graph: frame.graph, rows: frame.fresh.rows });
-        self.retained_bytes -= released;
+            occurrence: frame.occurrence, graph: frame.graph, fresh: frame.fresh });
@@
         for route in &self.local_routes {
-            total = sum(&[total, route.graph.bytes()?, bytes::<RowKey>(route.rows.capacity())?])?;
+            total = sum(&[total, route.graph.bytes()?, route.fresh.bytes()?])?;
         }
```

The real patch should be emitted by normal diff tooling after approval; this
proposal file remains the only artifact containing it. The
`Refresh_bytes` census already counts `LocalFreshRoute` vector capacity using
`size_of::<LocalFreshRoute>()`; that automatically accounts for the larger
inline `FreshUse` field. `FreshUse::bytes()` accounts for its separately
allocated map capacities. `retained_bytes` already includes the frame's
`FreshUse` backing allocations before commit, so moving them does not release
that charge. Route-slot growth remains preflighted by the existing allocator
and included in journal resource accounting.

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
Sprint contract revision 3 SHA-256
`be13224abe1dcfbcbc9e1c9eea8bfb83e9b2192854e8bdfb9e28ba4ed584e049`.
Compiler baseline `candidate_scheme.rs` SHA-256
`2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`.
R1 SHA-256 `c5c069798cd5822918e09438ac7e82e627d562ba0b13f8233ca5709e43f9c922`.

The v2 M2 correction received a fresh CLEAN compiler_referee delta review. The
reviewer verified those hashes, the immutable v1 snapshot, R1 and the exact
`candidate_scheme.rs` source pin, and STOPPED. Full details are in
`tasks/agent-loop/current.json`. Review scope was only the M2 correction and
dependent statements; it did not certify the proposed patch or broader proof.

Author: Luna / primary; exact writes limited to this design and its assigned
proposal handoff. No source edits, tests, probes, builds, Cargo, compiler
execution or external contact.
