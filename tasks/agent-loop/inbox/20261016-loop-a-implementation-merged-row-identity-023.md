Request-ID: LOOP-A-I17-MERGED-ROW-IDENTITY-023
Revision: 1
From: implementer (`/root/i17_merged_row_identity`; requested gpt-6-luna/high, observed runtime settings UNKNOWN)
To: next_action_selector
Parent-gate: I17 canonical CandidateGraphRow identity verification; original source correspondence, soundness/principality, Simple-sub/F5, and production gates remain OPEN
Baseline: `ecc6cf5595c619fbfc3f20465e9693eaf070eefe`; leased source input `shadow_apply.rs` SHA-256 before edit `4155a3bb3e632dee66a5db498cbff6f3a63da68e1b5d1d04b18719db610fe1a4`; other pinned input hashes listed below
Kind: implementation
Claim/task: Add one native regression showing that actual retained raw parent/copy RowKeys selected from a source-qualified same-SCC intrusion parent compare/hash as one canonical CandidateGraphRow identity after solving the existing nested-recursion source.
Missing-evidence: I12's identity test covered duplicate raw Value(7), Effect(7), independent state, and first-locality retention, but not two distinct raw keys actually merged by SCC-qualified intrusion. This bounded regression supplies that consumer evidence only.
Owners: `crates/yu-solver/src/shadow_apply.rs::tests::candidate_graph_row_hashing_uses_merged_representatives`; existing source fixture `crates/yu-solver/tests/candidate_intrusion_observation.rs`; existing local-source helper `crates/yu-solver/src/lib.rs::candidate_lifecycle_retirement::hir`; canonical consumer `CandidateGraphRow::{same_identity, PartialEq, Hash}`
Depends-on: I12 canonical row identity implementation, I16-R1 baseline `ecc6cf5595c619fbfc3f20465e9693eaf070eefe`, existing nested-recursion source fixture
Scope: Test-only addition under `#[cfg(test)]` in `shadow_apply.rs`; one inbox receipt. Source is solved normally; selection requires differing raw ordinals, same ComponentKind, equal observed final representatives, and an actual `same_scc=true` source event. The test takes actual private retained keys at that parent ordinal, borrows the same immutable finalized GraphState for both handles, and uses only an identity-only test Graph. No production, solver-state, graph-representation, language-semantic, or test-contract changes. This test Graph does not represent source formation and does not close source correspondence or any theorem.
Acceptance: A nonvacuous qualifying parent exists; actual keys differ and their final representatives agree; handle identity agrees with Eq; same DefaultHasher outputs; HashMap lookup and entry reuse the first row/index/locality. Both assigned focused commands pass; source diff is limited to this test; `git diff --check` passes.
Proposed-outputs: `crates/yu-solver/src/shadow_apply.rs`, this inbox receipt
Checks/resources: Serial; each command timeout 180s, `CARGO_BUILD_JOBS=2`, one test thread; no other tests/builds/benchmarks. Command 1 `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-solver --features shadow-apply-candidate --lib shadow_apply::tests::candidate_graph_row_hashing_uses_merged_representatives -- --exact --test-threads=1` passed: 1 passed, 0 failed, 714 filtered, 0.02s test / 8.23s compile; emitted one unused-import warning for `RowKey` in the new test. Command 2 `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli recursive_graph_is_finite_and_deterministic -- --exact --test-threads=1` passed: 1 passed, 0 failed, 21 filtered, 0.03s test / 2.99s compile. `git diff --check -- crates/yu-solver/src/shadow_apply.rs` passed.
Prior-work: Reused I12/R19 accepted `candidate_graph_row_hashing_matches_identity` for canonical identity, HashMap usage, and first stored row/locality; reused the exact nested-recursion fixture from `candidate_intrusion_observation.rs` and the local-source `candidate_lifecycle_retirement::hir` helper. Adapted only by selecting a real observed parent ordinal and reading that parent's actual retained private RowKeys from the same finalized state. I16's false foreign-selected fixture premise was not reused. No superseded Simple-sub bypass was recreated; no prior semantic or proof claim was promoted.
Priority-reason: Directly checks the remaining I12 aliasing coverage gap at the existing canonical Eq/Hash consumer, while retaining the original open source/proof/production gates.
Stop/escalate: No obstruction. Source SHA-256 after edit: `401b2406c7c4ac01d217752f431a9006eb5452731d71f90c7993ab293a0848e5`. Inbox SHA-256 is to be recorded after freeze. No independent review claimed. Freeze this receipt and source before review; next action is dispatcher consultation for bounded review/adjudication. No implementation escalation requested.

## Frozen input pin checks

The following six non-leased inputs still match their launch pins after both checks:

- `crates/yu-solver/src/candidate_scheme.rs`: `2ce5d664bdce1417379cd80767bc53643b6e40740a9fe7e942c24c2009da351e`
- `crates/yu-solver/src/candidate_intrusion.rs`: `7a57a93481095c6e7d4b8781810b1a5aa0d174e41ede29ac3f2b2b96bce10b0c`
- `crates/yu-solver/tests/candidate_intrusion_observation.rs`: `04a876b9fe0a3a45f2d1996446a11d0b36dce3bb26ad02537118e4853e4b78e1`
- `tools/inference-playground/src/render.rs`: `26b6078546a4ac99716af32e6e8036c610118786f7698fabc5c83c67dc836c9a`
- `tools/inference-playground/tests/cli.rs`: `4085d5e8f2c00a982419f236d92e58aa6d20fd469df6e1beeb6f35148aeaf8ea`
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`

The leased `shadow_apply.rs` pin naturally differs after this test-only edit; its frozen output hash is above. The exact launch pins were checked immediately before the assigned test commands.

## Literal baseline diff

```diff
diff --git a/crates/yu-solver/src/shadow_apply.rs b/crates/yu-solver/src/shadow_apply.rs
index 95328178d..a3594506b 100644
--- a/crates/yu-solver/src/shadow_apply.rs
+++ b/crates/yu-solver/src/shadow_apply.rs
@@ -2163,6 +2163,71 @@ mod tests {
         assert_eq!(solve_indices.len(), 2);
     }

+    #[test]
+    fn candidate_graph_row_hashing_uses_merged_representatives() {
+        use crate::candidate_scheme::{Graph, Row, RowKey};
+        use std::collections::hash_map::DefaultHasher;
+        use std::hash::{Hash, Hasher};
+
+        let hir = crate::candidate_lifecycle_retirement::hir(
+            "my loop x = { my helper y = loop y; helper x }",
+        );
+        let candidate = CandidateInference::solve(hir).unwrap();
+        let observation = candidate.intrusion_observation().unwrap();
+        let events: Vec<_> = observation.events().collect();
+        let parents: Vec<_> = observation.parents().collect();
+        let selected = parents
+            .iter()
+            .find(|parent| {
+                parent.copy.ordinal != parent.parent.ordinal
+                    && parent.copy.kind == parent.parent.kind
+                    && parent.copy.representative == parent.parent.representative
+                    && parent.source_events.iter().any(|&event| {
+                        events.get(event).is_some_and(|event| event.same_scc)
+                    })
+            })
+            .expect("nested recursion retains a same-SCC parent/copy merge");
+        let state = candidate.solved.data.candidate_graph.as_ref().unwrap();
+        let retained = state.intrusion.parents[selected.ordinal];
+        let copy_key = retained.copy;
+        let parent_key = retained.parent;
+        assert_ne!(copy_key, parent_key, "selected raw parent/copy keys differ");
+        assert_eq!(state.intrusion.rep(copy_key), state.intrusion.rep(parent_key));
+
+        let graph = Graph {
+            source_frontier: Vec::new(),
+            owned_regions: Vec::new(),
+            negative_functions: HashMap::new(),
+            nodes: Vec::new(),
+            rows: vec![
+                Row { key: copy_key, local: false },
+                Row { key: parent_key, local: true },
+            ],
+            bounds: Vec::new(),
+            bound_evidence: Vec::new(),
+            attachment_bundles: Vec::new(),
+            attachment_spans: HashMap::new(),
+            context_views: Vec::new(),
+            root: 0,
+            live_root: 0,
+            boundary: 0,
+        };
+        let first = CandidateGraphRow { state, graph: &graph, index: 0 };
+        let second = CandidateGraphRow { state, graph: &graph, index: 1 };
+        assert_eq!(first.same_identity(second), first == second);
+        assert!(first.same_identity(second));
+
+        let mut first_hasher = DefaultHasher::new();
+        first.hash(&mut first_hasher);
+        let mut second_hasher = DefaultHasher::new();
+        second.hash(&mut second_hasher);
+        assert_eq!(first_hasher.finish(), second_hasher.finish());
+
+        let mut indices = HashMap::new();
+        indices.insert(first, 0);
+        assert_eq!(indices.get(&second), Some(&0));
+        indices.entry(second).or_insert(1);
+        assert_eq!(indices.len(), 1, "merged rows share one index");
+        let (stored, index) = indices.get_key_value(&second).unwrap();
+        assert_eq!(*index, 0);
+        assert_eq!(stored.index, 0);
+        assert!(!graph.rows[stored.index].local);
+    }

     #[test]
     fn candidate_graph_fresh_use_refuses_conflicts_and_preserves_valid_use() {
```

Known generated outputs are confined to shared Cargo `target/` artifacts; no disposable path is identified for worker cleanup. Preexisting pending question and unrelated inbox files remain untouched. Requested settings are Luna/high; runtime did not report observed model/effort, so observed remains UNKNOWN.
