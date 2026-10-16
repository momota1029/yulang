Request-ID: 20261016-loop-a-implementation-expression-intrusion-locations-025-result
Revision: 1
From: implementer; actual worker ID unknown
To: next_action_selector
Parent-gate: I18 executable packet, `tasks/agent-loop/board.md` §I18; approved rendering/source-ownership scope in `notes/design/2026-10-16-module-expression-source-owner.md` (G1–G4 source ownership; this packet is diagnostic lookup coverage only)
Baseline: `e7324e89d93546f648540fb88976b4aeee00ef48`; pre-edit pins matched: render.rs `26b6078546a4ac99716af32e6e8036c610118786f7698fabc5c83c67dc836c9a`, tests/cli.rs `4085d5e8f2c00a982419f236d92e58aa6d20fd469df6e1beeb6f35148aeaf8ea`, lib.rs `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb`, yu-hir/module.rs `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`, design `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`, shadow_apply.rs `3fb9335e94ded08ec800d3d4dd9ce6097bc74e3b2966dc70c0b34aadd4c547f7`
Kind: implementation
Claim/task: Extend renderer source lookup over original direct-expression roots using the approved authentic `SourceRootId::Expression` mapping. The code slice is implemented, but the bounded regression did not pass: its first fixture expected the whole `id 1` range while the native retained checking occurrence points at the final argument byte `1`.
Missing-evidence: First fixture observed a real retained event and authentic source span, but the new test's range expectation was wrong: actual is `1:4 (bytes 3..4)` with exact excerpt `id 1; my id x = x; my main = 7`. Actual event label is `origin=v0 (expression value, SCC 0)` and receiver label is `module id`. The test aborts on this first fixture, so the second fixture's event/local-helper label is unobserved. Corrected regression evidence is required before accepting the slice.
Owners: renderer owner `tools/inference-playground/src/render.rs::local_source_for_item`, `intrusion_into`, `source_value_into`; regression owner `tools/inference-playground/tests/cli.rs::intrusion_expression_calls_keep_original_spans_and_local_names`; HIR accessors are read-only at `crates/yu-hir/src/module.rs::HirModule::{expression_root,local_source_for}`.
Depends-on: none for the source-lookup implementation; continuation requires a newly dispatched bounded implementation assignment because the assigned stop-on-first-assertion-failure condition was reached.
Scope: Preserve first-match HIR item order, `.ok().flatten()` unavailable-source fallback, range clone, names/fallback labels, formatting, observation charges, byte/work caps and atomic output. Do not change inference/admission/initialization semantics, existing expected assertions, or proof status. The renderer edit is bounded diagnostic coverage, not proof of global source adequacy or production readiness.
Acceptance: Under a new exact lease, adjust only the new test's expected call-tail span to the observed original range (or equivalent source-derived exact assertion); run both originally specified commands in order, with the second only after the first passes. The second fixture must independently show the retained event, line-1 source excerpt, authentic expression-origin label, `local helper`, and no unavailable span. Do not weaken fixture/preflight or synthesize an owner. Freeze updated diff and results before review.
Proposed-outputs: `tools/inference-playground/src/render.rs`, `tools/inference-playground/tests/cli.rs`, and a new uniquely allocated inbox revision/path if dispatched. These are proposals, not leases.
Checks/resources: Requested implementer settings Luna/high minimum; observed settings unavailable. Exactly one Cargo command was run: `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_expression_calls_keep_original_spans_and_local_names -- --exact --test-threads=1` — exit 101, compile succeeded, one test failed at the first fixture's expected-location assertion; actual output recorded above. The second command `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_flag_observes_actual_source_associations -- --exact --test-threads=1` was not run because command 1 failed and the packet requires stopping at first failure. No other tests/builds/benchmarks ran. `git diff --check -- tools/inference-playground/src/render.rs tools/inference-playground/tests/cli.rs` passed.
Prior-work: Reused the authentic direct-item mapping precedent `tools/inference-playground/src/lib.rs::conflict_ranges_for` (current pinned hash above; binding/expression/error handling and `.ok().flatten()` fallback) and the existing renderer's binding-only occurrence/name walks. `git log -- tools/inference-playground/src/render.rs tools/inference-playground/tests/cli.rs` showed the renderer's candidate-graph indexing commits (`df18c552c`, `7e1140c90`), computation-root source-plan addition (`7c1a3753e`), and earlier discarded-expression CLI coverage (`1d298c18d`); none supplies this direct-expression lookup, so adapted only the source-owner lookup. Rejected/withdrawn Simple-sub bypasses were not used or recreated; no inference route changed.
Priority-reason: A corrected bounded test can establish whether both approved expression-source lookup sites retain their authentic labels and location while preserving existing binding-only behavior. This is independent of open Simple-sub metatheory; this report does not close any proof or production gate.
Stop/escalate: Stop at the observed test failure. No Luna implementation escalation requested; the evidence identifies a test expectation mismatch, not a remaining implementation/semantic bottleneck. Dispatcher should allocate a new exact lease if it wants the corrected regression and remaining command run.

Frozen artifact snapshot at write time:
- `tools/inference-playground/src/render.rs` SHA-256 `ccd8f6551c49cc5fe937258c9dcd03ae7d441e8932e8fb9480515f1b587093bf`
- `tools/inference-playground/tests/cli.rs` SHA-256 `ab36ed6ea71c9db18edfdf55ce168d425a7663f1cc310c712feb2cd65a4d714b`
- Current diff is exactly: imports add `LocalSource, SourceRootId`; private `local_source_for_item<'hir>(&'hir HirModule, &HirItem) -> Option<&'hir LocalSource>` maps Binding to cloned Definition root, Expression through `expression_root(occurrence).ok().flatten()` to cloned Expression root, Error to `None`, then resolves through `local_source_for(...).ok().flatten()`; both existing item-order `find_map` closures call the helper; one CLI test uses the two board fixtures and expects `module id` / `local helper`, a retained event, a source-derived call-tail location, and no unavailable span. The first fixture currently fails because expected `id 1` bytes `0..4` but observed retained occurrence bytes `3..4`. No old assertion changed.
- The only unrelated current paths observed were the pre-existing board edit, pending question draft, and inbox files `...budgeted-runtime-007.md`, `...definition-index-009.md`, `...expression-freshuse-006.md`, `...source-schedule-008.md`; they were not edited.

Exact unified diff for the frozen Rust changes:
```diff
diff --git a/tools/inference-playground/src/render.rs b/tools/inference-playground/src/render.rs
index 396676a97..1415e2880 100644
--- a/tools/inference-playground/src/render.rs
+++ b/tools/inference-playground/src/render.rs
@@ -1,7 +1,7 @@
 //! Finite observations of the existing private candidate graph.
 use std::collections::HashMap;
 use std::fmt::Write;
-use yu_hir::{HirItem, HirModule};
+use yu_hir::{HirItem, HirModule, LocalSource, SourceRootId};
 use yu_solver::shadow_apply::{CandidateGraphExport, CandidateGraphNode, CandidateGraphRow};
 use yu_solver::shadow_apply::{CandidateInference, CandidateSourceValueIdentity};
 
@@ -9,6 +9,19 @@ use crate::output::{Output, cap};
 
 pub const OUTPUT_CAP: usize = 4096;
 
+fn local_source_for_item<'hir>(hir: &'hir HirModule, item: &HirItem) -> Option<&'hir LocalSource> {
+    let root = match item {
+        HirItem::Binding(binding) => {
+            SourceRootId::Definition(binding.definition_root().clone())
+        }
+        HirItem::Expression(expression) => SourceRootId::Expression(
+            hir.expression_root(expression.occurrence()).ok().flatten()?.clone(),
+        ),
+        HirItem::Error { .. } => return None,
+    };
+    hir.local_source_for(&root).ok().flatten()
+}
+
 fn intern<'a>(
     nodes: &mut Vec<CandidateGraphNode<'a>>,
     node_indices: &mut HashMap<CandidateGraphNode<'a>, usize>,
@@ -203,10 +216,7 @@ pub(crate) fn intrusion_into(
         output.observe(1)?;
         let occurrence = event.checking.occurrence();
         let range = hir.items().iter().find_map(|item| {
-            let HirItem::Binding(binding) = item else {
-                return None;
-            };
-            let local = hir.local_source(binding.definition_root()).ok().flatten()?;
+            let local = local_source_for_item(hir, item)?;
             local
                 .expressions()
                 .iter()
@@ -286,10 +296,7 @@ fn source_value_into(
         }
         CandidateSourceValueIdentity::Local(id) => {
             let name = hir.items().iter().find_map(|item| {
-                let HirItem::Binding(binding) = item else {
-                    return None;
-                };
-                let local = hir.local_source(binding.definition_root()).ok().flatten()?;
+                let local = local_source_for_item(hir, item)?;
                 local
                     .bindings()
                     .iter()
diff --git a/tools/inference-playground/tests/cli.rs b/tools/inference-playground/tests/cli.rs
index e4a82f737..6b2fad9f5 100644
--- a/tools/inference-playground/tests/cli.rs
+++ b/tools/inference-playground/tests/cli.rs
@@ -381,6 +381,40 @@ fn intrusion_flag_observes_actual_source_associations() {
     );
 }
 
+#[test]
+fn intrusion_expression_calls_keep_original_spans_and_local_names() {
+    let cases = [
+        (
+            "id 1; my id x = x; my main = 7",
+            "id 1",
+            "module id",
+        ),
+        (
+            "{ my helper x = x; helper 1 }; my main = 7",
+            "helper 1",
+            "local helper",
+        ),
+    ];
+
+    for (source, call, expected_label) in cases {
+        let output = infer_with_intrusion(source, "expression-intrusion.yu", true).unwrap();
+        assert!(output.contains("Retained intrusion state (not a chronological trace)"));
+        assert!(output.contains("  event "), "retained event missing: {output}");
+        assert!(output.contains(expected_label), "source label missing: {output}");
+        assert!(!output.contains("source span unavailable"));
+
+        let start = source.find(call).unwrap();
+        let expected_location = format!(
+            "at retained call-tail occurrence {}\n",
+            location(source, &(start..start + call.len()))
+        );
+        assert!(
+            output.contains(&expected_location),
+            "original call-tail location missing: {expected_location:?}\n{output}"
+        );
+    }
+}
+
 #[test]
 fn conflicts_also_withhold_intrusion_observations() {
     let error = infer_with_intrusion(
```
