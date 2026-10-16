Request-ID: 20261016-loop-a-implementation-expression-intrusion-repair-026-result
Revision: 1
From: implementer; actual worker ID unknown
To: next_action_selector
Parent-gate: I18 executable packet, `tasks/agent-loop/board.md` §I18; approved diagnostic/source-ownership scope in `notes/design/2026-10-16-module-expression-source-owner.md`
Baseline: `e7324e89d93546f648540fb88976b4aeee00ef48`; exact test baseline `tools/inference-playground/tests/cli.rs` SHA-256 `ab36ed6ea71c9db18edfdf55ce168d425a7663f1cc310c712feb2cd65a4d714b`; renderer frozen from I18 at SHA-256 `ccd8f6551c49cc5fe937258c9dcd03ae7d441e8932e8fb9480515f1b587093bf`; prior frozen result `tasks/agent-loop/inbox/20261016-loop-a-implementation-expression-intrusion-locations-025.md` SHA-256 `7f184a89644a56a56cbe3438497fac4d3f949a120d7951b9171240868abb0244`
Kind: implementation
Claim/task: Correct the new bounded CLI regression to match the native call-tail occurrence: it points to the final literal argument `1`, rather than the whole application text. Require the retained expression-origin label, fixture-specific receiver source label, exact source-derived location/excerpt, and absence of unavailable spans for both approved pure fixtures.
Missing-evidence: None for this bounded renderer diagnostic regression after both assigned commands passed. This does not establish whole-source adequacy, inference soundness, principality, or production readiness.
Owners: test `tools/inference-playground/tests/cli.rs::intrusion_expression_calls_keep_original_spans_and_local_names`; renderer owner was frozen/read-only `tools/inference-playground/src/render.rs::local_source_for_item`, `intrusion_into`, `source_value_into`.
Depends-on: I18 renderer implementation in frozen inbox025; its renderer bytes remained unchanged.
Scope: Test-only correction. Keep both fixtures exactly as approved. Assert `origin=v` and `(expression value, SCC `, receiver labels `module id` / `local helper`, retained event output, exact final-argument location plus original full-line excerpt, and no `source span unavailable`. Do not change renderer/native code, semantics, preflight, fixture meaning, or prior assertions.
Acceptance: Both assigned exact focused commands pass, one test each. The expression fixture and existing binding/nested-recursion compatibility control pass. Parent proof and production gates remain OPEN/BLOCKED; no proof is claimed from tests.
Proposed-outputs: `tools/inference-playground/tests/cli.rs` and this leased receipt only.
Checks/resources: Requested implementer settings Luna/high minimum; observed settings unavailable. Exactly two Cargo commands ran, serialized, jobs=2, test threads=1, each under its 180s timeout:
1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_expression_calls_keep_original_spans_and_local_names -- --exact --test-threads=1` — exit 0; 1 passed, 0 failed, 22 filtered; finished in 0.03s after compilation (3.40s reported build/test-profile duration).
2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_flag_observes_actual_source_associations -- --exact --test-threads=1` — exit 0; 1 passed, 0 failed, 22 filtered; finished in 0.11s.
`git diff --check -- tools/inference-playground/tests/cli.rs` passed. Pre/post dependency SHA checks matched: lib.rs `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb`; yu-hir/module.rs `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`; approved design `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`; shadow_apply.rs `3fb9335e94ded08ec800d3d4dd9ce6097bc74e3b2966dc70c0b34aadd4c547f7`.
Prior-work: Reused the authentic lookup precedent `tools/inference-playground/src/lib.rs::conflict_ranges_for` and the renderer's frozen source-owner implementation from I18. Adapted only the new regression's call-tail range expectation and added explicit origin-label requirements; no old tests or assertions changed. I18-R0 receipt025 recorded the first attempted test's mistaken whole-call range and exact actual first-fixture observation. No withdrawn Simple-sub bypass or superseded inference construction was used.
Priority-reason: This closes the executable regression portion of I18's approved diagnostic lookup slice and verifies that binding-only rendering remains compatible. It does not close any theorem or production gate.
Stop/escalate: No failure or unsupported fixture occurred. No escalation requested. Stop this lease after freezing and hand it to Luna/dispatcher for review; do not edit renderer or other owners.

Frozen artifact snapshot:
- `tools/inference-playground/tests/cli.rs` SHA-256 `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea`
- `tools/inference-playground/src/render.rs` unchanged at SHA-256 `ccd8f6551c49cc5fe937258c9dcd03ae7d441e8932e8fb9480515f1b587093bf`
- Prior inbox025 unchanged at SHA-256 `7f184a89644a56a56cbe3438497fac4d3f949a120d7951b9171240868abb0244`
- First fixture's tail range is bytes `3..4`, line 1 column 4, excerpt `id 1; my id x = x; my main = 7`. Second fixture's tail range is bytes `26..27`, line 1 column 27, excerpt `{ my helper x = x; helper 1 }; my main = 7`. The passing test asserts each source-derived location.
- Exact unified test diff:
```diff
diff --git a/tools/inference-playground/tests/cli.rs b/tools/inference-playground/tests/cli.rs
index e4a82f737..45fa19313 100644
--- a/tools/inference-playground/tests/cli.rs
+++ b/tools/inference-playground/tests/cli.rs
@@ -381,6 +381,48 @@ fn intrusion_flag_observes_actual_source_associations() {
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
+        assert!(output.contains("origin=v"), "expression origin missing: {output}");
+        assert!(
+            output.contains("(expression value, SCC "),
+            "expression-origin label missing: {output}"
+        );
+        assert!(
+            output.contains(expected_label),
+            "receiver source label missing: {output}"
+        );
+        assert!(!output.contains("source span unavailable"));
+
+        let start = source.find(call).unwrap();
+        let expected_location = format!(
+            "at retained call-tail occurrence {}\n",
+            location(source, &(start + call.len() - 1..start + call.len()))
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

Unrelated pre-existing paths observed and left untouched: board edit; pending question draft; inboxes `...budgeted-runtime-007.md`, `...definition-index-009.md`, `...expression-freshuse-006.md`, `...expression-intrusion-locations-025.md`, and `...source-schedule-008.md`.
