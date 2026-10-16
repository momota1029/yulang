# I21 implementation result — intrusion event range lookup

Packet: I21, dispatcher-selected implementation slice
Revision: 1 (frozen)
Baseline: `805374d4df1bcc229509b64d1fabaafb2163270c`
Requested role/model: resident implementer, Luna/high minimum
Observed runtime model/effort: UNKNOWN (runtime metadata unavailable)

## Authority and scope

Authority: top-level inference principles §2 and the approved authentic module-expression source owners. This is only an optimization in `intrusion_into`'s existing range lookup. It does not change solver/runtime/source semantics, public helpers, event order, output format, excerpts, fallback/withholding, or observation charges.

The source-owner note path supplied in the packet had a pluralization typo. The actual file is `notes/design/2026-10-16-module-expression-source-owner.md`; its SHA-256 exactly matches the supplied design pin. No design-content mismatch was found.

## Earlier evidence reused / adapted / rejected

- Reused I14's `conflict_ranges_for` helper, introduced in commit `3d5144e00e3f149f3e4ca4295477389f04be0235` (message: `perf: index playground conflict source ranges`). It accepts borrowed authentic occurrence keys and returns borrowed `Option<&Range<usize>>` values after indexing retained local-source expressions. Its existing callers bound requested keys with `take(WORK_CAP)` before mapping; its tests cover authentic roots, missing/foreign occurrences, duplicate keys, and strict prefix consumption.
- Reused I18's authentic direct-expression ownership change in commit `8efe58aee42962ce8eaaed84648d094ece9917fe` (message: `fix: render expression-owned intrusion locations`), which routes HIR expression items through the authentic `ExpressionRootId` and `local_source_for_item` helper.
- Adapted the borrowed range index only at the intrusion event renderer. The map is lazily constructed after the first successful `output.observe(1)?`, over `observation.events().take(WORK_CAP).map(|event| event.checking.occurrence())`; each current occurrence then uses the borrowed lookup result. The existing output-cap semantics keep the loop complete and charged event-by-event.
- Rejected further per-event rescanning of HIR carriers and cloning each `Range`; no solver graph/value index or source-owner construction was changed. I20/I20-R1 is a separate solver observation optimization and is not reused as an implementation mechanism here.

## Frozen implementation and exact baseline diff

Only `tools/inference-playground/src/render.rs` changed in production source. The full literal baseline diff is:

```diff
diff --git a/tools/inference-playground/src/render.rs b/tools/inference-playground/src/render.rs
index 1415e2880..a4ceeda04 100644
--- a/tools/inference-playground/src/render.rs
+++ b/tools/inference-playground/src/render.rs
@@ -212,17 +212,20 @@ pub(crate) fn intrusion_into(
         observation.pending_total()
     )
     .map_err(cap)?;
+    let mut conflict_ranges = None;
     for event in observation.events() {
         output.observe(1)?;
         let occurrence = event.checking.occurrence();
-        let range = hir.items().iter().find_map(|item| {
-            let local = local_source_for_item(hir, item)?;
-            local
-                .expressions()
-                .iter()
-                .find(|expression| &expression.occurrence == occurrence)
-                .map(|expression| expression.range.clone())
+        let conflict_ranges = conflict_ranges.get_or_insert_with(|| {
+            crate::conflict_ranges_for(
+                hir,
+                observation
+                    .events()
+                    .take(crate::output::WORK_CAP)
+                    .map(|event| event.checking.occurrence()),
+            )
         });
+        let range = conflict_ranges.get(occurrence).copied().flatten();
         write!(
             output,
             "  event {}: origin=v{} (",
@@ -244,7 +247,7 @@ pub(crate) fn intrusion_into(
         )
         .map_err(cap)?;
         if let Some(range) = range {
-            crate::location_into(source, &range, output)?;
+            crate::location_into(source, range, output)?;
         } else {
             output.write_str("source span unavailable").map_err(cap)?;
         }
```

The first action inside each event loop iteration remains `output.observe(1)?`. If there are no events, the optional map is never initialized. If the first charge fails, initialization and carrier scanning do not occur. Prefetch takes `WORK_CAP` events before mapping occurrence keys. No assertion expectations or tests were edited.

## Complexity and selected tradeoff

Let E be retained event count, K=min(E, WORK_CAP)=min(E, 16,384), T the retained source-owner/expression scan performed by the existing helper, and U≤K the number of distinct requested occurrence keys.

- After the first successful event charge, the helper may scan the bounded K-event prefix and authentic source carriers once, with expected cost O(K+T) plus existing identity/hash costs. The borrowed map stores O(U) keys/values; per-event lookup is expected O(1).
- Existing source-value/name lookup, formatting, excerpt construction, and non-intrusion renderer work remain unchanged. This does not establish whole-renderer linearity.
- The prefetch can scan up to K events even if remaining output work or byte capacity later allows fewer rows to render. Source scanning, hashing, and map allocation are not charged through `Output::observe`; this is the explicitly selected M2 tradeoff.
- The helper retains its existing infallible `HashMap` allocation behavior; no allocation-failure recovery guarantee is added.
- No benchmark was run (budget 0 processes / 0 samples); no speedup claim is made.

## Verification

Ran exactly the three assigned commands serially; each passed, exit 0, one test passed:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_expression_calls_keep_original_spans_and_local_names -- --exact --test-threads=1`
   - `1 passed; 0 failed`.
2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_flag_observes_actual_source_associations -- --exact --test-threads=1`
   - `1 passed; 0 failed`.
3. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli aggregate_output_limit_withholds_all_cli_output -- --exact --test-threads=1`
   - `1 passed; 0 failed`.

No other tests, builds, probes, benchmarks, or measurements were run. The cap test's existing CLI process behavior stayed within the packet's two-child budget. No Git operation was performed.

## Pinned inputs and frozen hashes

All supplied content pins matched at launch; the source-owner design note's corrected singular path matched the supplied hash.

- `tools/inference-playground/src/render.rs` baseline `ccd8f6551c49cc5fe937258c9dcd03ae7d441e8932e8fb9480515f1b587093bf`; frozen result SHA-256 `94f45c15f49dc460e006856604f9309bdf73e3fe41347579d694c004615c0f16`.
- `tools/inference-playground/src/lib.rs`: `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb`.
- `tools/inference-playground/src/output.rs`: `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a`.
- `tools/inference-playground/tests/cli.rs`: `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea`.
- `crates/yu-solver/src/shadow_apply.rs`: `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf`.
- `crates/yu-solver/src/candidate_value_graph.rs`: `8738c1b1699228b1a4dfd30af7e03d0afb100ca6124d23037c645246d888dc50`.
- `crates/yu-hir/src/module.rs`: `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`.
- `notes/design/2026-10-16-module-expression-source-owner.md`: `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- `tasks/agent-loop/inbox/20261016-loop-a-implementation-intrusion-range-index-030.md`: this frozen receipt SHA-256 to be recorded after writing.

## Gates and handoff

This packet changes no inference, source, or runtime semantics and closes no proof, source-adequacy, F5, or production gate. No new proof TODO was exposed by this bounded renderer optimization. No disposable files were created or identified for cleanup. Requested implementer setting was Luna/high; observed runtime model/effort is UNKNOWN. Suggested successor: assign the planned independent M2 review of the renderer diff and explicitly selected prefetch-before-later-cap tradeoff.
