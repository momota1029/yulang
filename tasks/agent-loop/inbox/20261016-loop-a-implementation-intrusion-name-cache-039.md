# I28 intrusion renderer borrowed name-cache receipt

- Request: `20261016-loop-a-implementation-intrusion-name-cache-039`
- Revision: 1
- Baseline HEAD: `ca261b572c743f2fb6225a929c19210190b60ae8`
- Requested/configured implementer: Luna/high
- Observed runtime model/effort: UNKNOWN
- Authority: approved source-owner rendering contract, existing identity and
  fallback behavior, and efficiency principle §2.
- Claim: private per-render lookup reuse only. No formatting, API, source
  identity, solver/runtime, or test-contract change; no measured-speed claim.

## Frozen nine-pin manifest

All nine input pins matched at launch and freeze:

| Input | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/render.rs` | `94f45c15f49dc460e006856604f9309bdf73e3fe41347579d694c004615c0f16` |
| `tools/inference-playground/tests/cli.rs` | `cf265feba7414b159353c81751608e9c127b072559b2c8c4cc513ecbc15c22ea` |
| `crates/yu-solver/src/shadow_apply.rs` | `bb1e63c2ea33bf0b6e7408bd015d2498a9aed4dd45e250a85433169c9da334bf` |
| `crates/yu-hir/src/module.rs` | `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e` |
| `crates/yu-hir/src/module/local_source.rs` | `ede8b845e1ad19bb1481d7e6337cefa1f117197512975f0f306dc6edb79672e5` |
| `tools/inference-playground/src/output.rs` | `04e99c5bdb562a8edb8a7e17bdcc03f7b46eaca9d8e13b20216b4dcf3032a88a` |
| `tools/inference-playground/src/lib.rs` | `b65cfd7200e459c9448438ec979ffeb9eddb35c282600349cebe7ddf3b759bbb` |
| `notes/design/2026-10-16-module-expression-source-owner.md` | `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81` |

## Implementation and cost

`intrusion_into` now keeps separate per-render `HashMap<&DefId, &str>` and
`HashMap<&HirLocalId, &str>` caches. Each successful resolution stores the full
typed ID borrowed from the immutable HIR and its borrowed source name. Lookup is
lazy at the same two `source_value_into` call sites. The original first-match
scan runs on cache misses, only successful matches are inserted, and misses
continue to use the original fallback on every occurrence. No ID or name is
cloned; no eager pass or map iteration was added. Parameter, CatchBinder and
Expression labels, range indexing, formatting, event order, charges, errors and
caps remain unchanged.

For K charged events, at most D≤2K≤32,768 successful distinct IDs are cached.
Storage is O(D); typed-ID hashing/equality/collision work and ordinary map
allocation remain exposed. Misses remain uncached, and the other source and
excerpt scans remain. No whole-renderer linearity, resource-equivalence or
measured-speed claim is made.

## Exact verification

The three assigned commands ran serially:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_expression_calls_keep_original_spans_and_local_names -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 22 filtered out`.

2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli intrusion_flag_observes_actual_source_associations -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 22 filtered out`.

3. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test cli aggregate_output_limit_withholds_all_cli_output -- --exact --test-threads=1`

   Result: exit 0; `1 passed; 0 failed; 0 ignored; 0 measured; 22 filtered out`.

No warning, timeout, identity/fallback/cap mismatch, dependency change, extra
check, or benchmark was observed. Benchmark budget was 0 processes / 0 samples.

## Complete literal baseline diff

```diff
diff --git a/tools/inference-playground/src/render.rs b/tools/inference-playground/src/render.rs
index a4ceeda04..b0daf2853 100644
--- a/tools/inference-playground/src/render.rs
+++ b/tools/inference-playground/src/render.rs
@@ -1,7 +1,7 @@
 //! Finite observations of the existing private candidate graph.
 use std::collections::HashMap;
 use std::fmt::Write;
-use yu_hir::{HirItem, HirModule, LocalSource, SourceRootId};
+use yu_hir::{DefId, HirItem, HirLocalId, HirModule, LocalSource, SourceRootId};
 use yu_solver::shadow_apply::{CandidateGraphExport, CandidateGraphNode, CandidateGraphRow};
 use yu_solver::shadow_apply::{CandidateInference, CandidateSourceValueIdentity};
 
@@ -213,6 +213,8 @@ pub(crate) fn intrusion_into(
     )
     .map_err(cap)?;
     let mut conflict_ranges = None;
+    let mut module_names: HashMap<&DefId, &str> = HashMap::new();
+    let mut local_names: HashMap<&HirLocalId, &str> = HashMap::new();
     for event in observation.events() {
         output.observe(1)?;
         let occurrence = event.checking.occurrence();
@@ -232,14 +234,26 @@ pub(crate) fn intrusion_into(
             event.ordinal, event.origin.ordinal
         )
         .map_err(cap)?;
-        source_value_into(hir, event.origin.identity, output)?;
+        source_value_into(
+            hir,
+            event.origin.identity,
+            &mut module_names,
+            &mut local_names,
+            output,
+        )?;
         write!(
             output,
             ", SCC {}), receiver=v{} (",
             event.origin.component, event.receiver.ordinal
         )
         .map_err(cap)?;
-        source_value_into(hir, event.receiver.identity, output)?;
+        source_value_into(
+            hir,
+            event.receiver.identity,
+            &mut module_names,
+            &mut local_names,
+            output,
+        )?;
         write!(
             output,
             ", SCC {}), same_scc={} at retained call-tail occurrence ",
@@ -280,17 +294,31 @@ pub(crate) fn intrusion_into(
     Ok(())
 }
 
-fn source_value_into(
-    hir: &HirModule,
+fn source_value_into<'hir>(
+    hir: &'hir HirModule,
     identity: CandidateSourceValueIdentity<'_>,
+    module_names: &mut HashMap<&'hir DefId, &'hir str>,
+    local_names: &mut HashMap<&'hir HirLocalId, &'hir str>,
     output: &mut Output,
 ) -> Result<(), String> {
     match identity {
         CandidateSourceValueIdentity::Module(id) => {
-            let name = hir.items().iter().find_map(|item| match item {
-                HirItem::Binding(binding) if binding.id() == id => Some(binding.name().spelling()),
-                _ => None,
-            });
+            let name = if let Some(name) = module_names.get(&id) {
+                Some(*name)
+            } else {
+                let found = hir.items().iter().find_map(|item| match item {
+                    HirItem::Binding(binding) if binding.id() == id => {
+                        Some((binding.id(), binding.name().spelling()))
+                    }
+                    _ => None,
+                });
+                if let Some((key, name)) = found {
+                    module_names.insert(key, name);
+                    Some(name)
+                } else {
+                    None
+                }
+            };
             if let Some(name) = name {
                 write!(output, "module {name}").map_err(cap)
@@ -298,14 +326,24 @@ fn source_value_into(
         }
         CandidateSourceValueIdentity::Local(id) => {
-            let name = hir.items().iter().find_map(|item| {
-                let local = local_source_for_item(hir, item)?;
-                local
-                    .bindings()
-                    .iter()
-                    .find(|binding| &binding.id == id)
-                    .map(|binding| &*binding.spelling)
-            });
+            let name = if let Some(name) = local_names.get(&id) {
+                Some(*name)
+            } else {
+                let found = hir.items().iter().find_map(|item| {
+                    let local = local_source_for_item(hir, item)?;
+                    local
+                        .bindings()
+                        .iter()
+                        .find(|binding| &binding.id == id)
+                        .map(|binding| (&binding.id, &*binding.spelling))
+                });
+                if let Some((key, name)) = found {
+                    local_names.insert(key, name);
+                    Some(name)
+                } else {
+                    None
+                }
+            };
             if let Some(name) = name {
                 write!(output, "local {name}").map_err(cap)
```

## Frozen output hash and remaining scope

- `tools/inference-playground/src/render.rs` SHA-256:
  `86dba831366995d4c36e2446c9b8e6847f7bff524d5e7e7b6d12d02ff337fc66`
- This receipt SHA-256: recorded by the primary after freeze.

The artifact remains an internal renderer optimization. It is not evidence of
compiler inference correctness or a broader performance result.
