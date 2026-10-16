# I24 implementation result — borrowed runtime Binder predicates

Request-ID: `20261016-loop-a-implementation-borrowed-runtime-binder-033`
Revision: 1 (frozen)
Baseline: `68ebe8e895fa9aad7524879377917508861d8367`
Requested role/model: implementer Luna/high
Observed runtime model/effort: UNKNOWN (runtime metadata unavailable)

## Authority and invariant

Authority: approved module-expression source-owner G4 runtime handoff, reviewed runtime-root correspondence §10 within its accepted scope, existing `Binder` full-ID equality and environment consumers, and top-level inference principles §2 efficiency. This is behavior-preserving private implementation maintenance; it adds no language, source-profile, materialization, or API rule.

`Binder` continues to compare the same full `HirParameterId`, `HirLocalId`, or `LocalSourceCatchBinderId`. `lookup` still checks the current frame before following `frame.parent?`, returns `Some(*cell)` for the nearest matching binder, and returns `None` when the environment chain ends or an environment index is absent. Name resolution retains the same MissingBinding path. `direct_formal_root` retains its instruction match, `.get`/None behavior, received-cell lookup, and computation interface check.

## Earlier implementation reused / adapted / rejected

- Adapted `lookup` as last revised in `9020651883f160a09f67e4d7afcd29494cfdc665` (“refactor: reuse program definition index in runtime machines”). Its existing environment-chain order and Option/cell behavior remain intact; the borrowed predicate replaces only temporary owned lookup keys.
- Reused the existing `Binder` enum and its derived full-identity `Eq`/`PartialEq` semantics in `tools/inference-playground/src/runtime/program.rs`. No equality implementation, storage, IDs, or public interface changed.
- Replaced temporary `id.clone()` key construction at exactly the three `LocalSourceResolution::{Parameter,Local,CatchBinder}` branches and the `direct_formal_root` Parameter lookup. The stored environment Binder clones at genuine binding/storage boundaries are unchanged.
- Rejected any change to namespace/shadowing, lookup order, direct-formal authorization, receiving interfaces, transitions, values, charging, or scheduling. No Box/dyn closure, collection, cache, or allocation policy was added.

## Exact frozen source diff

Only `tools/inference-playground/src/runtime/machine.rs` changed. Full literal baseline diff:

```diff
diff --git a/tools/inference-playground/src/runtime/machine.rs b/tools/inference-playground/src/runtime/machine.rs
index 729659983..5bbf8024c 100644
--- a/tools/inference-playground/src/runtime/machine.rs
+++ b/tools/inference-playground/src/runtime/machine.rs
@@ -450,13 +450,19 @@ impl Machine {
                         self.program.definition_indices.get(id).copied()
                     }
                     LocalSourceResolution::Parameter(id) => {
-                        self.lookup(environment, &Binder::Parameter(id.clone()))
+                        self.lookup(environment, |binder| {
+                            matches!(binder, Binder::Parameter(candidate) if candidate == id)
+                        })
                     }
                     LocalSourceResolution::Local(id) => {
-                        self.lookup(environment, &Binder::Local(id.clone()))
+                        self.lookup(environment, |binder| {
+                            matches!(binder, Binder::Local(candidate) if candidate == id)
+                        })
                     }
                     LocalSourceResolution::CatchBinder(id) => {
-                        self.lookup(environment, &Binder::Catch(id.clone()))
+                        self.lookup(environment, |binder| {
+                            matches!(binder, Binder::Catch(candidate) if candidate == id)
+                        })
                     }
                     LocalSourceResolution::Unresolved | LocalSourceResolution::Ambiguous => None,
                 }
@@ -1178,7 +1184,9 @@ impl Machine {
         else {
             return None;
         };
-        let cell = self.lookup(environment, &Binder::Parameter(parameter.clone()))?;
+        let cell = self.lookup(environment, |binder| {
+            matches!(binder, Binder::Parameter(candidate) if candidate == parameter)
+        })?;
         let received = self.cells.get(cell).copied().flatten()?;
         (received.interface == ParameterRole::Computation).then_some(received.view)
     }
@@ -1596,11 +1604,11 @@ impl Machine {
             _ => Err(RuntimeUnavailable::ExpectedComputation(site.clone())),
         }
     }
-    fn lookup(&self, mut environment: usize, binder: &Binder) -> Option<usize> {
+    fn lookup(&self, mut environment: usize, matches: impl Fn(&Binder) -> bool) -> Option<usize> {
         loop {
             let frame = self.environments.get(environment)?;
             if let Some((candidate, cell)) = &frame.binder {
-                if candidate == binder {
+                if matches(candidate) {
                     return Some(*cell);
                 }
             }
```

## Verification

Ran exactly the three assigned focused commands serially. All passed, exit 0, exactly one test discovered and passed each; no warnings were emitted:

1. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime returned_closure_retains_its_lexical_capture -- --exact --test-threads=1`
   - `1 passed; 0 failed; 0 ignored; 0 measured; 16 filtered out`.
2. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_receiving direct_formal_forwarding_preserves_the_received_root -- --exact --test-threads=1`
   - `1 passed; 0 failed; 0 ignored; 0 measured; 17 filtered out`.
3. `timeout 180s env CARGO_BUILD_JOBS=2 cargo test -p yu-playground --test runtime_module_expressions expression_owned_local_parameter_and_catch_schema_follow_real_invocation -- --exact --test-threads=1`
   - `1 passed; 0 failed; 0 ignored; 0 measured; 15 filtered out`.

No other tests, builds, probes, benchmarks, or measurements were run. No Git/index operation, shared-record write, delegation, or cleanup was performed.

## Pinned inputs and output hashes

All nine packet inputs matched at launch and the eight read-only inputs re-matched after checks:

- `tools/inference-playground/src/runtime/machine.rs` baseline `d9a8e14bd3eda8f5c40641beabac0ad862a4c04fc1173359934376681b731e77`; frozen output SHA-256 `910e583843d6afa1b06530cc52f83a59708fd3d22bdf384a16d03a99931078cc`.
- `tools/inference-playground/src/runtime/program.rs`: `b9798ac4c5d93e761582d712114615defa913f858d70e91f170471c8b8912748`.
- `tools/inference-playground/tests/runtime.rs`: `2a263b532a1db0fceafb2787e5783461b3a6684f5a7a74c45995943ec2060e90`.
- `tools/inference-playground/tests/runtime_receiving.rs`: `f82399766a012383f12e7190744c397ce10d11b9730241d6f724fa254c9d06bf`.
- `tools/inference-playground/tests/runtime_module_expressions.rs`: `f1693e49067f9bbfcd354ee3b87094cddef3736b324ca6c2551f70582368afa6`.
- `crates/yu-hir/src/module.rs`: `2e0c579a525efd5ac4c7ce0f06189c568ed46c7382d4576698a0b8d846c2228e`.
- `notes/design/2026-10-16-module-expression-source-owner.md`: `ab12b442f4f3d3d11565c89cda82c1cb25b17e943c2851b6bc937252410311e5`.
- `notes/theory/2026-10-16-runtime-module-expression-roots.md`: `915f99eb5cbd9734c3d1e4e0b778682bf1dbb3a8044ea21d5d77cee9d7250694`.
- `notes/design/2026-10-11-yulang-inference-top-level-principles.md`: `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- `tasks/agent-loop/inbox/20261016-loop-a-implementation-borrowed-runtime-binder-033.md`: this frozen receipt; final SHA-256 is reported separately to Luna.

## Static cost and limits

The change retains O(environment depth) traversal and the same full-ID comparison at each frame. The statically dispatched borrowed predicate avoids constructing/cloning a temporary owning `Binder`; it adds no persistent storage or heap allocation for the predicate. This is a local static claim only: there is no measured speed claim and no claim that the whole machine is allocation-free.

The three focused tests cover lexical closure capture, direct-formal forwarding with the receiving root, and expression-owned local/parameter/catch execution plus its nested-helper refusal control. Their passing results do not prove exhaustive runtime correctness, inference soundness, or source/profile adequacy. No pin/lease/owner mismatch or expanded lookup caller was found. Existing source admission, N1/F1-other/FK1, exact-U, A/B, F5, and production gates remain OPEN/BLOCKED.
