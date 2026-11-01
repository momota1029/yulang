# R134 source candidate reconstruction — revision 1

Sprint / contract: `R134`, `tasks/agent-loop/sprints/effect-permission-causal-observation-20261102-r134.md`, SHA-256 `3f0c46ccdf98c5999ade532cea73f07dca0d755ce4307f350375166c2a99a321`.
Admission: `tasks/agent-loop/history/effect-permission-causal-observation-20261102-r134-admission.md`, SHA-256 `4b71d593042b2ae837af9e300502e4bb9f314451f789f7121c9ab194e116d22b`.
Assignment: R134 exact two-file source reconstruction; this is revision 1 of the sole leased handoff.
Parent gate: original Simple-sub A/B and effect-hygiene/source-preservation obligations; no theorem or production gate closes here.

## Runtime, role, lease and disposition

- Requested model/effort: `gpt-6-luna` / `high`. Observed model/effort: `UNKNOWN` in available runtime evidence.
- Worker: `/root/r134_causal_observation_source`; session `R134`; launch/active-work receipt: current-state row says `RUNNING`, spawn returned this identity; no separate launch token available to this worker.
- Exact write lease: this handoff only. Source paths were read only; no source writes or staging.
- No descendants. No compiler, Cargo, tests, Lean, checker, scratch, storage or environment probe was used. No Git mutation.
- Outcome class: provisional source-native observation instrumentation. This is a reconstructed candidate awaiting fresh independent review; no integration or commit-ready status claimed.

## Candidate hashes, byte counts and dependency pins

All base bytes are committed at `0961390608a6aadad6add22be38323709ed1a570`.

| Path | Base bytes / SHA-256 | Candidate bytes / SHA-256 | Unified diff lines (+/−) |
|---|---|---|---:|
| `crates/yu-solver/src/lib.rs` | 1,660,798 / `6eb6b5df29bda1d1bd1fecabcbc2cc6e85e777dda2045f1d1ab86084f64cd84f` | 1,662,249 / `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` | 28 / 5 |
| `crates/yu-solver/src/candidate_source.rs` | 212,009 / `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` | 212,732 / `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` | 12 / 0 |

Only direct recorder dependency: committed `crates/yu-solver/src/candidate_effect.rs`, SHA-256 `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`. Its recorder is `#[cfg(test)]`; `formal_live_capture_trace_event` calls the observation closure only when the thread-local trace contains `Some(events)`. No added dependency outside this pinned file is required by these hunks. This is a static dependency observation, not compiler evidence.

## Complete reconstructed unified patches

```diff
diff --git a/crates/yu-solver/src/lib.rs b/crates/yu-solver/src/lib.rs
index d9f2833a5..7ce2a3d59 100644
--- a/crates/yu-solver/src/lib.rs
+++ b/crates/yu-solver/src/lib.rs
@@ -13809,7 +13809,17 @@ impl InferenceSession {
         occurrence: &ConstraintOccurrenceId,
         cause: &CauseId,
     ) -> Result<usize, SolveAvailabilityError> {
-        self.constrain_live(LiveConstraintTask::Effect(lower, upper), occurrence, cause)
+        #[cfg(all(test, feature = "shadow-apply-candidate"))]
+        candidate_effect::formal_live_capture_trace_event(|| format!(
+            "live-effect-constraint before lower={lower:?} upper={upper:?} occurrence={occurrence:?} cause={cause:?} errors={}", self.errors.len()
+        ));
+        let result = self.constrain_live(LiveConstraintTask::Effect(lower, upper), occurrence, cause);
+        #[cfg(all(test, feature = "shadow-apply-candidate"))]
+        candidate_effect::formal_live_capture_trace_event(|| format!(
+            "live-effect-constraint after lower={lower:?} upper={upper:?} occurrence={occurrence:?} cause={cause:?} result={result:?} errors={:?}",
+            self.errors.iter().map(|error| (error.occurrence().clone(), error.cause().clone(), error.kind())).collect::<Vec<_>>()
+        ));
+        result
     }
 
     fn apply_effect_task(
@@ -13819,7 +13829,16 @@ impl InferenceSession {
     ) -> Result<(), SolveAvailabilityError> {
         #[cfg(feature = "shadow-apply-candidate")]
         if self.candidate_graph.is_some() {
-            return self.candidate_apply_effect(lower, upper);
+            #[cfg(test)]
+            candidate_effect::formal_live_capture_trace_event(|| format!(
+                "effect-propagation before lower={lower:?} upper={upper:?}"
+            ));
+            let result = self.candidate_apply_effect(lower, upper);
+            #[cfg(test)]
+            candidate_effect::formal_live_capture_trace_event(|| format!(
+                "effect-propagation after lower={lower:?} upper={upper:?} result={result:?}"
+            ));
+            return result;
         }
         match (lower, upper) {
             (EffectEndpointKey::EffectRow(a), EffectEndpointKey::EffectRow(b)) => {
@@ -16652,6 +16671,10 @@ impl InferenceSession {
                 cause: cause.clone(),
                 kind,
             });
+            #[cfg(all(test, feature = "shadow-apply-candidate"))]
+            candidate_effect::formal_live_capture_trace_event(|| format!(
+                "diagnostic-add occurrence={occurrence:?} cause={cause:?} kind={kind:?} index={}", self.errors.len() - 1
+            ));
             #[cfg(all(test, feature = "f5c_resource_probe"))]
             self.observe_f5c_structured_pair_top(
                 19, self.errors.len(), self.errors.capacity(),
diff --git a/crates/yu-solver/src/candidate_source.rs b/crates/yu-solver/src/candidate_source.rs
index 16f30e032..b43f37f4c 100644
--- a/crates/yu-solver/src/candidate_source.rs
+++ b/crates/yu-solver/src/candidate_source.rs
@@ -2450,7 +2450,19 @@ impl InferenceSession {
             }
             _ => {},
         }
+        #[cfg(test)]
+        candidate_effect::formal_live_capture_trace_event(|| format!(
+            "source-action before schedule={:?} index={} action={action:?} errors={:?}",
+            frame.schedule, frame.next,
+            self.errors.iter().map(|error| (error.occurrence().clone(), error.cause().clone(), error.kind())).collect::<Vec<_>>()
+        ));
         self.execute_candidate_action(&action)?;
+        #[cfg(test)]
+        candidate_effect::formal_live_capture_trace_event(|| format!(
+            "source-action after schedule={:?} index={} action={action:?} errors={:?}",
+            frame.schedule, frame.next,
+            self.errors.iter().map(|error| (error.occurrence().clone(), error.cause().clone(), error.kind())).collect::<Vec<_>>()
+        ));
         self.candidate_graph.as_mut().unwrap().source.as_mut().unwrap().next += 1;
         Ok(CandidateRun::Complete(false))
```

## Scope, cfg and source/native evidence

The source-action trace records schedule/index/action plus error occurrence/cause/kind before execution and after successful return. Because `execute_candidate_action(&action)?` precedes the after event, error returns have no paired after row. The live-effect wrapper records the same lower/upper endpoints, occurrence, cause, error count/list and returned `Result`, then returns that original result. Candidate propagation records before/returned result on the candidate-graph feature branch and returns the unchanged result. Diagnostic insertion is logged after the existing push with occurrence/cause/kind and inserted index; existing payload construction is unchanged.

Cfg coverage from the exact hunks and pinned recorder: non-test builds compile out every new observation. Test builds without `shadow-apply-candidate` retain only the source-action trace; the live-constraint and diagnostic trace sites are absent and the propagation branch is absent. Test builds with `shadow-apply-candidate` include the full live-effect, candidate propagation and diagnostic trace sites. Recorder availability is `cfg(test)`, matching each call site. When recording is disabled (`None`), the recorder does not invoke the `FnOnce` closure, so formatting and observation reads are skipped. These are source inspections only; cfg combinations, borrow behavior and compilation remain for the independent referee.

No source constructor is changed. The candidate instruments the existing source-action -> live effect-constraint -> candidate effect propagation -> diagnostic boundaries; it does not show source/native correspondence, establish that an expected edge should exist, repair a parent failure, or change solver semantics. Existing diagnostics and protected expectations are not edited. No withdrawn Simple-sub bypass is included.

## Prior evidence reused and rejected

Reused R104's frozen candidate hashes and outcome in `tasks/agent-loop/history/effect-permission-source-causality-20261101-r104-outcome.md`: its 47 passed / 4 failed / 2 ignored protected test result and four unresolved protected failures remain contrary evidence to closure. Reused R104's finding that logs/tests did not authorize source promotion. Reused R113's classification that current `candidate_source.rs` action logging is test-only instrumentation and does not itself establish propagation or execution correspondence. The R134 contract narrows this packet to its exact two target files and the pinned recorder dependency.

Rejected as proof or implementation authorization: passing subsets or instrumentation output; any claim that a failed source action always has a paired after row; treating source trace as theorem, semantic approval, parent closure or production evidence; restoring any withdrawn Simple-sub bypass; broadening to unpinned dependencies.

## Checks, limits and handoff

Checks performed: scoped path-specific diff reconstruction against the pinned baseline; direct target SHA-256 and byte-count reads; committed recorder hash and bounded recorder implementation read. No tests or builds were run by contract. The exact diff and target hashes match the contract. No semantic or diagnostic expectation was changed. Independent review remains mandatory for all cfg combinations, recorder availability, borrows, return values, call counts, early returns and accidental extra behavior.

Provisional boundary: test-only source-evidence instrumentation, not cutover. Falsifiers include a before/after event with mismatched schedule/index/action, altered or missing error payload, or an observation closure evaluating while recording is disabled. Cleanup owner: Luna after independent review/adjudication; tests do not authorize removal or promotion.

Mutual TODOs: none newly submitted; no parent premise is adjudicated by this source reconstruction. Remaining R104 protected failures, source/native correspondence, original A/B and effect-hygiene/production obligations stay open under their existing owners.

Exact files read for working diffs: only the two leased targets. Immutable dependency read: only pinned `candidate_effect.rs`, plus admitted contract/admission and relevant R104/R113 handoffs for prior evidence. New repository path: this handoff. Generated/scratch paths: none. Writes stop at this frozen revision. No live independent reviewer receipt is included; Luna owns review and any next authority decision.

Next related step within envelope: fresh independent static compiler-referee review of this frozen handoff and the exact two candidate hashes. No execution or integration is authorized by this handoff.

Worker state: STOPPED_WRITING; no descendants or generated outputs. Frozen revision hash is reported with submission.
