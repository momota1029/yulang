Sprint-ID / contract revision and SHA-256: EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r15; contract hash is recorded in the R15 evidence after admission.
Assignment-ID / handoff revision: R15-source / rev1.
Parent gate / original theorem and scope: unchanged Simple-sub inference/executor goal; R14 `with_term_events` control model and all R12/R13 inherited roots.
Baseline / direct dependency hashes: R14 candidate artifact `fde5e86c3540646b778856dda985b51db201a20ab7a38ca3e34485257c2dbfdc`; R14 source handoff `744c3244b919758360c3e0f966278ebbc3881d2cd1120de19410e345340c65ce`; R14 failed audit receipt `19a8aacc9932ea3003103b71b5b728340bc3ed8b46bc4497aaa5e110a65bf86b`; pinned Rust sources unchanged.
Role / actual worker ID / current session / launch receipt: primary Luna read-only source audit; no child launched.
Requested/observed model and effort: UNKNOWN / UNKNOWN.
Exact leased paths: read-only `crates/yu-solver/src/lib.rs`, `crates/yu-solver/src/candidate_effect.rs`, `crates/yu-solver/src/term.rs`, the frozen R14 artifact and R14 failure output; write only this R15 handoff.
Outcome class: source handoff; proof repair remains the only authorized code/artifact change.

## Source observations

The pinned `Session::with_term_events` implementation in `crates/yu-solver/src/lib.rs` calls the supplied constructor with `&mut self.store.terms`, then unconditionally drains `self.store.terms.take_capacity_events()` into `events`. It walks these snapshots in order. When `incoming_route_accounting_active` is false, the loop drains them without sampling. When true, each event first sets `route_attempt_physical_change = true`; the `#[cfg(test)]` attempt observer may be incremented; then `sample_f4_resources_with_term_snapshot(snapshot)` runs. On its first error, the function sets `incoming_route_event_sample_failed = true` and returns immediately, so later snapshots are not sampled and the constructor result is not mapped. If all samples succeed (including the empty-event case), the original constructor result is returned through `result.map_err(Into::into)`. Thus a sample error wins over either constructor outcome; otherwise constructor error mapping is preserved.

The test-only snapshot/count writes occur only after each successful sample. The current R14 model uses `testFields` as instrumentation identities preserved by sample state; the frozen diagnostic arose in `control_test_fields`, not in a source ambiguity. The relevant existing lemma `loop_test_fields` already proves that the loop preserves those fields. In the true branch, `controlState` is `loopState events (drained constructor events s)`, so the proof can apply `loop_test_fields` at that intermediate state and then simplify the unconditional drain's instrumentation fields. This is a proof-only repair route; the theorem statement, state model, source transcription, and all semantics remain fixed.

## Exact boundary and exclusions

The primary Lean 4.35.0 Audit 1 failed before printing theorem or axiom roots at `FormalPermissionTermCallControl.lean:231:80`, the true branch of `control_test_fields`. The goal is proof construction, not a counterexample to `with_term_events`. This lane did not run Lean, Lake, Cargo, Rust tests, or modify source. It makes no claim that constructor event generation, sample availability, or Rust execution has been related to the explicit model inputs.

Source -> generated constraints -> propagation -> consumer/native path remains the existing R14/R13 open boundary. The exact permitted next step is to repair only `control_test_fields` using `loop_test_fields` without changing the declaration or control model. If that route requires a theorem/model change, stop and return the exact obstruction to Luna.

Writes stopped; no descendant leases.
