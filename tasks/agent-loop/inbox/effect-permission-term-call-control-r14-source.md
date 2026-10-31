# R14 source handoff — `with_term_events` control flow

Sprint: `EFFECT-PERMISSION-TERM-CALL-CONTROL/20261029-r14`  
Authority: unchanged Simple-sub inference/executor research goal; R13 is conditionally closed. This source lane is read-only and does not authorize compiler semantics or production.

## Frozen source pins

- `crates/yu-solver/src/lib.rs`: `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`
- `crates/yu-solver/src/candidate_effect.rs`: `1f64d4fec8f2abceb11a48a51f5b615aa2cf605c9586ba742f15f9024a6a2717`
- `crates/yu-solver/src/term.rs`: hash recorded by the R14 admitted input manifest.
- R13 `FormalPermissionConnectedCuts.lean`: `6427eed5f0c3b84f80a3a37c31797fc782960c725fb77f6bef46cebcc993b023`
- R13 review: `fb1f43e3c486237b9f93d6955f4bf4cf96b5b3827a40c42044838e099734c394`; R12 helper operation model: `92531e0849a08a03a37bbb35315f01b831d31bdffb108712c5b0a4a7eaaa75dd`.

## Pinned control flow

`InferenceSession::with_term_events` is at `lib.rs:10594–10621`:

1. It calls the supplied `FnOnce(&mut BranchTermArena) -> Result<Term, ConstraintError>` with only `&mut self.store.terms`, retaining the result without returning early.
2. It unconditionally drains `self.store.terms.take_capacity_events()` after the constructor returns. The iterator preserves the recorded snapshot order.
3. For every drained snapshot, it checks `incoming_route_accounting_active`. If false, that snapshot causes no sampling operations. If true, it sets `route_attempt_physical_change = true`, then calls `sample_f4_resources_with_term_snapshot(snapshot)`.
4. If that sample returns an error, the helper sets `incoming_route_event_sample_failed = true` and immediately returns the sampling error. Later snapshots are not processed and the constructor result is not mapped.
5. Only after the complete event loop does it map the constructor result with `result.map_err(Into::into)`. Therefore a successful return requires a successful constructor result and successful sampling for every drained event. If construction failed but all samples succeeded, the mapped constructor error is returned; a sample failure takes precedence because it returns first.

`BranchTermArena::take_capacity_events` at `term.rs:955–958` takes the event buffer and yields its stored snapshots. Arena capacity event generation is tied to observed capacity changes: `record_capacity_change` takes a before snapshot, compares the selected lane's before/after capacity, and records a change event when they differ. Constructor internals and allocator failure behavior remain owned by `term.rs` and its reservation helpers.

`sample_f4_resources_with_term_snapshot` at `lib.rs:10804–10818` routes each event to `sample_f4_resources_with_term_override(ResourceBoundary::IncomingRoute, 0, Some(snapshot), None)`. This sampler has fallible accounting/resource work and can return `SolveAvailabilityError`; R14 must model only an explicit successful sample outcome for the successful-call theorem. It must keep early sample failure explicit and must not infer availability from the outcome input.

`incoming_route_accounting_active` is set true around `route_incoming`'s transactional body and set false immediately after it (`lib.rs:18969–18975`). This confirms the accounting flag is caller/session state, not derived inside `with_term_events`.

## Callers and model boundary

`candidate_effect.rs` calls `with_term_events` for function and tuple term construction, including `candidate_formal_value_pair`'s positive/negative function terms and tuple terms. The callback supplies the constructor and its arguments; R13 `TermCall.terms`/`.events` correspond to constructor output/event data, while the existing arbitrary `.handling` list is the exact control-flow freedom R14 should replace for the named helper.

A source-directed successful-call constructor may take explicit constructor outcome, ordered capacity snapshots, accounting flag and per-event successful sampler outcomes. For `incoming_route_accounting_active = false`, it should drain the event list but append no physical-change/sample sequence. For `true`, it should append one physical-change followed by one successful sampling segment per event in order. Empty events yield no sample segments. The transcript must preserve the existing `TermCall.ops` ordering: constructor, drain, then this generated handling sequence.

The source establishes this control-flow order only. The following remain explicit inputs or later obligations: actual `BranchTermArena` constructor result and snapshot sequence; exact sampler state delta and resource/capacity availability; actual Rust return values and `Calls`/path/state correspondence; term primitive/library alias behavior; all publication/native and original-parent gates. Test-only observers and snapshot counters are not production effects and should not be silently promoted to semantic fields.

## Exact scope and stop boundary

R14 proof may add `FormalPermissionTermCallControl.lean` and one proof handoff only. Reuse R12/R13 declarations unchanged. Prove a source-directed successful `TermCall` construction and its refinement/application to the R13 term-call cuts. Do not assume arbitrary `handling`, endpoint equalities, a successful constructor from opaque primitive input, successful sampler availability, or Rust execution correspondence. Stop if the source result cannot justify the selected transcript without such a premise.

This source handoff is read-only; no Rust, Lean, tests, Cargo, instrumentation, or compiler configuration was changed or run.
