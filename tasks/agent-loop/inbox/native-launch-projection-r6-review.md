# NATIVE-LAUNCH-PROJECTION/r6 — independent review handoff

Verdict: **REJECT**. R6 closes incomplete under its review gate. The contract authorizes no conditional checks or revisions after rejection.

Reviewer: `/root/native_launch_projection_r6_review`, registered `compiler_referee`; requested Sol/medium, observed model/effort UNKNOWN. Review duration and CPU/RSS were not independently measured. Source bodies and governing contract were inspected before producer explanations. No files were edited by reviewer; this receipt was persisted by the primary from the returned review.

## Blocking findings

1. **Replacement helper is statically ill-typed.** In `isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_extrusion.rs:753`, the helper passes `item: ExtrusionEndpoint` to `std::mem::replace` on vector elements whose concrete types are `u32`, `ValueEndpointKey`, or `EffectEndpointKey`. Line 754 puts the unwrapped old element into `BoundKey`'s `ExtrusionEndpoint` field. Actual storage declarations are in the pinned snapshot `lib.rs:4194–4197` and `4216–4219`. All eight macro expansions are affected. No compiler ran. Any future packet needs lane-specific unwrapping/reconstruction and focused compilation.

2. **Removal helper returns the wrong endpoint type.** At `candidate_extrusion.rs:787`, `BoundKey` receives `$wrap(item)`. Row arms wrap only into `ValueEndpointKey`/`EffectEndpointKey`; atom arms return those inner types directly. None supplies the required outer `ExtrusionEndpoint::Value` or `::Effect`. This independently prevents the test build. A future packet needs correct reconstruction for all eight lanes and focused compilation.

## Major proof finding

3. **The resource model omits exact native error prefixes.** `NativeLaunchProjectionR6.lean:199` samples `s.undoCapacity`, modeling replay-operation undo capacity. Actual `lib.rs:10782` samples `route_journal.value_rows.capacity()`; these are different owners with potentially different capacities. Under `f5c_resource_probe`, `lib.rs:11431–11444` can panic after ledger/counter/sample publication but before the completed-sample trace at `10993`. `sampleWrites`/`sampleExit` model prepublication panic or later matrix panic, omitting this intermediate prefix. The projection calculations are abstract candidates, not exact source callback correspondence. Closure needs separate owner state and the publication-prefix panic case, followed by source correspondence review.

## Minor record finding

4. `current.json` amendment lease SHA is `0db2b4f8…`; actual frozen amendment bytes and both producer acknowledgements use `77033272…`. Correct this through primary record synchronization.

## Accepted bounded source observations and proof boundary

The observer addresses R5's stale-readback and unused-handle causes: actual begin/return sites record invocation plus handle; completed authentication joins those records and rereads the physical row/lane through `candidate_physical_slot_bound`. The ordinary module freshening path reaches the driver. The raw-transformer mutation restores the moved original before asserting rejection. These are source observations only; fixture success remains untested.

The Lean artifact has seven candidate theorem terms and imports only `Init`. It has no composed `runPrefix` or Idle/Some-to-Running theorem. Its first unmodeled **launch owner** is `clear_diagnostic_scratch` (`lib.rs:15934`, called at `14196`); exact resource realization is already open earlier. No theorem was kernel-checked or transitively axiom-audited. Original soundness/native quantifiers, immutable-birth qualification, effect policy, shared witness, and all parent/production gates remain open.

## Authenticated frozen outputs

```text
contract 01236acb3ef9134788e58aa888ec7d498ddd24fa9f64250c4f1fc2837f03034a
amendment 770332723483bb646936c71eb4bf7e83e9dfaf5ee6cf9898ff0bbefe98ff5296
candidate_scheme.rs c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d
candidate_context.rs 19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec
candidate_extrusion.rs e532e7228487e125a73576cb76b8bf17c065862b049bd8d6f8fa185bb77c54af
NativeLaunchProjectionR6.lean eb4c5c99fee13689b4c7ee4b9cf7668ec39416e3259ed826c44204c78fc7ea13
Rust handoff ab4fc227328d2ad8e9081d3379778f5d99f10177462e4df616a9d8ba776b694d
Proof handoff 2a4cb3c9e0af0fa354ce89b6b8305d9ff54f55889407f9001d1018bad4bdc4c4
Astra handoff c8ca2b528fcaf4b62c578535cfbe570db92dfa47cae5d1c025c0fd4b0072482d
```

Contract, amendment, immutable proof inputs, and all intended snapshot Rust pins matched.

## Review deviation and stop

One hash-only authentication script initially resolved nine dependency paths against root files. It interpreted no root source body and made no writes. Explicit isolated-path authentication was then repeated successfully; the mistaken root hashes were discarded. This deviation is retained, not waived.

No Git, build, Cargo, tests, Lean/Lake, formatter, descendants, or executable verification ran. Review and producer writes are stopped. The primary must synchronize current state and close R6 incomplete; no conditional checks may follow this rejection.
