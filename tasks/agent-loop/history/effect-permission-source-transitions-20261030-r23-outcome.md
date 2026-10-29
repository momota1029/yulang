# R23 pre-ACCEPT review disposition

Sprint: `CALLBACK-SOURCE-TRANSITIONS/20261030-R23`

## Frozen revision reviewed

The independent compiler referee authenticated all supplied frozen hashes:

- `machine.rs`: `0116f875bc5df81f1321c4f13ca49e7745b67d02c52976fc216dabbfc7c7aab6`
- `receiving.rs`: `cfac5fcbc875f24172cc9027ace1169a2901614f25d1822f5f922e206ac7dd2e`
- `program.rs`: `6607c4371366739c0e593b29a5da96becbb0bd743b2618a3755653f1b0ac3907`
- `source-transitions.json`: `bc1bdb6f4c840c1cf2cc602adf8de5ccaf92d121a0c89b2c700fce54140303fb`
- Rust handoff revision 2: `a7ae2e7eed07e4c4c17fbbd5e705c996fa206fd62fd1851134dfb3729e090af1`

The approved callback bytes, companion source, hygiene source, Cargo manifests/lockfile and runtime `mod.rs` matched their governing pins. The owner-minted observation ordinal fixes the prior same-step ordering defect.

## Disposition: REJECT / STOP

No Cargo invocation is authorized. Runtime behavior remains unobserved. The read-only review found four blocking pre-Cargo defects in the isolated R23 project:

1. `machine.rs:1738,1773`: `observe_source_transition(...)?` appears inside `Option::and_then` closures; `?` cannot propagate the `Result` from closures returning `Option`.
2. `machine.rs:4259,4279`: invocation joins compare the entry's `usize` with `ExecutionOwner`; explicitly extract `ExecutionOwner::Invocation(id)` and reject `ModuleRun` before joining IDs.
3. `machine.rs:4198` onward: positive assertions do not include contract-required mutation rejection. Required identity swaps, missing records, invalid order and lost-write cases need to be rejected; changing the formal receipt while keeping it distinct from the Name receipt currently passes.
4. `machine.rs:4233,4246,4310,4318–4343`: substring-selected handler/request and unused callback arm identity do not authenticate the exact Catch arm. Companion checks omit the inner signal consumption and its connection to the retained write obligation. Structured source-owner coordinates and both companion events need exact joins.

The referee did not run builds/tests, Lean/Lake, checker, formatter or Git, and wrote no files. Its active elapsed time was not instrumented; the observed wall envelope from followup at 17:39:15 UTC to STOP observed at 17:40:47 UTC was at most 92 seconds of the <=500-second first-review cap.

The Rust author remains STOPPED; all exact leased source and handoff paths remain FROZEN. No Cargo, Rust test, Lean, Lake or checker ran. The remaining Rust grant is conservatively 554 seconds from the original 1,400-second cap; the original scope and semantics are unchanged. Parent theorem, source/native execution, effect hygiene, soundness, principality, termination and production gates remain OPEN.

Next action: consult the sprint selector on whether another in-scope correction fits the remaining exact lease and resource envelope.


## Correction session 2 stop

The same Rust identity was resumed under the selector's <=309-second same-lease correction envelope. It STOPPED at 2026-10-29 17:43:10 UTC without a revision; the worker reported active elapsed UNKNOWN and conservatively treated the cap as exceeded. No source or receipt changed: all five revision-2 hashes above still match. No process or descendant remains, and no compiler, Cargo, test, Lean/Lake, checker, formatter or Git command ran in the worker lane.

The primary charges the full 309-second correction cap, reducing the cumulative Rust remainder from 554 to 245 seconds. That remainder is exactly the preserved <=240-second post-ACCEPT Cargo reservation plus <=5-second handoff reserve. The pre-ACCEPT review is REJECT, so neither reservation is currently executable. No source-correction allowance remains in this R23 allocation.


## Closeout

**Disposition: CLOSED_INCOMPLETE — PREFLIGHT_REJECTED / CORRECTION_BUDGET_EXHAUSTED.** This closes only R23's provisional source-transition packet. No runtime trace, compiler counterexample or checked R23 theorem exists. The same-sprint Lean lane never started because Rust review prerequisites failed. Preserve the revision-2 candidate and all four review blockers as failure evidence only.

The selector authorized one same-lease correction capped at 309 seconds and explicitly barred Cargo until a later exact-hash ACCEPT. Correction session 2 stopped without a revision; the worker reported elapsed time UNKNOWN and conservatively over the cap. The primary charged the full 309 seconds, leaving 245 seconds of the original Rust grant, reserved as Cargo <=240 seconds plus handoff <=5 seconds. Preflight remains REJECT, so that reserve is unusable for R23 and cannot fund another correction. No renewed resources, paths, workers, semantics or production authority were granted.

The original parent theorem, source/native correspondence, effect hygiene, soundness, principality, termination and production gates remain OPEN. R23's isolated leased paths remain FROZEN; both Rust and referee identities are STOPPED. A successor repair specification may be prepared, but executing it requires a new explicit resource envelope and exact leases.
