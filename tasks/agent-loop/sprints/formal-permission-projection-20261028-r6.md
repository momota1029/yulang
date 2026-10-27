# Sprint FORMAL-PERMISSION-PROJECTION-20261028/r6

Status: ADMITTED — one-owner production caller reachability for r2 B
Baseline: `3cc8a897fe08980576b1582952a95acab55f09d2`
Parent: unchanged full inference/executor soundness and original permission
endpoint-image obligation. Preserve source domain, accepted semantics, A/B
claims, quantifiers and source/native scope.

## Fixed outcome

Trace production formal-permission actions through source scheduling, route
transactions, candidate-state initialization/replacement, capture publication,
and the graph consumed by export. Determine whether each reachable originating
action uses the same graph and active undo begun before publication through its
matching commit/abort, or has a justified private lifetime whose failure cannot
publish inconsistent state.

Specifically:

1. Identify production (not test-only) reachability for `FormalAnnotation`,
   `RecordParameter`, `UnitParameter` and any sibling publisher needed for the
   first exact equation. Connect source-action dispatch to the admitted r5
   `State::begin` / publication / rollback evidence.
2. Establish whether route begin dominates each relevant publication, and
   whether candidate graph, journal or initialization can be replaced between
   begin, publication and disposition. Show which paths preserve a live
   originating association on commit.
3. Trace the abort exits including `lib.rs:9684` and `:9702` through their
   callers. Complete restoration is not required if the affected private
   attempt terminates or its partial state and captures cannot produce accepted
   typing or an exported result.
4. Trace capture publication/escape and identify the graph/root used by
   successful export. Keep original endpoint-image and occurrence/path identity
   intact. No actual counterexample is established without a reachable
   originating construction, surviving mismatched association, successful
   capture/export, and endpoint outside the original captured image.

A local checkpoint equation, missing active undo, offset reuse, rollback error,
retained graph or missing-root unavailability alone is insufficient. Keep r2 B
OPEN until caller reachability, identity and escape are established. Keep r2 C
(canonicalization/store association) and D (successful capture/export) separate.
Keep r1 Lean verification, all parent A/B, native correspondence and
production gates OPEN. If another owner is required, name the exact path and
equation and stop without opening it.

## Authority, source pins and output

Primary owns authority, this contract, current state, adjudication, review and
Git. One read-only `researcher` may inspect only this owner union:

| Owner | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `96be2c8e3270870bfd7c0f76827b50e8ce381139cd33796980375a79004b8b4a` |
| `crates/yu-solver/src/candidate_intrusion.rs` | `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97` |
| `crates/yu-solver/src/candidate_effect.rs` | `70c42056a1041d54f88f16d7712875e3acf9ef7649b99a34bc990ff19f04936f` |
| `crates/yu-solver/src/candidate_scheme.rs` | `02349de1a2d69289eb348f7ff807a9e36faa2e2028cf61d10c1af9cd364409c5` |
| `crates/yu-solver/src/shadow_apply.rs` | `f8d92f2d59353e5b9cda014545b352c8d6356cc0aff3b4eeae0e81893e78202d` |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `tools/inference-playground/src/scheme.rs` | `82019fd22ad565c753461d8962934fcfe8e6663f8a7971b4fcbc5f5067026be0` |
| Annotation policy | `a95e048e66465e3be3417f2ce0170aabaa3582bd4aebd5ef00ad2ae5ba65fc18` |

R5 contract SHA-256: `a8c163667df7d2fbbedde50d211a5db41fd188db033d986836fd028ef250524d`;
r5 source handoff: `a013997ca7529c36627254cf2a283e2142ec416cffd46c76df6cfa230d9e1ab0`;
r5 independent review: `823a377c9c2c3935fcde27bfbbc37df65ffddecdb09956839aaa5558ab83314a`.
Retain their accepted conditional equations and limitations. Baseline source hash
for the new owner was authenticated at the stated baseline; no source mutation
is authorized.

Exact output lease: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r6.md`.
No Rust edits, Cargo, Lean/Lake, tests, probes, network, Git, or descendants.
Do not touch quarantined paths. Hash mismatch or resource bound ends the packet.

## Runtime and review

- Role: registered `researcher`; no descendants.
- Budget: at most 200 seconds, one CPU, 1 GiB RSS; no renewal.
- Report source-path reachability, transaction/graph identity, all relevant
  disposition/error paths, capture escape, exact unsupported equation and
  source locations/hashes. Keep all parent, theorem, native and production
  gates OPEN.
- Freeze the handoff and assign a fresh non-author `compiler_referee` before
  any Lean bridge or proof promotion.
