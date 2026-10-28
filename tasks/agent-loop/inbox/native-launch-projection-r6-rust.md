# NATIVE-LAUNCH-PROJECTION/r6 — Rust implementation handoff

Sprint-ID / contract revision and SHA-256: `NATIVE-LAUNCH-PROJECTION/r6`, revision 1; contract SHA-256 `01236acb3ef9134788e58aa888ec7d498ddd24fa9f64250c4f1fc2837f03034a`.
Assignment-ID / handoff revision: `native_launch_projection_r6_rust` / 1.
Parent gate / original theorem and scope locator: `SourceProblem.InferenceSoundness` in `notes/theory/lean/YulangClosure/Contracts.lean`, with unchanged quantification `∀ s x d a, p.supported s → p.generates s x d → p.solves d a → ∃ e, p.sourceJudgment s x e ∧ p.sameScoped s x e a`. `SourceProblem.NativeCorrespondence` remains separate and open.
Baseline / direct dependency hashes: clean isolated snapshot from `7b3ad7074`. Before body reads, all 12 hashes in the contract Rust source/dependency read set were checked and matched. Relevant source baselines: scheme `35c58dca3748595e273cd53bfba07da2be3fd340ec63c56f6a18adea5e514fb1`, context `57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e`, extrusion `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`. Read only the isolated snapshot bodies, plus the frozen R5 outcome/review as rejected reference.
Role / actual worker ID / current session / launch or resume receipt: assigned `implementer`; worker `/root/native_launch_projection_r6_rust`; session `NATIVE-LAUNCH-PROJECTION-20261028/r6`; no separate launch receipt exposed to this worker.
Requested model and effort / observed model and effort: `gpt-6-luna` / high requested; observed model and effort UNKNOWN in available runtime metadata.
Exact leased paths / all authors and contributing descendants:
- `isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_scheme.rs`
- `isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_context.rs`
- `isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_extrusion.rs`
- `tasks/agent-loop/inbox/native-launch-projection-r6-rust.md`
Author: `/root/native_launch_projection_r6_rust`; descendants: none.
Outcome class: provisional source-native evidence / implementation instrumentation.

## Outcome and source correspondence

Added test-only instrumentation to the ordinary source-driven fixture in `candidate_scheme.rs`. Execution reaches `freshen_candidate_graph_core` → `begin_candidate_fresh_bound` → `candidate_begin_bound_restoration`, where a restoration invocation ID is recorded with the exact `ReplayOperationId`. Successful `candidate_drive_bound_restoration` return records that same invocation, handle, and returned emission.

The completed observer resolves the returned emission's admission and requires its `FreshUse` cause to retain the exact source `BoundKey`, use origin, mapped relation, and destination `BoundKey`. It verifies the retained emission slot/readback, then independently rereads the current physical bound vector slot through `candidate_physical_slot_bound`, including owner row and value/effect row/atom lane. The ordinary fixture now includes falsifiers for sibling invocation/handle reassociation, wrong source and destination bounds, current physical vector replacement and removal, and mutation under the same raw transformer ID. Physical and raw values are restored before the corresponding acceptance/rejection assertions; the transformer test captures rejection while mutated, restores the exact moved old value, then asserts rejection and restored acceptance.

Raw effect transformer contents are checked by ID through `authenticate_replay_ancestry`; this is a bounded test observation of the existing resolver, not a whole-language theorem. No non-Clone transformer is cloned. No production branch, public API, diagnostic, fixture text, expected output, dependency, or source domain was intentionally changed.

This remains reversible `#[cfg(test)]` evidence. It does not establish whole-source/native correspondence, close the launch projection, prove inference soundness, or authorize production cutover. It must be source-first independently reviewed before any conditional check. No compiler or test execution establishes that the fixture assertions pass.

## Prior evidence reused and rejected

R5 review/outcome is used only to target the actual failure modes: stale retained readback after physical vector mutation, unauthenticated restoration handle, same-ID transformer contents, and unsafe mutation assertion ordering. I did not copy or restore the rejected R5 Rust output. Reused baseline owners are the existing restoration lifecycle, FreshUse admission/readback records, physical-slot reader, and raw transformer resolver.

## Artifact hashes and checks

Frozen source output SHA-256:

```text
isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_scheme.rs
c79b136dd033a4d0e3f1664be670fda0c538866baa05a20c273d69a1927ead0d
isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_context.rs
19726ef8a6034a1b99f629021b6b7e97ec638f3c1d683206de3c6eac8025a2ec
isolated/native-launch-projection-r6/crates/yu-solver/src/candidate_extrusion.rs
e532e7228487e125a73576cb76b8bf17c065862b049bd8d6f8fa185bb77c54af
```

Checks: none. The contract prohibits worker Cargo/tests/compiler/Lean/Lake/build/formatter/Git/descendants. No checks were run. No scratch or generated outputs were created.

Budgets: assignment grant 1,100 seconds; actual active duration and CPU/RSS not independently measured by this worker. No renewal requested or assumed. No deviations known.

Parent application / exact remaining premise and owner: this supplies only provisional ordinary-source instrumentation. Fresh source-first independent review is required; only after acceptance may Luna use the contract's conditional checks. The original inference-soundness, native-correspondence, semantic, and production gates remain open. Parent/proof owner TODO: apply the eventual reviewed bounded source observation to the original parent without treating a green test as theorem closure; keep all missing constructors/consumers and A/B premises explicit.
Next related step inside envelope: independent reviewer inspects these exact frozen bytes against the baseline, contract, R5 rejection, and existing source/native obligations; no producer self-certification.
Mutual TODOs: proof/core owners should identify the exact bridge point (if any) from this successful restoration observation to their bounded launch projection, and state the first missing source/native owner. This instrumentation supplies no premise for erased resource callbacks or unrelated launch writes.
Worker state / writes stopped receipt / unresolved descendant leases: STOPPED; all four assigned output paths frozen; no descendants, subprocesses, or scratch paths. No other path was written.
Commit-ready milestone or pending review/integration: pending fresh independent source-first review; not commit-ready and not an accepted gate.
