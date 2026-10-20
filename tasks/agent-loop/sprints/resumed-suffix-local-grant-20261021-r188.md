# Sprint R188 — resumed suffix local Grant owner

Status: ACTIVE, primary-only serial investigation; no theorem or production promotion.
Branch: `research/simple-sub-intrusion`; start HEAD `183d69ef36cf45753980a83b7eecefd303421650`.
Authority: continue the unchanged user goal and the original computation-forwarding preservation parent pinned in R187. R187's 6000-second cap is exhausted and is not reused. No subagents or new worker identities; the user requires Luna to be the only worker.

## Original outcome and success evidence

Keep the original parent statement, its A/B obligations, source/native correspondence, accepted semantics, and expected outputs exactly as pinned by R187. This sprint does not narrow or prove that parent. It investigates one observed ordinary runtime failure: `runtime_unmatched::unmatched_request_preserves_original_suffix_across_outer_handling` expects the resumed suffix's `other 23` request to reach the original inner handler, but the runtime stops with `Unavailable(HandlerEvidence(... range: 87..123))`.

Success is a source-qualified account of event 1 from request creation through observations, owner/view receipt, image ancestry, and handler selection, plus either (a) an owner-safe implementation repair that preserves the positive local-Grant rule and makes the unchanged test pass, or (b) a precise candidate counterexample/remaining premise that explains why no repair is justified. A debug print, green test, or missing-receipt guess alone does not satisfy this outcome.

## Exact source inputs and leases

Pinned read bytes at sprint start:

- `tools/inference-playground/src/runtime/receiving.rs` — SHA-256 `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9`
- `tools/inference-playground/src/runtime/machine.rs` — SHA-256 `7187abd78ca13efaeebf4cb70837c98360c0024d082a59af331da41169d3409b`
- `tools/inference-playground/src/runtime/program.rs` — SHA-256 `6c46d4cf908eafc808f23f3b9a4e2eab9f4a1f1e5b45b90a9acd68cd87c4bf6f`
- `tools/inference-playground/tests/runtime_unmatched.rs` — SHA-256 `480229b78a1203c5c23fc4d7de78f9c7c257a1d8024661c3a24f9cd3fbbf1208`
- `tools/inference-playground/tests/runtime_resume.rs` — SHA-256 `ec87db17fa228b90332a2b4c71bbafed2e70f6aad6c6c26d441edd7aea4e6426`
- Candidate context only: `notes/theory/2026-10-21-r187-primary-source-readback.md` — SHA-256 `1f39ea63031edc2325ab7013518f0c7e34fb275b134ebf6b47ba546013b988ae`

Read lease: the six paths above and only the exact called constructors/consumers needed to trace this request. Write lease: `tools/inference-playground/src/runtime/receiving.rs`, `tools/inference-playground/src/runtime/machine.rs`, `tools/inference-playground/src/runtime/program.rs`, `tools/inference-playground/tests/runtime_unmatched.rs`, and `tasks/agent-loop/inbox/20261021-r188-resumed-suffix-local-grant.md`. Do not edit solver semantics, source fixtures, expected outputs, unrelated contracts, or frozen R187 artifacts.

## Method, falsifier, and implementation boundary

Trace actual IDs for event 0 and event 1: request owner, each authenticated observation, execution view and receipt, candidate receipt lookup, receiver boundary, image parent chain, active invocation and installed CatchReturn owner. Compare against the source constructors in `Machine::propagate_request`, continuation capture/resume, and `Receiving::local_grant`.

Falsifier for an implementation repair: the event-1 handler has no authentic candidate-owner receipt or no image ancestry reaching its annotated receiver. In that case preserve `Unavailable(HandlerEvidence)` and report the exact missing premise. A repair may only restore an already justified current owner/view/receipt join. It may not infer a Grant from absence, reuse event-0 authority for event 1, skip the observation/event checks, or make the handler unconditional.

No changes to accepted language semantics, original parent quantifiers, source-to-native claims, or expected outputs. No production admission authority is granted by this runtime investigation.

## Work mode, resources, and review

Luna performs the bounded work serially because the user explicitly forbids subagents. No simulated/nested dispatcher or worker is launched. Maximum active work: 1800 seconds; no carryover. At most one Cargo process, focused tests only; no concurrent heavyweight build. Stop on resolved source/native explanation, exact counterexample, cap, no-progress limit, or session end. Preserve all other dirty files and leases.

Fresh independent review is unavailable under the user's solo-worker constraint. Any implementation remains candidate-only and uncommitted until independent review is possible. The primary may freeze the exact source-qualified result; all parent/A/B/source-native/production gates remain OPEN.

## Closeout record

Before/after evidence, command outputs, exact owner/view/receipt chain, omissions, resource use, worktree state, and next falsifiable step are recorded in the leased inbox result. End this session with an honest STOPPED state; do not leave a worker RUNNING without runtime evidence.
