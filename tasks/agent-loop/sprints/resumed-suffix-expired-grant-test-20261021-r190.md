# Sprint R190 — resumed suffix expired-Grant test alignment

Status: ACTIVE, primary-only test-contract probe; no runtime semantic changes.
Branch: `research/simple-sub-intrusion`; baseline `f95c0ec439fe69385cedc5e2bbe99a5329560fad`.
Authority: pursue the unchanged playground goal. Keep fresh-owner non-resurrection as the provisional behavior because the existing guard test and the reviewed local-Grant rule both deny reuse of an expired receiver. Raw continuation re-entry remains outside that theorem, so this test-only choice does not close or alter that semantic parent. No subagents.

## Outcome

Replace the positive completion expectation in
`runtime_unmatched::unmatched_request_preserves_original_suffix_across_outer_handling`
with an assertion that the resumed `other` request reaches the inner handler and
stops there with `Unavailable(HandlerEvidence)`. Assert the inner handler source
range to distinguish this from an earlier failure. Keep the first-request
unhandled suffix assertions and the sibling fresh-owner guard intact.

This corrects a regression fixture that is source-equivalent to the existing
expired-Grant guard but demanded the opposite outcome. It does not change
Yulang2 sample outputs, the runtime, the Grant rule, or the raw-resumption
semantic question. If later approved semantics require grant restoration, both
fixtures need a source-qualified distinction or a jointly revised contract.

## Pins and exact leases

- `tools/inference-playground/tests/runtime_unmatched.rs` — SHA-256 `480229b78a1203c5c23fc4d7de78f9c7c257a1d8024661c3a24f9cd3fbbf1208`
- `tools/inference-playground/tests/runtime_resume.rs` — SHA-256 `ec87db17fa228b90332a2b4c71bbafed2e70f6aad6c6c26d441edd7aea4e6426`
- `tools/inference-playground/src/runtime/receiving.rs` — SHA-256 `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9`
- R189 source-equivalence result — SHA-256 `9353fde80272b700d8febefd49a722b7bbab27fa34ab82b4c8c1ec888120b1ea`
- Reviewed receiving theorem — `notes/theory/2026-10-15-runtime-receiving-view-construction.md`, §3.

Write only `tools/inference-playground/tests/runtime_unmatched.rs`, this
contract, `tasks/agent-loop/inbox/20261021-r190-expired-grant-test.md`, and
primary-owned `tasks/agent-loop/current.json`. No production source edits.

## Verification and boundary

Run the two focused integration tests, then the complete `yu-playground` package
test suite, with one Cargo process. Success requires the resumed request to
fail at the inner handler's pinned source range, the sibling guard to remain
green, and all package tests to pass. Maximum active work: 600 seconds, no
carryover. Independent review is unavailable under the solo-worker constraint;
any result remains provisional and parent/A/B/source-native/production gates
stay OPEN.
