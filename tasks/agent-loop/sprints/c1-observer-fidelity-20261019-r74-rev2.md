# Sprint R74 — version 2 bounded build continuation

Status: ACTIVE, approved by Luna as primary under the user's explicit inference/evaluator implementation goal. Branch `research/simple-sub-intrusion`; baseline remains `d21c8eb3a87e43dd441474c9f138e71b1d8372ff`. This version supersedes R74 revision 1 only for the exact lease, source correction and resource/verification boundary below; its fixed source, C1 outcome, semantics, proof boundary, falsifiers and other leases remain unchanged.

## Frozen provenance correction

The immutable revision-1 contract at `tasks/agent-loop/sprints/c1-observer-fidelity-20261019-r74.md` has actual SHA-256 `9b225304040b8ff11b1f1cb79876de136ce0400d69c68fef87bf07288f2c8a25`. The R74 proof note and inbox both copied a mistyped contract SHA; they remain frozen and are not changed or treated as authority. Luna records this discrepancy and the correct hash in the final integration receipt. The failed compile is attributed to two baseline source initializers and a `cfg(test)` field mismatch; no claim is made that the baseline was independently built.

## Narrow added authority

Add exactly one write path: `crates/yu-solver/src/shadow_apply.rs`, direct baseline SHA-256 `5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb`. Luna may edit only the two test-only `Graph` initializers near the original lines 2304 and 2410 to initialize the already `#[cfg(test)]` `capture_forest` field consistently with each fixture. For the empty `GraphState::default()` fixture, use an empty forest snapshot. For the fixture paired with an actual intrusion state, use that state's existing `forest_snapshot()` result. Preserve all assertions and test expectations. No production path, type, semantic rule, expected output or unrelated initializer may change.

All other R74 revision-1 leases and constraints remain exact. The accessor in `candidate_intrusion.rs`, observer in `candidate_scheme.rs`, registration in `lib.rs`, and new C1 test remain test-only. Proof author `/root/r74_proof` remains STOPPED; do not relaunch or revise its frozen artifacts. The conditional proof is one input to fresh review, not a fidelity certificate.

## Single verification retry and resources

Permit exactly one additional primary-owned execution, only after the four code paths and implementation artifacts freeze:

```sh
CARGO_BUILD_JOBS=2 timeout 180s cargo test -q -p yu-solver --features shadow-apply-candidate --lib candidate_c1_observer_tests -- --nocapture
```

Compilation and test execution both consume this one attempt. Do not retry on a second compile error, timeout or test failure. The first attempt failed after 12.06 seconds before any test ran; that time and the full original 2,400-second reservation remain charged, with no refund or transfer.

One additional 300-second Luna grant is approved: at most 120 seconds for the two initializer corrections and freeze receipt, and one 180-second bounded verification attempt. Revised total sprint envelope is 2,700 seconds: original Luna implementation/source map 900, Sol proof 600 (fully reserved; worker stopped with elapsed UNKNOWN), two fresh reviews 300 each, Luna integration 300, and the additional Luna continuation 300. Astra 0; no carryover; no second retry; global ceiling unchanged. This corrects revision 1's ambiguous integration wording: integration 300 seconds is separate from Luna's original 900-second implementation allocation.

## Success, review and stop

Success still requires the fixed non-scoped candidate source to reach the exact helper C1 once with cursor `(0,None,false)`, emit a complete constructor-owned ledger, complete the observer-erasure/fidelity argument, and pass independent compiler/source and spec/conformance review of the same frozen code, ledger and receipts. The added initializers only make the existing test target construct its test-only graph fixtures; they do not count as C1 evidence.

Stop after the single retry on any build failure, timeout, ambiguous helper occurrence, incomplete field/provenance, observer effect on solver control/order/identity, or blocking/major independent finding. Leave C1 and every original parent OPEN. No additional probe, test command, worker, lease or output path is authorized by this revision.

## Dependency pin and Luna approval

```text
5bbcf27d51906814ba38b2cca2066807d285d0b1817f0ea6e04d70c4a5c8a5cb  crates/yu-solver/src/shadow_apply.rs
```

Luna accepts the selector's bounded revision and grants this one path/continuation. Only Luna records state, adjudicates review, and stages/commits/pushes explicit accepted artifacts. Original parent, Simple-sub A/B remain OPEN 0→0; R50 remains NOT_ADOPTED.
