# Primary admission — amendment 04 research baseline and focused verification

Contract: `SELECTED-MODULE-ENTRY-AND-FRESHENING/r1`, amendment 04 (`3711cca5dc9cbaa6eb94cb3589d4c10ff0844a5a4639168bec82106b06fe3bc1`).

## Admission decision

After the independent amendment-04 review PASS (`tasks/agent-loop/inbox/selected-module-entry-freshening-amendment04-review.md`, SHA-256 `3ef0462e0c9b978b4002fd680e8c5773397bc48d9c117d56f212e80ce2ef1af8`), I admit the exact isolated three-owner bytes as a **research baseline only**:

- `candidate_effect.rs`: `8d80a98b4fe22bd91409b645dbac3d5bcd10eed4b45bbe6f5c17a773e65874f6`
- `candidate_scheme.rs`: `33235b840c42be38be1df634291e309c0d143fa62f412afa633768be9b40aa0e`
- `shadow_apply.rs`: `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`

Admission does not close native reconstruction, whole-branch allocation-root correspondence, H_u, A/B, effect-hygiene, or production gates. It grants only the exact verification below.

## Frozen checks

Run two exact unit tests, in order, against the isolated manifest. Do not broaden the filters or run the recursive transport probe. Each invocation is capped by the remaining portion of a shared 180-second budget; one failure, timeout, or resource breach stops the sequence. One CPU, `CARGO_BUILD_JOBS=1`, at most 2 GiB aggregate process RSS, and at least 4 GiB available memory before launch. Use a unique target and retain raw combined stdout/stderr plus resource and exit receipts under the output directory.

1. `candidate_effect::tests::tuple_formal_permissions_keep_element_paths_and_transaction_ownership`
2. `candidate_effect::tests::formal_permission_symbolic_effect_memo_trace_tolerates_missing_constructor_identity`

Command form (the actual timeout seconds for each invocation must be frozen in its receipt so the total never exceeds 180 seconds):

```text
/usr/bin/time -v timeout --signal=TERM --kill-after=5s <remaining-seconds>s taskset -c 0 env CARGO_TARGET_DIR=/home/momota1029/rust/yulang/isolated/selected-module-entry-freshening-repair-r1/target-amendment04 CARGO_BUILD_JOBS=1 RUSTC_WRAPPER= cargo test --locked --manifest-path /home/momota1029/rust/yulang/isolated/selected-module-entry-freshening-repair-r1/crates/yu-solver/Cargo.toml -p yu-solver --lib --features shadow-apply-candidate candidate_effect::tests::<exact-name> -- --exact --nocapture
```

Target directory: `isolated/selected-module-entry-freshening-repair-r1/target-amendment04/` (disposable build output; do not commit). Exact output directory: `tasks/agent-loop/verification/selected-module-entry-amendment04/`, containing `run-01-original-regression.log`, `run-02-missing-constructor-trace.log`, and `result.md`. Primary owns these paths and is the sole verification process. Check and record available memory and absence of another active heavy Cargo process immediately before launch. No Lean rerun, workspace suite, unrelated source read, retry, or output-path expansion.

The review PASS and this admission authorize only these two bounded invocations. All semantic/proof and production limits remain as stated in the sprint contract.
