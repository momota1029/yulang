# EFFECT-PERMISSION-CAPTURE corrected Rust verification receipt

Primary receipt for sprint `EFFECT-PERMISSION-CAPTURE-20261028/r1` under
amendment 01, SHA-256
`35e1a4e9f9859886fd7324abca59089da7f5e2c7d71c0fe12b544c396d4d13d9`.
This file records the single permitted corrected invocation. It does not
replace or erase the earlier failed command recorded in the Rust lane handoff.

## Frozen inputs

- `crates/yu-solver/src/shadow_apply.rs`: SHA-256
  `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`
- `tasks/agent-loop/inbox/effect-permission-construction-rust.md`: SHA-256
  `5c1bad68921ad95e3707ca90f4a9e559d01f385771ceacbe3f72829b3c2e7189`
- Both hashes were rechecked after execution and still match.

## Invocation and result

```text
timeout 240s taskset -c 0 env CARGO_TARGET_DIR=/tmp/yulang-effect-permission-capture-20261028-r1/rust-target CARGO_BUILD_JOBS=1 cargo test -p yu-solver --lib --features shadow-apply-candidate formal_permission -- --nocapture
```

- Exit status: **0**.
- Elapsed wall time: **41.22 seconds**.
- Maximum RSS reported by `/usr/bin/time -v`: **1,652,828 KiB** (about 1.58 GiB), exceeding the amendment's 1 GiB cap by 604,252 KiB (about 590 MiB).
- Tests executed: **2 passed, 0 failed, 814 filtered out**.
- Exact executed tests:
  - `candidate_effect::tests::negative_concrete_formal_permission_recovers_its_shared_port_and_rolls_back`
  - `candidate_effect::tests::tuple_formal_permissions_keep_element_paths_and_transaction_ownership`
- Test output, timing/RSS, command and status are retained in the leased scratch directory:
  `/tmp/yulang-effect-permission-capture-20261028-r1/rust-target/`.
- A post-run process check found no `cargo` or `rustc` process. No further Cargo invocation or source edit is authorized in this sprint.

## Disposition

The two existing focused tests passed for the frozen extraction. The invocation
exceeded the admitted memory limit, so the corrected run is recorded as
**RESOURCE-CAP BREACH / SPRINT VERIFICATION INCOMPLETE**, not as a fully
contract-compliant check. Do not retry or broaden the suite. The Lean catalog
model remains checked only within its declared premises; actual constructor,
LIFO worklist, canonical representative and negative-root arrival
correspondence remain OPEN. Every original parent and production gate remains
OPEN.
