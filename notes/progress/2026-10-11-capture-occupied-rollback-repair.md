# Occupied capture-bucket rollback restoration

Date: 2026-10-11
Status: independently reviewed M1 implementation slice; absent-key restoration,
retained-frame entry, and parent W/A3 remain open.
Baseline: `e28dfb61f`, branch `research/simple-sub-intrusion`.
Authority: private candidate suspension contract §6; no language or API change.

## Cause and repair

The Oracle-qualified actual-Local observation recorded an allocator request
when rollback restored a saved bucket for a key still present in
`capture_incidence`. The rollback owner used `HashMap::insert` for every saved
`Some(bucket)`, which may allocate even when replacing an occupied entry.

`State::rollback` now updates an occupied entry in place through `get_mut` and
retains `insert` only for a saved key that is absent. Reverse order, snapshot
contents, incidence-key cleanup, capture records, and route rollback ownership
are unchanged. The separate absent-key path is necessary for splice inverses;
its allocation/headroom guarantee remains OPEN.

The focused synthetic test checks occupied replacement and absent insertion
separately. The actual Local probe now asserts zero allocator requests over the
occupied inverse events while retaining the original failure and restoration
checks. One serial Cargo process ran:

```sh
RUSTC_WRAPPER= CARGO_BUILD_JOBS=1 timeout 120s cargo test -p yu-solver --features shadow-apply-candidate --lib capture_inverse --offline --jobs=1 -- --include-ignored --test-threads=1 --nocapture
```

Result: 2 tests passed. Each of the 8 sampled sessions reached the injected
failure and restored asserted state; each recorded 81 occupied inverses with
zero allocator requests. This is bounded evidence, not a seed/layout sweep,
allocator-failure test, or universal rollback theorem.

An independent compiler-referee found no findings. The reviewer traced
admission/splice writers and rollback order, confirmed `get_mut` cannot grow
the map, and confirmed the absent insertion remains required for splice
restoration. Broader solver tests were not run.

## Separate counterexample result

The pre-repair universal zero-allocation inverse claim is refuted on the
recorded source-qualified injected-fault domain by the independently reviewed
[counterexample derivation](../theory/2026-10-11-capture-local-rollback-allocation-counterexample.md).
That result concerns the frozen pre-repair tree only. It does not refute or
certify the current occupied-key repair. The original W/A3 and all retained
frame/pause-resume claims remain OPEN.

Next: establish the absent-key inverse storage premise at the owning splice /
transaction path, and separately resume the broader source-correct inference,
effect hygiene, proof, and F5 replacement gates. No production cutover follows
from this local repair.
