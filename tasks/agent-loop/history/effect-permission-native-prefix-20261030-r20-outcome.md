# R20 outcome: compile blocked before runtime

Sprint `EFFECT-PERMISSION-NATIVE-PREFIX/20261030-r20` closed as **`CLOSED_INCOMPLETE — COMPILE_BLOCKED_BEFORE_RUNTIME`**. The selected ordinary source module never ran, so this sprint authenticates no SCC plan, member/provider prefix, selected occurrence, arena identity, journal event or native `intern_structure` call. This is a tooling/dependency failure, not a semantic counterexample and not evidence that the native journal is absent.

The frozen contract is [R20](../sprints/effect-permission-native-prefix-20261030-r20.md), with [amendment 01](../sprints/effect-permission-native-prefix-20261030-r20-amendment-01.md) and [input manifest revision 2](../sprints/effect-permission-native-prefix-20261030-r20-inputs-r2.json). The base is `871de7c6dca9c2645ad10bad231f05c46392b244`. Their identities and the frozen result hashes are recorded in the R20 evidence JSON.

## Rust probe

The one authorized command was:

```text
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate --lib r20_native_prefix_selected_ordinary_candidate_trace -- --nocapture
```

It exited 101 during test-binary compilation after 40.613 seconds. Stdout was empty; the complete stderr and resource receipt are preserved in `isolated/ep-native-r20/project/receipts/native-prefix-receipt.json` (SHA-256 `fa0b472bd0ce7477f8d082872439da3158e7f2d2c0fe92e9a46cc40a598e4e27`). The process used one CPU; sampled peak process-tree RSS was 45,875,200 bytes; available RAM before launch was 28,694,102,016 bytes. No retry was made.

There were four compiler errors. Two local instrumentation mistakes (`SourceAnnotation.text` and missing `Debug` for `RoutePurpose`) were corrected only after the sole command, so those edits are uncompiled. Two errors remain in unleased detached `shadow_apply.rs` `Graph` initializers missing `formal_capture_trace_id`, required by the isolated `candidate_scheme.rs` snapshot. The worker did not modify that dependency.

The receipt has `machine_trace: null`; every one of the 21 R18 `TupleInput` fields is `unavailable_test_never_executed`. No defaults, skipped-operation claims, runtime absence or same-call input correspondence are inferred.

The five final isolated test-only source files and a byte-identical copy of the [complete Cargo receipt](effect-permission-native-prefix-20261030-r20-rust-snapshot/native-prefix-receipt.json) are preserved under [the Rust source snapshot](effect-permission-native-prefix-20261030-r20-rust-snapshot/README.json), with their SHA-256 identities. The snapshot includes two post-command local fixes that remain uncompiled. It is a record of the failed probe, not a compiler change.

The independent referee accepted preservation of this failed experiment and identified two major successor requirements in [the review](effect-permission-native-prefix-20261030-r20-review.md): bind every source and term event to the same invocation/arena/selected occurrence, and observe the session journal's owning `.take()` transition or rigorously distinguish any source reconstruction from direct observations. Neither finding changes this failed-execution classification.

## Lean result

The frozen [Lean artifact](../../../notes/theory/lean/YulangClosure/FormalPermissionNativePrefix.lean) (`7129aae721bf07eeb9330540c833a3b7d6d225dea8dc9e722b6e207e2bbef0f1`) contains four checked general transition/projection roots. Three have empty axiom sets; `validates_cons` uses `[propext]`. Audit 1 passed on Lean 4.35.0 in 20.98 seconds at 971,900 KiB peak RSS. Its complete raw output and resource record are in the leased Lean scratch. The second audit was not run.

The call-specific event list, source/arena-selected state, completion equality and R19 `selected_call_excludes_R18` application were **not constructed**. The general projection model accepts arbitrary event lists and does not authenticate native execution. The independent referee confirmed these limits.

## Gate status and next evidence

R18's native active-journal premise, R19 native-call exclusion, the original source/native correspondence, source-owner hygiene, the original parent theorem, soundness, principality, termination and production all remain OPEN. R20 closes no part of those parent gates and changes no compiler semantics or expected output.

The selector's sprint-end recommendation is to pursue the approved annotated-relay permission-to-consumer path next. A successor probe must preserve the original source domain and quantifiers, include the build dependency in its explicit isolated leases, and fix same-call identity plus owner-transition observation before accepting any trace. It must keep every prior OPEN gate open unless its own evidence closes that exact obligation.

The two producers froze all writes and had no descendants. Independent review is accepted for this exact failure checkpoint. The primary's [Git receipt](effect-permission-native-prefix-20261030-r20-git-checkpoint.md) records the coherent checkpoint and push disposition.
