# DEMAND-TRACE-COMPILE/r13

Status: **ADMITTED BY LUNA** under the same ongoing inference/executor diagnostic objective after R12 `CLOSED_INCOMPLETE`. R12 remains immutable and unchanged. Baseline source commit `7b3ad7074`; R12 close commit `69ebe0545`. R12 outcome SHA-256 `0708322e5657939276bb0827cd00431774cf56ee4a7b3bcdd4abfc530241e175`; review SHA-256 `09d8764d7d8ab3a580d3b3e86d9c9e69381631b63c6a3306f14031637098239d`. Inputs manifest `tasks/agent-loop/sprints/demand-trace-compile-20261028-r13-inputs.json`, SHA-256 `475b5eaaea90d7a5f66b52ebf6b3cf45969b9c4c1953dd00c5593c75332763ee`; 434 entries. R13 snapshot is `isolated/demand-trace-compile-r13/`; its two leased Rust files are independent copies. R12 paths remain frozen.

## Fixed goal and outcome

Repair only the R12 test-instrumentation compile defects and obtain the same focused Cargo-1 execution under review. R12's compile errors were: the `format!` call omitted `graph.boundary` and placed an `Option<&Node>` in a Display slot; two `Graph` test literals in `shadow_apply.rs` omitted the test-only `r12_trace_graph_id` field. Do not alter production solver semantics, fixture text, assertions, expected behavior, error kind, source domain, or original `InferenceSoundness` claims.

The bounded outcome is a feature-correct execution of `replay_constructor_lineage_observes_rejected_cross_route_authentication` that either records the same-invocation R12 source/graph/bound/demand/use/antecedent diagnostic, or preserves an honest new failure. Compilation alone is not success. No semantic repair or map insertion is authorized. The deferred-demand source law and original source/native Call/shared-witness bridge remain OPEN.

## Frozen inputs and exact leases

The 434-entry manifest pins the R12 parent cone, adjudicated outcome/review and failed Cargo logs, the R13 isolated source snapshot, all Rust/Cargo source files in the copied workspace, and exact initial hashes of the two mutable R13 sources. Immutable R12 source/evidence must not be changed. Verify all manifest pins and the exact source leases before body work.

- Implementation, Luna/high, maximum **400 seconds**, writes only:
  - `isolated/demand-trace-compile-r13/crates/yu-solver/src/candidate_scheme.rs`
  - `isolated/demand-trace-compile-r13/crates/yu-solver/src/shadow_apply.rs`
  - `tasks/agent-loop/inbox/demand-trace-compile-r13-rust.md`
- Luna primary owns source/proof analysis after any trace, maximum **300 seconds**; no Lean artifact is required or authorized.
- Independent fresh `compiler_referee`, Sol/medium, maximum **300 seconds**, reviews exact frozen bytes and final logs.
- Luna primary checks/integration maximum **500 seconds**.
- Aggregate fresh envelope **1,500 seconds**, no renewal; Astra 0. Proof/source work waits for the actual trace and must not infer correspondence from the R12 compile failure.

Initial code changes are restricted to supplying `graph.boundary` in its correct format position and initializing the existing test-only trace ID field in the two test constructors. Preserve exact field meaning and lazy trace guarding. Any additional compile correction must be local to this instrumentation and within the same two files. Do not change any other owner, fixture, assertion or expected output.

## Review and conditional checks

A fresh independent source-first review must ACCEPT the frozen candidate and Rust handoff before Cargo-1. Cargo-1 is the only authorized first attempt. If and only if Cargo-1 fails during compilation due to a remaining R13 instrumentation-local issue, one bounded correction may be made within the implementation envelope. Freeze new hashes and obtain independent delta ACCEPT before Cargo-2. Cargo-2 is then the final attempt. A runtime/test failure, resource limit, source-law issue, changed fixture, or non-instrumentation defect ends this sprint; no retry or semantic repair follows.

The exact command for either authorized attempt is:

```text
CARGO_TARGET_DIR=isolated/native-witness-frame-repair-r9/build-target cargo test --manifest-path isolated/demand-trace-compile-r13/crates/yu-solver/Cargo.toml --locked --features shadow-apply-candidate replay_constructor_lineage_observes_rejected_cross_route_authentication
```

At most two Cargo attempts, each at most **120 seconds wall**, combined at most **240 seconds**, CPU affinity 0, maximum **2 GiB sampled process-group RSS**. Capture exact argv, complete stdout/stderr, tool versions, exit and sampled resources in:

- `isolated/demand-trace-compile-r13/logs/r13-cargo-1.argv`
- `isolated/demand-trace-compile-r13/logs/r13-cargo-1.stdout`
- `isolated/demand-trace-compile-r13/logs/r13-cargo-1.stderr`
- `isolated/demand-trace-compile-r13/logs/r13-cargo-1.resources.json`
- `isolated/demand-trace-compile-r13/logs/r13-cargo-2.argv`
- `isolated/demand-trace-compile-r13/logs/r13-cargo-2.stdout`
- `isolated/demand-trace-compile-r13/logs/r13-cargo-2.stderr`
- `isolated/demand-trace-compile-r13/logs/r13-cargo-2.resources.json`

Absent attempts are **NOT_RUN**, never synthesized. Lean is **NOT_RUN** unless the primary later finds an independently justified source theorem and obtains a separately admitted packet.

## Stop conditions and open gates

Stop on any semantic or fixture/expectation change, source-domain or quantifier weakening, unleased owner, false trace join, missing source authority, resource limit, initial/delta review rejection, or second compile failure. Preserve every failure. No finite trace closes original `YulangClosure.SourceProblem.InferenceSoundness`, full source/native correspondence, effect hygiene or production.

Luna owns current-state updates, review receipt `tasks/agent-loop/inbox/demand-trace-compile-r13-review.md`, outcome `tasks/agent-loop/history/demand-trace-compile-20261028-r13-outcome.md`, explicit staging, integration and Git.
