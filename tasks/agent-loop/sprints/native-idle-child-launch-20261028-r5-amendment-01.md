# Amendment 01 — exact candidate-context test helper lease

Contract: `tasks/agent-loop/sprints/native-idle-child-launch-20261028-r5.md`.

This amendment adds exactly one implementation output path:

```text
isolated/native-idle-child-launch-r5/crates/yu-solver/src/candidate_context.rs
```

Its admitted baseline bytes are the pinned `candidate_context.rs` SHA-256
`57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e` from
commit `418bde889`. The only permitted change is a `#[cfg(test)]` helper that
replaces one existing raw scope-transformer row by ID and returns the exact
previous value. The helper must not intern, run the solver, alter resource
accounting, or expose a production/mutable API. It exists only to test the
same complete readback predicate under same-ID raw-content mutation and then
restore the original row.

This is an output-lease change only. It adds no new source input, dependency,
semantic assumption, reviewer authority, worker, budget or check. The
implementer must ACK this amendment's exact SHA-256 and the additional path
before writing it. The R5 source-first review must inspect this file alongside
the other frozen Rust outputs.
