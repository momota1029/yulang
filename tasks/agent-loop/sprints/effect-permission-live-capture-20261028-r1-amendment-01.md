# Amendment 01 — EFFECT-PERMISSION-LIVE-CAPTURE-20261028/r1

Status: ADMITTED by Luna after the sprint-end selector's material-blocker
recommendation. This amendment changes only the bounded validation allowance;
it adds no compiler semantics, production authority, source acceptance or proof
closure.

Base contract: `tasks/agent-loop/sprints/effect-permission-live-capture-20261028-r1.md`,
SHA-256 `08224918615443e37273da946a13c1437a1c0ec7afa37314225d56f8aa543f2b`.
Admission baseline: `31ea9a07f`. Initial Rust handoff:
`tasks/agent-loop/inbox/effect-permission-live-capture-rust.md`, SHA-256
`3c77c6a39fb100c1cdc4795ba6c89b7ac457109dd620a573c68e43999bf1b44f`.

## Failure and frozen correction

The sole initial Cargo invocation exited 101 after 37.32 seconds, with peak RSS
1,159,420 KiB and zero executed tests. It reported four missing `Debug`
implementations for `Endpoint` and one private capture-method access. The
producer applied two source-only corrections after that invocation: derive
`Debug` on the private `Endpoint` enum and call the existing `pub(super)`
`capture_candidate_graph` wrapper. Those corrected bytes are still unvalidated.

Current admitted source bytes before this amendment's validation:

- `crates/yu-solver/src/candidate_effect.rs`:
  `f0b08ea8cee26e372b2a2e0b8076b82e4e6e29fa73618fe9cddfe360df117b8f`
- `crates/yu-solver/src/candidate_scheme.rs`:
  `33c066da527c3251d106aa9ca9a4f77d3f54844478ea2f6f2258933a5eb30852`
- `shadow_apply.rs` remains `2e0aba4d172e97dd60ba909a7aca873c109785f3d38cce46ddd033c70f64613d`.

## One additional validation attempt

Reopen only `candidate_effect.rs`, `candidate_scheme.rs`, and the new handoff
`tasks/agent-loop/inbox/effect-permission-live-capture-rust-amendment-01.md`
for `/root/formal_permission_live_capture_rust`. The previous Rust handoff and
Lean outputs remain immutable. First perform lightweight source/diff checks and
confirm at least 4 GiB available memory. Then exactly one focused invocation is
allowed:

```text
/usr/bin/time -v timeout 180s taskset -c 0 env CARGO_TARGET_DIR=/tmp/yulang-effect-permission-live-capture-20261028-r1/rust-target CARGO_BUILD_JOBS=1 cargo test -p yu-solver --lib --features shadow-apply-candidate formal_live_capture_source_observation_trace -- --nocapture
```

Limit: one CPU, 2 GiB RSS, 180 seconds for the command, and 240 seconds total
for the amended assignment including receipt and primary synchronization. Keep
the same target directory. Do not retry. A second compile failure, test failure,
timeout, resource breach or source-behavior concern ends Rust execution for this
sprint as INCOMPLETE.

This 240-second maximum is reallocated from the original 600-second contingency;
the sprint total remains 3,600 seconds, with 360 seconds contingency left.
The initial failed attempt remains charged to its original grant. The already
planned 450-second independent review does not change. Heavy Cargo remains
serialized; the one pinned Lean heavy check has finished and will not be rerun.

## Evidentiary boundary

The existing fixture directly calls `candidate_formal_annotation` and bypasses
source preflight. Even a successful trace is internal producer evidence only.
It cannot close source acceptance, the successful-constructor realization,
canonical representative transport, universal live row/bound/context
simulation, root arrival, the original parent theorem, or production gates.
Instrumentation remains provisional under primary review. All original
Simple-sub, effect-hygiene, source/native, principality, termination and
production obligations remain OPEN.

Luna owns the exact lease transition, final review admission, current-state
synchronization, and Git. The worker owns no Git path or descendant.
