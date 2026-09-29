# SCC intrusion: Rust incoming-use characterization slice

Date: 2026-09-30
Branch: `research/simple-sub-intrusion`
Classification: current-path test evidence; no replacement implementation authority

## Result

Added `synthetic_identity_incoming_uses_accept_distinct_function_constraints`
in `crates/yu-solver/src/lib.rs`. The test builds a synthetic identity
Function root in a collected batch, gives it two distinct incoming use IDs,
routes each through the current solver's incoming-use path, and applies
different Function constraints to the two use rows: `Int -> Int` and
`(Int -> Int) -> (Int -> Int)`. Both constraints are accepted without solver
errors and both routes are recorded.

The witness runs through Rust and uses no finite model. The earlier
assistant-authored Python model has since been removed, and its outputs are not
evidence for this result or any other Gate B/C claim.

## Review and limits

An independent spec-auditor approved the pre-write test contract and reviewed
the diff. The test does not assert F5 scheme shape, binder count/order,
ordinals, arena IDs, or resource counters. Its setup manually publishes the
current implementation's finalized member view, so the test characterizes the
current incoming route rather than the future intrusion engine or the full SCC
publication scheduler.

The first review found a major evidence gap: accepting both constraints alone
did not directly establish fresh identity isolation. The test was extended to
inspect each actual routed Function lower before later constraints. It now
checks that the argument and result share one exposed live variable identity,
and that the identities for the two uses differ from one another and from the
root variable. An independent delta review accepted these assertions without
blocking or major findings. This establishes per-use identity sharing and
freshness for the one exposed identity variable in this witness. It does not
establish isolation of every graph node, all cross-use edges, or solution-space
independence through a shared environment. It also does not establish
source-level Oracle parity, intrusion correctness, soundness, or principality.
The source-level Oracle identity-use witness remains unsupported by current
Yulang3 HIR, as recorded in `2026-09-29-intrusion-rust-replacement-map.md`.

Focused verification:

```text
RUSTC_WRAPPER= cargo test -p yu-solver synthetic_identity_incoming_uses_accept_distinct_function_constraints --lib
1 passed; 428 filtered out
git diff --check -- crates/yu-solver/src/lib.rs
```

The test is a temporary characterization of the current Rust path, not an
acceptance contract for F5 or the replacement design.
