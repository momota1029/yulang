# R104 v3 final Cargo-call amendment

Status: **ADMITTED** under the standing Rust/Lean goal. This is a narrow
execution-phase amendment to R104 r1 and r2. All parent semantics, source
obligations, leases, frozen dependencies and resource limits remain fixed.

Base contracts:

- R104 r1: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104.md`
- R104 v2: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104-v2.md`,
  SHA-256 `b2fcf0ba32a2c657d59d3e468da9f7308e4edf517f4eb256b86d3be581711752`.

## Final permitted Cargo call

R104 call 1/2 failed before tests because a test-only `Debug` format required
`CandidateGraphEffectOperand: Debug`, which is not implemented and is outside
the lease. Amend the call allocation: call **2/2 is the one corrected causal
observation invocation** after the edit below and a fresh independent review.
It consumes the final Cargo allowance whether compilation succeeds or fails.
No Rust test/build/retry/solver-repair verification may follow in R104.

The exact command remains unchanged:

```sh
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1 --show-output
```

## Exact repair and gates

Thaw only `crates/yu-solver/src/candidate_effect.rs` and the existing source
handoff path. Replace test formatting of `CandidateGraphEffectOperand` with an
explicit, non-semantic observation using existing accessors: node index, source
owner/position, permitted effects, origin identity, and optional tail node
identity. Resolve a tail index with the existing graph node identity check;
report absent operands and unresolved tails distinctly. Retain all four frozen
source hashes for the other files, fixtures, protected assertions, and every
field required to distinguish capture loss from fresh-use remapping loss. Do
not add a `Debug` derive or modify `shadow_apply.rs`.

Freeze the revised effect hash and sequential handoff revision. A fresh
independent reviewer must accept the delta and the protected observation
component before the final call. No call is allowed before that review. After
execution, a fresh receipt review records the complete logs, hashes, exit,
resource peaks and cleanup. The result establishes causal observations only;
it does not imply Rust source promotion, solver repair, or parent closure.

Preserve the 4,200-second aggregate envelope, original `/dev/shm` target, locked
offline command, CPU 0, 180-second timeout, 2 GiB RSS and 8 GiB target cap. Cargo
allowance before the final call is 1/2. No retries, new target, dependencies,
leases, semantic changes or budget increases are authorized.
