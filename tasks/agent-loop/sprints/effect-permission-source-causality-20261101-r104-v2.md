# R104 v2 bounded Rust observation amendment

Status: **ADMITTED** under the standing Rust/Lean goal. This is a narrow,
versioned amendment to R104 r1, not a replacement for its parent objective,
source semantics, leases, proof obligations, or resource envelope.

Base contract: `tasks/agent-loop/sprints/effect-permission-source-causality-20261101-r104.md`,
SHA-256 `0f70cfbcbe18c74c2b1b6aa0130fc425261c916d2418b4e6e10251568a9357dd`.
R104 v1 pre-execution review receipt is recorded in
`tasks/agent-loop/history/effect-permission-source-causality-20261101-r104-outcome.md`.

## Authorized delta

Authorize the Rust test harness option `--show-output` so successful test
observations are retained in the complete execution log. The one exact
permitted command for either remaining Cargo call is:

```sh
cargo test --locked --offline -p yu-solver --features shadow-apply-candidate candidate_effect::tests:: -- --test-threads=1 --show-output
```

This changes only output capture. It does not relax assertions or change solver
semantics. Cargo remains **0/2 spent**; preserve all r1 limits, including one
CPU, 180 seconds, 2 GiB RSS, the unique `/dev/shm/yulang-effect-permission-source-causality-20261101-r104-target`
target capped at 8 GiB, offline/locked execution, and no retry, download,
fallback, or ext4 build target. Charge elapsed work already performed to the
original 4,200-second aggregate envelope; no budget resets.

## Exact repair packet and gates

After the source worker acknowledges the rejection and Luna explicitly thaws
the existing lease, the worker may write only the same four Rust owners and one
handoff path listed in r1. Required delta:

1. In the no-source-row branch, replace the invalid `row.position` observation
   with `context.position()` and an explicit `row=None` field. Keep all other
   source/action/error identities and branch polarity.
2. Complete fresh-use Support remapping evidence. Join each route's use/provider
   identity, captured Support template node index, original view, retained
   `effect_operands` entry, mapped endpoint/tail and live bounds. Reuse the
   existing `FreshRoute.retained` observation and the existing
   `prepare_candidate_fresh_use` remap; record missing or inconsistent entries
   explicitly. Do not change solver behavior or infer a loss from row mappings
   alone.
3. Freeze all four source hashes and the sequential handoff revision. A fresh
   independent reviewer must accept the complete relevant component and all
   three prior findings before Cargo. No call is spent before that review.

After review, stage 1 may run once. A demonstrated owner-local cause in the
already leased effect/scheme owners may proceed to repair, independent review,
and the single stage-2 verification call. Any outside owner, unsupported
semantic need, missing causal edge, review rejection, or resource/cleanup
failure stops before the next call and returns to Luna. All R1 protections,
leases, original fixtures/assertions, parent theorem obligations, UNKNOWN
workers, and quarantined paths remain unchanged.

## Lean disposition

The R104 Lean candidate and its independently reviewed successful one-call
receipt are accepted as the bounded flattened syntax checkpoint. No second
Lean invocation, source-owner bridge, source/native conclusion, or parent
theorem closure is authorized or implied by this amendment.
