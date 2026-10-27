# Sprint FORMAL-PERMISSION-PROJECTION-20261028/r3

Status: ADMITTED — source read-back correspondence only
Baseline: `42e31a76658d744c7b7ecf39eae8bd1856450ee5`
Parent: full Yulang inference/executor soundness; r1/r2 effect-permission
projection sub-obligation. Preserve the original successful-path endpoint-image
claim and all source/native, A/B, effect-hygiene and quantifier scope.

## Fixed outcome

Establish or falsify the first missing premise from r2: successful read-back of
the original live Effect term, positive/negative Function terms, and ordered
Tuple elements. Trace the actual `InferenceSession` wrappers through term
construction, interning, lookup and `TermNode::view`. Distinguish fresh
allocation from interning hits; include arena/brand/handle validity and any
mutation or rollback boundary that can affect the same successful call.

Apply only established equations to r2's conditional derivation and report the
first remaining premise. A mismatch is a falsifier only if construction and
same-branch read-back both succeed and the returned kind, polarity, ordinal,
Function field or Tuple order differs. Stale/invalid-handle errors require
lifecycle analysis and are not automatically counterexamples. Do not assume
the endpoint-image result, change semantics, edit Rust, or bridge/repair Lean.

## Authority, inputs and exact ownership

Primary owns the contract, current state, adjudication and Git. One read-only
`researcher` may inspect exactly these owners, whose committed bytes match the
admitted baseline:

| Owner | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07` |
| `crates/yu-solver/src/term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |

Frozen predecessor: r2 contract
`34cd037c944d067b94b3ab89aadbf7cdeb2153bb3afcd48fbd2d497f58ef0877` and
handoff `f4a3ca3491d36e35e1d066aeafbe0e17f672e90014eeeb063b0cc6ca8a42b8d2`.
The independent r1 review is
`tasks/agent-loop/inbox/formal-permission-projection-20261028-review.md`,
SHA-256 `a64d9bafde670a2c6e580741c8fc94e58b8d4b417c6e2768330ebf505f868203`.
Retain r2's conditional map and the independently reviewed r1 finding; this
packet does not reopen their semantics or claim proof closure.

Exact write lease: `tasks/agent-loop/inbox/formal-permission-projection-20261028-source-r3.md`.
No other writes, descendants, Cargo, Lean/Lake, tests, probes, network or Git.
Keep unknown runtime diffs and all quarantined paths untouched. No new source
owner may be opened: identify it as the exact next missing dependency and stop.

## Runtime, review and stop conditions

- Role: registered `researcher`; requested model/effort are registered defaults;
  record actual observations as UNKNOWN unless runtime evidence supplies them.
- Budget: at most 200 seconds, one CPU, 1 GiB RSS; no renewal or descendants.
- Success: source-qualified read-back equations and an explicit reduction (or
  falsification) of r2's first missing premise, with exact locations and hashes.
- Freeze the handoff, then assign a fresh non-author `compiler_referee` to review
  only this result and its pinned owners before any Lean bridge is admitted.
- Stop on hash mismatch, need for another owner, missing equation, budget bound,
  or falsifier. Parent, theorem, native and production gates remain OPEN.
