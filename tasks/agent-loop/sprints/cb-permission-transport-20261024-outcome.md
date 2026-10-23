# CB-PERMISSION-TRANSPORT-20261024 — outcome

Status: ACTIVE. Contract is frozen; the proof assignment has not started.
No implementation or theorem closure is claimed.

Contract: `tasks/agent-loop/sprints/cb-permission-transport-20261024.md`.
Baseline: `a0dcc92b8f8b866f7ed2e06acf399a4c86057a3c`.
Prior reviewed obstruction: `notes/theory/2026-10-24-callback-permission-bridge.md`,
SHA-256 `c228ff45a272a52b92eaaccd91183272438bb8c3287dd39e7749d700ce919f4d`.

## Objective

Construct the runtime evidence missing from the prior reviewed callback trace:
the source formal's nested `[Result]` permission must reach the actual
receiving relay invocation, remain authentic through callback Result
execution and the post-unwind `OperationResultConsumer`, then grant the
matching request to the Catch owned by that same relay invocation.

The proof must preserve annotation/formal/occurrence/row/path/family identity,
the request event and view/port, plus distinct callback-call, operation and
handler owners. It must cover bubbling, delimiter unwind, discard and replay.
The proof is the gate for any runtime write.

## Before state and boundaries

Candidate construction retains the concrete permission at `[Result]` over an
open inflow port. The reviewed runtime has no matching callback-result view;
the operation invocation ends before the request consumer runs under the
restored relay owner. The prior sprint closed as
`NO_SAFE_CODE_SLICE`; this sprint changes method by constructing the missing
transition and frame invariant, not by repeating an absence audit.

The approved callback result `1`, open input row and residual `write`
requirement are unchanged. No wildcard/scoped-release semantics, computation
thunk behavior, arbitrary callback coverage, original A/B closure or
`SOURCE-SAFETY-BRIDGE` closure is claimed.

## Lanes and verification

The bounded proof worker owns only its contract's two new Markdown paths and
must stop before code changes. Luna owns the three existing runtime paths,
gated on fresh independent review of the frozen construction. A later fresh
review covers the implementation.

No tests, builds, probes, Git operations or code writes have run in this
sprint. Following accepted code and review, the contract permits one Cargo
check as compile evidence. All original source/native obligations and the
broader inference/evaluator goal remain open.
