# CALL-REQUEST-BOUNDARY-PRIMARY / handoff revision 2

Sprint: LEAN-CALL-REQUEST-BOUNDARY-20261025/r2; contract SHA-256
`b92747b9e519be2f9f3c14c01db0f1353a0a3ea461fb8633b0d25eb2ff27896f`.
Baseline: `4d15e26ff207993a8e9049fb21f754f219c0a273`.
Author: current primary `/root`, following the acknowledged r1 Astra STOP.
Original constructive coauthor: `/root/call_request_boundary_astra_r1`.
No descendants; observed primary model/effort UNKNOWN. Review is pending.

## Result and parent application

The failed r1 source has been repaired at its record syntax and induction step.
`call_request_prefix_iff` now proves, for arbitrary `n`, exactly
`Prefix n s t ↔ n ≤ frames.length + 1 ∧ t = requestBoundary md n s`.
The bound follows from the actual request transitions: `n + rank(t) = rank(s)`.
It is not an input assumption. Partial state equations preserve literal
remaining frames and observation fields; completion exposes the ordered
world/scope fold and captured continuation. `call_request_completion_iff`
characterizes the exact completion time; `call_requested_no_step` excludes
further represented Call transitions from a requested head.

`initial_call_request_boundary_response` constructs the actual complete prefix
from a reachable requesting state and applies existing typing preservation and
terminal inversion. An explicitly typed response yields a typed substitution
of that actual captured continuation, equal to plugging the original frames.
`actual_call_request_completed_response` applies the same result to every
actual completed trace, even when its terminal operation and continuation were
initially unspecified.

This removes the gap between existential request unwind and universal exact
boundary/response composition for the existing formal Call transitions.
Force source realization, raw successor coverage, actual source/native response
authenticity, original Call/inference A/B and production remain OPEN.

## Frozen sources and checks

| Artifact | SHA-256 |
|---|---|
| `CallRequestBoundary.lean` | `28ffc2943c18d324c35dacf18b4dd70921d4cc462ffd6ffdce989475ef46cce6` |
| `CallRequestBoundaryComposition.lean` | `fed00f06cdbf2a5bdc1b3c18957acc33c7b281e890f277ca5bd1d20ece53ee76` |
| `.lake/call-request-boundary-r2-check.lean` | `8595e7b81d9a495604166380659a6474bb60737658f6625237f74e306498bbb3` |
| r2 verification JSONL | `4df963ddb36e55246ef204a67f676633e26b2c0da3c4bb8782adcd8c7a53062d` |

Five serialized r2 Lean invocations consumed 2.203071898 seconds. Rows 2, 4, 5
are the final boundary source, final composition and signature/axiom/falsifier
query: all exit 0, no timeout or warning. Row 1 checked the intermediate repaired
boundary; row 3 recorded the composition's initial projection-simplification
error, corrected before row 4. The r1 failure receipt remains immutable.

The final query checks ten public signatures, all with only `[propext]`, and
fifteen kernel-checked examples discriminating mixed frame order, binder
lifting/index, noncommuting metadata order, effect/result identities, completion
time, observation and literal suffix preservation. The JSONL embeds each exact
source/query and full streams, plus input/output hashes and timing. All final
hashes were rechecked against the worktree. No broad test, Cargo, runtime or
source-semantic change ran.

Sources, generated outputs and final query/receipt are frozen for fresh
independent review. The primary wrote only the r2 leased proof/record/scratch
paths; the original author's handoff is unchanged. Next action: reviewer checks
the original universal scope and actual constructor/typing correspondence;
primary adjudicates before integration. No author certifies its own result.
