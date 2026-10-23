# CONCRETE-CALLBACK-PERMISSION-20261024 — outcome

Status: ACTIVE. Proof assignment has not started. The prior permission audit
identified callback-result correspondence as a major missing premise. This
outcome does not adopt the global permission candidate or close
`SOURCE-SAFETY-BRIDGE`.

Contract: `tasks/agent-loop/sprints/concrete-callback-permission-20261024.md`.

## Before state

The approved source behavior allows `relay(cb: () -> [signal] int)` to catch
`signal` from `cb()` and return `1`, while preserving additional `write`
effects. The source proof has a concrete-permission candidate, and the solver
retains `FormalPermission` metadata. The prior implementation audit did not
establish a bridge from that nested callback-result permission through runtime
program construction and receiving to the same callback invocation's request.

## Proof and implementation

Pending the leased source/runtime proof handoff and its independent review.
Production code remains unchanged at this checkpoint.

## Verification and remaining scope

No tests, builds, probes, source changes, or expected-output changes have been
run or made for this sprint. The previous integer-comparison `cargo check` and
review remain recorded in the prior sprint outcome. Wildcard/release adoption,
the computation-form relay, full source/native correspondence, and the original
Simple-sub A/B theorem remain open.
