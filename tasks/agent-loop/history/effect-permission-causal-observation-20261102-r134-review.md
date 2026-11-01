# R134 independent review receipt

Verdict: **PASS for the exact two-file causal-observation candidate, with one
MINOR handoff correction.** No blocking or major source finding.

Reviewer: `/root/r134_causal_observation_review` (`compiler_referee`), read-only,
STOPPED. Contract SHA-256:
`3f0c46ccdf98c5999ade532cea73f07dca0d755ce4307f350375166c2a99a321`.
Admission SHA-256:
`4b71d593042b2ae837af9e300502e4bb9f314451f789f7121c9ab194e116d22b`.
Frozen handoff: 27,796 bytes, SHA-256
`50e61dc61cd7fc377db08f9ed9179d9e0f500cbbab87820b9e4cd83e8c4b8244`.
Both reconstructed targets, baseline hashes, byte counts and the recorder
hash independently match the contract.

## Accepted bounded findings

The exact hunks preserve solver calls, call counts, return values, assertions
and diagnostic payloads. Copied endpoints, frame and owned action avoid
extending session borrows across mutation. Observation closures run only when
the test recorder is enabled; disabled recording skips formatting, clones and
error iteration. No new dirty observer, scheme adapter or shadow hook is used.

Source-action `after` follows only successful `execute_candidate_action`.
Effect-constraint and propagation `after` events record completed calls,
including `Err`, while preserving the original result. Diagnostic events occur
only after insertion.

## Minor handoff correction and coverage limit

The frozen handoff says test builds without `shadow-apply-candidate` retain the
source-action trace. This is inaccurate: `candidate_source` itself is gated by
that feature in pinned `lib.rs:212–213`, so all new observations are absent
without it. The primary records this correction; the frozen handoff remains
unchanged.

The source-action trace also omits pre-existing early paths for `Install`,
`LocalAnnotation`, publication, suspension and schedule completion. This is a
bounded coverage limit, not a defect in the authorized patch, and it does not
support causality claims for every source-driver failure.

## Limits

Static review only. No compiler, Cargo, tests, Lean, checker, scratch,
environment probe or build output. The result closes no parent proof,
source/native correspondence, consumer, effect-hygiene or production gate.
