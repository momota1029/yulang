# LEAN-CALL-REQUEST-BOUNDARY-20261025/r2 — checked repair and composition

Status: **AUTHORIZED by the current primary after the r1 writer STOP receipt.**
Baseline: `4d15e26ff207993a8e9049fb21f754f219c0a273`, `research/simple-sub-intrusion`.
Original goal, semantic authority, unrestricted world/metadata quantifiers and
the dependency pins are unchanged from r1 (SHA-256
`b3113904ec188ab90455f2af0d702541ee6c50ce2c6a49e3919fcbff4bd90775`).

## Evidence and reason for revision

The r1 source failed its first Lean invocation on record-update indentation and
the `boundary_shift` induction. The author stopped at 04:38:04 UTC, with no
descendants or running subprocesses. Its source SHA-256 was
`abdce99f622337e229b08c74d96e6b732b493f0b8eed4482686998162d578b4f`;
the immutable handoff SHA-256 is
`a0f36ead2c88b5b0aec8e715059a5805e5a4710eeae5dab3e05cd98e3217bca0`.
That result is an unchecked candidate, not a mathematical counterexample.

This revision authorizes one primary-owned repair and composition pass, with
bounded development checks before a frozen certification check. It replaces
r1's first-compiler-error stop and three-invocation cap for the new pass only;
the failed receipt and charged author grant remain in the accounting. Routine
elaboration repairs stay inside this packet. A semantic counterexample, changed
dependency, authority question or exhausted envelope still stops the affected
work. The dispatcher's selected universal request-boundary outcome is retained.

## Required result

1. Repair and check the original partial/complete state equations and the
   request-specific exact-prefix theorem against the actual transitions.
2. Prove the length bound for **every** actual finite requesting-state prefix,
   so the public complete characterization does not assume its own bound.
   Completion is exactly `frames.length + 1`; requested states cannot step.
3. Compose this exact boundary with initial Call reachability, existing typing
   preservation, captured-continuation cancellation and response typing.
   The response is an explicit typed input; no source/native response existence
   or faithful metadata interpretation is inferred.
4. Check exact public signatures and axiom dependencies, concrete mixed-frame
   order/binder/observation falsifiers, then obtain fresh nonauthor review.

## Exclusive paths and resources

The primary takes over `CallRequestBoundary.lean` and its two generated outputs
only after the received writer STOP; it owns all r1 composition/query/receipt/
outcome paths. The r1 handoff and contract stay immutable. Additional exact paths:

- `notes/theory/lean/.lake/call-request-boundary-r1-failed.lean` (failed snapshot);
- `notes/theory/lean/.lake/call-request-boundary-r2-check.lean` (final query);
- `notes/theory/lean/.lake/call-request-boundary-r2-run.py` (bounded checker);
- `tasks/agent-loop/inbox/20261025-call-request-boundary-r2-verification.jsonl`;
- `tasks/agent-loop/inbox/20261025-call-request-boundary-r2-review.md`;
- `tasks/agent-loop/sprints/call-request-boundary-20261025-r2-outcome.md`.

The existing 1,800-second envelope is retained: r1 author 300 charged, primary
repair/composition 600, checks 240, independent review 300, integration 120,
contingency 240. Up to twelve serialized Lean development/final invocations,
120 seconds each, one process, `-j1 -M1024`, and 240 seconds aggregate actual
Lean time. Record complete streams, exit status, wall/monotonic times and all
source/import/output hashes. Final source must be checked after its last edit.
No Rust/test-suite/build-system change is authorized.

The user explicitly selects Astra subagents. For this session that supersedes
the default Sol reviewer routing: use one fresh Astra/medium nonauthor reviewer
after the old author has stopped, for at most 300 seconds. The cumulative Astra
reservation is 600 seconds (old author 300 plus reviewer 300); it is not reset.
Only one Astra child may run at a time. The current user-selected primary keeps
authority, leases and Git; historical "Luna" names do not establish its model.
Requested model/effort and observed telemetry remain separate.

## Review, implementation boundary and integration

Freeze both Lean sources, final query and receipt before fresh review. M1:
one independent proof/conformance reviewer; producer and repairing primary are
ineligible. Acceptance requires no holes/custom axioms, allowed axiom subset
`[propext, Quot.sound]`, exact arbitrary-prefix scope, all request cases, literal
fields and order, checked typed composition, and no unresolved major finding.
Minor elaboration repairs require only the affected delta to be rechecked.

`NO_SAFE_CODE_SLICE`: inspected native `runtime/machine.rs::return_value`,
`enter_template` and `runtime/receiving.rs::Receiving::delay` under
`tools/inference-playground/src/`. They retain actual response/template/view
owners, but a checked encoding between those owners and this formal Call state
is still missing. This sprint changes proof artifacts only. Force source
realization, raw Call coverage, source/native response authenticity, original
Call/inference A/B and production gates remain OPEN.

Integrate the reviewed coherent proof component with its immutable r1 failure
receipt, r2 verification/review/outcome and compact current state. Preserve all
three UNKNOWN quarantines and pending questions. Stage only explicit paths,
inspect the complete outbound range and push without forcing. No theorem status
is promoted until the independent review has been adjudicated.
