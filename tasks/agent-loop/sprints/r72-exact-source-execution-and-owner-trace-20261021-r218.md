# R218 — Execute the fixed R72 source and trace its owner path

Status: CLOSED, bounded candidate-only source/native outcome C; Luna solo
primary, no independent review.
Baseline: `301a714b2243ea12ed668010355f40efeccc394c` on
`research/simple-sub-intrusion`.

## Original parent and outcome

Continue the unchanged computation-forwarding preservation theorem in
`notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7,
including its shared assignment, original current-formal identities, whole
Name arguments, arbitrary finite prefixes, repeated calls, simultaneous
receivers, and foreign-continuation obligations. R72's fixed
`outer/loop/direct/helper` source and A/B/C outcome are preserved from
`tasks/agent-loop/sprints/third-owner-prefix-20261019-r72.md`.

Run that exact source through public ordinary-mode
`CandidateInference::solve(hir)` and produce a source-qualified account of the
actual helper Local/FreshUse route, relevant effect bounds, physical owners,
canonical aliases, and any subsequent production `Work::Bound` records and
consumer obligations available in current instrumentation. Identify the first
remaining premise from actual records. A failed solver run is not B unless an
authentic source constructor rejection is identified. A missing observer field
or incomplete trace is not C. Do not combine fixtures or manufacture rows.

The durable result is at
`notes/theory/2026-10-21-r218-r72-exact-source-execution.md`. The exact source
was admitted; its complete bounded trace contains no Work::Bound copy of the
fixed slot-4 item and no intrusion-forest birth or parent write for that item.
This is R72 outcome C for this case only. The theorem, source/native completion,
R71 coverage, global R72 coverage, semantic approval, and production gates
remain OPEN.

## Exact write paths

- `crates/yu-solver/src/shadow_apply/local_source_observation.rs`
- `crates/yu-solver/src/candidate_extrusion.rs` (test-only work-item trace label)
- this contract
- `notes/theory/2026-10-21-r218-r72-exact-source-execution.md`
- `tasks/agent-loop/current.json`

Baseline SHA-256 for `local_source_observation.rs`:
`2e9dbc67dbe7408e9e642128ae5c355e813e5533bc15657694fc7219bc716e7f`.
Baseline SHA-256 for `candidate_extrusion.rs`:
`7bdf566f6a2e6298aa1559f7af9c59e9efc66114ad631d03c2f924b42f60dace`.
R217 Capture implementation remains frozen and is read-only input.

No subagents, semantics, production code, expected-output changes, scratch
inside the repository, or changes to R72's source are authorized. Luna owns
the exact writes, interpretation and Git. Runtime/model observations for any
nonexistent worker remain UNKNOWN. Independent review is unavailable and will
not be claimed.

## Method and bounded verification

Add one focused regression/observation test using the exact R72 source. Assert
ordinary public solver entry and exact syntax/HIR occurrences; print bounded
route/bound/lineage evidence using existing read-only accessors. Add
`#[cfg(test)]` R148 trace labels that attach the already allocated extrusion
occurrence, initial endpoint, polarity, target level, and active processing
relation to extrusion start/finish and each popped Work item. This must not add
semantic work or affect solver order. Join each Work item to its stored
intrusion-parent group, source relation, and source checking event. Verify
successful start/finish balance and retain queue-pop ordering. Do not infer
full event history from final state. If current accessors cannot identify a
required transition, record that precise gap and keep the parent open.

Run only the focused R218 test first. If it passes and the source route is
complete enough to interpret, run `RUSTC_WRAPPER= cargo test -q -p yu-playground`
to protect the user-visible samples. Do not retry a stalled heavy solver suite
in this sprint. Check `python3 tools/agent_sprint.py check`, the tooling unittest
suite, `git diff --check`, and the compact-state byte limit before commit/push.

One heavy test process at a time; one attempt; 600 seconds total, no carryover.
Stop at a precise constructor/observer limit, a source counterexample, or the
bounded result. Apply the evidence to R71/R72 without changing either contract.
