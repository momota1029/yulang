# Sprint R197 — R187 intrusion merge/source readback

Status: CLOSED, primary-only provisional source readback; parent open.
Branch / baseline: `research/simple-sub-intrusion` / `02bd5b44d1b89e4e2f81bafac44d8b4155f74905`.
Authority: unchanged computation-forwarding preservation parent §§1, 6–7; exact R183/R196 frontier premise. No theorem narrowing or production authorization.

## Outcome

Determine whether the existing R187 `bridge`/`relay` local-call fixture actually
contains a retained intrusion copy/merge whose final representative owns one
of the captured bounds, and whether retained intrusion `source_events` join
that reclassification to authentic source checks. This directly tests the
successful source-history case left open by R196.

Success evidence: enumerate final intrusion parent/copy representatives,
target/polarity, source-event/checking occurrence joins, then intersect those
with exact local Capture owner keys and their final local flags. State whether
the fixture contains the merge transition and whether the available records
cover its causal order/source admission. A mere parent count or row-key match
does not qualify. The universal parent remains open unless a full source chain
is established.

## Exact boundary

Read-only inputs are the R187 fixture/readback, R195 Capture frontier, R196
transition audit, and the pinned `candidate_intrusion.rs`, `candidate_source.rs`,
`candidate_scheme.rs`, `shadow_apply.rs`, and local observation code; record
their hashes in the outcome note. No source edits, tests, or new observer. One
bounded offline Cargo readback may use only `target/r197-merge-readback/` and
must be removed at closeout. Do not retry Cargo after an invocation failure.

Exact durable writes: this contract, `tasks/agent-loop/current.json`, and
`notes/theory/2026-10-21-r197-intrusion-merge-readback.md`. No other dirty file
may be edited or staged. No subagents or independent review under the user's
explicit solo-work rule. Budget 600 seconds, one Cargo process maximum, no
carryover. Preserve original parent/A/B, source/native and production gates as
OPEN.

## Outcome and closeout

The R187 fixture retains four settled intrusion parents tied to source event 0
at bridge-to-outer occurrence 9. The effect and value copies merge into shared
Capture rows Effect 9 and Value 9, while later local relay rows Effect 29 and
Value 12 point to those shared rows. This proves that the fixture contains a
mixed Capture boundary after a source-associated merge. It does not provide
the full three-edge frontier witness: the shared-owner return edge and second
same-owner edge are not joined, and shared rows are not expanded. Capture
coverage gaps remain. Full hashes and joins are in
`notes/theory/2026-10-21-r197-intrusion-merge-readback.md`.

The one offline Cargo readback succeeded. No source edits or tests occurred.
R197 used 180s of its 600s allocation; the remainder expired without
carryover. Scratch was removed. Solo primary; no independent review. Original
parent/A/B/source-native/production gates remain OPEN.
