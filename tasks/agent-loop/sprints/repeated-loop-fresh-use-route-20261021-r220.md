# R220 — Trace repeated-loop Local FreshUse bounds

Status: CLOSED, bounded candidate-only source/native lineage result; Luna solo
primary, no independent review.
Baseline: `6dc402afca4d0cdb8a2f26815477fa50c9481c7e` on
`research/simple-sub-intrusion`.

## Parent and target

Continue the unchanged computation-forwarding preservation theorem and R71
raw/canonical fiber obligation. R219's exact repeated-call source was admitted
and classified C for the third-owner/merge/later-Work::Bound pattern, but its
Local capture observation truncated. Trace the two actual `loop z` Local route
bounds from that exact source through their relation lineage to the Lambda
slot-4 source admission. Determine the exact mapped FreshUse bound and whether
any later production consumer uses it.

Success is an occurrence-specific source -> physical slot -> Local route row
mapping and relation/provider lineage, joined against the complete Work::Bound
and intrusion-forest traces. If current retained artifacts do not support that
join, record the exact observer gap. No inference from the truncated capture
list or final state alone. This remains a candidate-only result; R71, global
R72, theorem and production gates remain OPEN.

The exact route result is recorded at
`notes/theory/2026-10-21-r220-repeated-loop-fresh-use-route.md`. Both FreshUse
images are identified, but no later production Work::Bound consumes either
image item in this source.

## Exact write paths and checks

- `crates/yu-solver/src/shadow_apply/local_source_observation.rs`
- this contract
- `notes/theory/2026-10-21-r220-repeated-loop-fresh-use-route.md`
- `tasks/agent-loop/current.json`

Add one read-only focused test using the exact R219 source. For each source
`loop z` Apply, join the existing local-source observation route to
`solved.local_routes`, find the exact slot-4 bound, map both row endpoints
through the physical route rows, and inspect `test_relation_lineage` for the
FreshUse transport. Keep the observer truncation fact explicit. Relate the
result to the complete production Work::Bound trace and forest replay already
checked by R219. No new tracing hook or semantic/production change.

Run the focused R220 test, then the ordinary `yu-playground` package tests if
the route is interpretable. Finish with sprint state check, tooling unittests,
`git diff --check`, byte limit, explicit-path commit and push. 600 seconds,
no carryover. No subagents or independent review claimed.
