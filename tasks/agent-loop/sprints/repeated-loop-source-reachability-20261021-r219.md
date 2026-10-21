# R219 — Repeated retained-loop source reachability

Status: CLOSED, bounded candidate-only source/native outcome C; Luna solo
primary, no independent review.
Baseline: `b47a9425bd556bf4c97f591a800650a1c0f77324` on
`research/simple-sub-intrusion`.

## Parent and exact outcome

Continue the unchanged computation-forwarding preservation theorem and R71
raw/canonical fiber obligation. R218 established case-specific R72 outcome C
for its fixed source. This packet tests one distinct, source-derived repeated
call case, because repeated calls are explicitly in the original parent.

Use the R72 source unchanged except add a second distinct local initializer
`my again = loop q` after `my first = loop q` in `outer`. Keep the inner `loop`,
`direct`, and `helper` definitions unchanged. Run this exact ordinary source
through public `CandidateInference::solve(hir)`. Determine from source-qualified
parents and the complete intrusion forest whether the second retained Local use
causes the loop Lambda slot-4 item to enter a third physical owner, merge through
an alias-changing representative transition, and later be selected/copied by a
production `Work::Bound`.

Outcome A requires the actual owner/slot, raw and canonical keys, source
occurrence, event order, exact consumer and provider lineage. Outcome C means
the exact repeated-call source is admitted and its bounded relevant trace is
complete, but this pattern still does not arise. No general impossibility or
parent closure follows. Do not manufacture rows, combine fixtures, or infer
history from final state.

The result is recorded at
`notes/theory/2026-10-21-r219-repeated-loop-source-reachability.md` and is
outcome C for this exact source. The slot-4 item never enters the complete
intrusion forest or either production Work::Bound lookup. The original parent
and global R71/R72 coverage remain OPEN.

## Exact write paths and method

- `crates/yu-solver/src/shadow_apply/local_source_observation.rs`
- this contract
- `notes/theory/2026-10-21-r219-repeated-loop-source-reachability.md`
- `tasks/agent-loop/current.json`

Use only `#[cfg(test)]` tracing already added in R218. Add one focused test for
the exact source above; assert the two `loop q` HIR occurrences, public ordinary
solver entry, successful extrusion start/finish balance, work-item ordering,
source-qualified Work::Bound groups, complete alias-forest log and exact replay
to its final snapshot. Read the loop Lambda slot-4 admission/physical slotback
and record whether its item ever appears in the forest or a later Work::Bound.
No semantic or production changes, additional instrumentation, source fixture
mutation, playground edits, or expected-output changes.

Run the focused test first, then `RUSTC_WRAPPER= cargo test -q -p yu-playground`
if the source is admitted and the trace is interpretable. Finish with
`python3 tools/agent_sprint.py check`, tooling unittests,
`git diff --check`, compact-state size validation, and clean commit/push.
600 second hard cap, no carryover; one heavy test process at a time.

R71 and the original theorem, semantic approval, and production gates stay
OPEN. Solo primary work is intentional; no independent review is claimed.
