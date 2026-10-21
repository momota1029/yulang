# R216 — Capture reverse-owner bound readback

Status: COMPLETE, solo primary, source/code-path adjudication. No production edit.
Baseline: `26fde472d`; branch `research/simple-sub-intrusion`.

## Question

R215 observed `Effect(10)` absent from `effect_bounds[31].direct_lower_rows`.
Determine whether relation 71 is absent from solver bound storage or stored on
its other endpoint, and connect that physical owner to Capture's row walk.

## Exact scope

Read-only source paths:

- `crates/yu-solver/src/candidate_extrusion.rs`
- `crates/yu-solver/src/candidate_scheme.rs`
- frozen R213/R215 result records
- the already-built `local_source_observation` test binary

Write paths: this contract, `tasks/agent-loop/current.json`, and one result note
under `notes/theory/`. No solver behavior changes. No subagents per the user's
standing constraint; select this direct follow-up from R215's row-31 result.

## Evidence and decision

The filtered R187 `local_source_observation` test run reports relation 71 as
`Effect(10) <= Effect(31)`, with admission 64 and emission 61 at physical slot
`Effect(10), EffectUpperRow, index 0`; readback returns the same bound. In
`candidate_apply_effect`, equal-level rows select the lower endpoint as owner
with negative polarity. `candidate_insert_bound_with_evidence` stores a negative
row bound in that owner's `direct_upper_rows`. Thus the source relation exists
in solver bound storage; R215 checked only the complementary lower-row list at
Effect(31).

`Capture::expand_row` reads the visited row's own `direct_lower_rows` and
`direct_upper_rows`, then emits bounds. It has no reverse-owner lookup from a
visited upper row to other rows whose `direct_upper_rows` contain it. The
existing route therefore cannot discover the Effect(10) owner while walking
from Effect(31). This locates the candidate Capture omission at frontier
traversal/discovery, not source relation emission or initial bound storage.

This is candidate implementation evidence for one fixture. It does not close
the native theorem, source/native correspondence, independent review, semantic
approval or production gates. R215's interpretation is superseded by this
record; its raw Effect(31) snapshot remains accurate.

## Verification

The existing compiled test binary was run with the single
`local_source_observation --nocapture` filter and its R208/R211/R215 records
were extracted; it exited 0. Source inspection confirms the insertion and
Capture walk described above. No new behavior was tested because no code changed.

Next: design and implement a bounded incoming-owner frontier for Capture,
including accounting and source-bound evidence, then rerun the source-qualified
local-route test and re-evaluate the original gate separately.
