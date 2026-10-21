# R219 — Repeated retained-loop source reachability

Status: bounded candidate-only source/native result, case-specific outcome C.
The original computation-forwarding theorem and R71 remain OPEN; no
independent review is claimed.

## Exact source and execution

The source keeps R72's `loop`, `direct`, and `helper` definitions and adds one
local `repeated (z:[io] int)` function whose body contains `my first = loop z`
followed by `loop z`. The outer body calls `repeated q`. The parsed source had
no structural recoveries, lowered successfully, and was admitted by public
ordinary-mode `CandidateInference::solve(hir)` without candidate solver errors.
The two `loop z` Apply occurrences are 18 and 21.

The test-only R148 trace recorded exactly two production `Work::Bound` events,
both immediately after their matching popped Bound work item. Their stored
intrusion-parent groups map to source checking ordinals 6 and 10, corresponding
to the unchanged direct `loop x` and helper-body `loop y` source calls. Neither
repeated `loop z` Apply owns a Work::Bound group. Every extrusion start has a
finish record.

The `loop` Lambda slot-4 admission reads back as
`BoundKey(Effect(EffectRow(5)), Negative, Effect(EffectRow(38)))`, physically
owned by `Effect(5)` in `EffectUpperRow[0]`. The complete intrusion forest log
replays exactly to the final Value and Effect snapshots. `Effect(38)` has no
Birth or ParentWrite in that log and appears in neither of the two Work::Bound
lookups. The final forest has 35 Effect rows, so the item is outside the
intrusion forest. This exact repeated-call source therefore does not realize a
third-owner merge followed by a later production Work::Bound copy of the
slot-4 item: outcome C for this source only.

The local-source observer returned one route for each repeated `loop z` Apply
with complete facts and origins, but marked its capture list truncated even
with a 4096-row cap. That is an observer limitation. The execution trace and
complete forest event replay establish the bounded negative result without
using those incomplete capture lists. No consumer obligation for a copy of
this item arises in this execution.

## Checks and limits

- Focused R219 exact-source test: passed (1 test).
- `RUSTC_WRAPPER= cargo test -q -p yu-playground`: passed.
- No semantic, production, sample, or expected-output changes; R218's
  test-only trace was reused.
- This is one additional source case. It proves no global reachability
  impossibility, does not close R71 or R72's global coverage, and does not
  discharge the arbitrary-prefix, simultaneous-receiver, foreign-continuation,
  semantic approval, or production obligations of the original parent.
