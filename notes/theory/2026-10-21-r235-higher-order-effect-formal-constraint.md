# R235 — Higher-order formal effect boundary

Date: 2026-10-21. Status: unreviewed candidate-path implementation result.
Branch: `research/simple-sub-intrusion`. Sprint contract:
[`higher-order-effect-formal-constraint-20261021-r235.md`](../../tasks/agent-loop/sprints/higher-order-effect-formal-constraint-20261021-r235.md).
Original Simple-sub, R71/R72, semantic approval, independent review and
production gates remain OPEN.

## Finding

At the source call `accept bad`, the ordinary candidate solver generated the
four FunctionPort children for the nested callback comparison. The result
effect child was present, but the negative concrete formal port had no
`Allowance` bound carrying its declared `[io]` set. In
`candidate_formal_effect_port`, the negative concrete branch created a fresh
effect row and retained only a `FormalPermission`. That permission preserves
the formal's local handling role; by itself it does not constrain a supplied
callback. As a result, `bad : int -> [state] int` passed an
`accept (f: int -> [io] int)` formal, whether `f` was unused or called.

The source HIR retained `[io]` on the formal. The missing boundary was in the
candidate constructor. The direct top-level annotation control already
rejected the same `[state]`/`[io]` mismatch.

## Bounded repair

The negative concrete formal-effect branch now creates a source-owned effect
view from the retained concrete row and attaches `Allowance(view)` to the
negative effect port. It still records the existing `FormalPermission` and its
typed path. Constructor-generated Function/Effect comparison then carries a
supplied callback's effect into that allowance and reports the ordinary
`IncompatibleEffect` conflict. No source-form-specific rejection was added.

The ordinary CLI regression covers a direct annotation control, unused and
called higher-order formals, an inline incompatible callback, and a compatible
`[io]` callback. A solver source-route test confirms the outer Apply retains a
Name argument and reaches the effect conflict consumer.

## Verification and limits

- `cargo test -p yu-playground` — passed.
- Focused solver source-route test — passed.
- Focused `cli_higher_order_effect_mismatch` — passed.
- `npm run check` in `web/playground` — passed; inference and all embedded
  execution, Yulang2 identity and diagnostic smoke cases passed.
- `python3 tools/agent_sprint.py check` — passed.
- `python3 -m unittest discover -s tools -p 'test_agent_sprint.py'` — 57 passed.
- `git diff --check` — passed before final record synchronization.

The full `yu-solver` library test run did not complete cleanly: two
candidate-context resource-accounting assertions failed, and a serial run
stalled in `queued_relation_equality_transport_retains_context_ancestry_and_retry`.
Those outcomes are unresolved and are not presented as caused by or unrelated to
this repair. The targeted regression and playground suite pass; full solver
suite status remains open.

This is solo, unreviewed candidate work. It does not prove source/native
completeness, the original Simple-sub theorem or computation-forwarding. No
production cutover or parent-gate closure follows.
