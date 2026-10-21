# R218 — Exact R72 source execution and owner trace

Status: bounded candidate-only source/native result; the original
computation-forwarding preservation theorem and parent R72 gate remain OPEN.
No independent review is claimed.

## Fixed source and ordinary execution

The unchanged source in `tasks/agent-loop/sprints/third-owner-prefix-20261019-r72.md`
was parsed and lowered without structural recovery, then passed through public
ordinary-mode `CandidateInference::solve(hir)`. It produced no candidate solver
errors. The four relevant source Applies were `loop x` at occurrence 6,
`loop y` at occurrence 10, `helper x` at occurrence 13, and `loop q` at
occurrence 16.

The complete test-only execution trace recorded 1,506 candidate events, 2
production `Work::Bound` lookups, 4 row merges and 3 bound transports. Every
started extrusion finished; queue-pop order was retained. Both `Work::Bound`
families joined through their stored intrusion-parent groups and source
checking events to the exact inner source Applies:

- occurrence 6 (`loop x`): the raw lookup was
  `BoundKey(Effect(EffectRow(9)), Positive, Effect(EffectRow(18)))`, copied to
  owner `Effect(21)`;
- occurrence 10 (`loop y`): the raw lookup was
  `BoundKey(Value(ValueRow(20)), Positive, Value(IntPositive))`, copied to
  owner `Value(22)`.

The ordinary `loop q` observation is complete and identifies the retained
`loop` Local route. Its Lambda slot-4 source relation is 87, with raw bound
`BoundKey(Effect(EffectRow(4)), Negative, Effect(EffectRow(29)))`. The
constructor readback identifies physical owner `Effect(4)`, lane
`EffectUpperRow`, index 0. The exact Local route maps it by a `FreshUse`
transport to
`BoundKey(Effect(EffectRow(38)), Negative, Effect(EffectRow(34)))`; the source
relation lineage records six replay children and that transport.

The full intrusion forest event log is complete and replays exactly to the
final Value and Effect snapshots. `Effect(29)` has no Birth or ParentWrite in
that forest. The complete extrusion trace has only the two Work::Bound events
above, neither of which mentions `Effect(29)`. Thus this exact source does not
instantiate the requested slot-4 third-owner, alias-changing-merge, later
Work::Bound-copy pattern. This is case-specific outcome C, not a general
impossibility claim. Since there is no such later copy, no corresponding
consumer obligation for that copied relation arises in this execution.

The public local-source observer returned complete observations for `helper x`
and `loop q`. It returned `ArtifactMismatch` for `loop x` and `loop y`; those
missing route records are an observer limitation. The independent execution
trace still joins both actual Work::Bound parent groups to their source
checking occurrences, and establishes the negative result above without
assuming those missing observer fields.

## Checks and limits

- Focused R218 exact-source test: passed (1 test).
- `RUSTC_WRAPPER= cargo test -q -p yu-playground`: passed.
- Full `yu-solver` library suite: not rerun; the earlier R217 attempt stalled
  after failures and is not evidence about this bounded source case.
- No semantic or production behavior changed. Instrumentation is under
  `#[cfg(test)]`.
- The parent theorem retains its original quantifiers, arbitrary-prefix,
  repeated-call, simultaneous-receiver and foreign-continuation obligations.
  R71/R72 global coverage, semantic approval and production gates remain open.
