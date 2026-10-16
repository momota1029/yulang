# Frozen carrier inventory repair handoff

- Sprint: `catch-matcher-introduction-and-call-bijection-20261017`.
- Contract rev4 SHA-256: `812f7f44e433a836a8b8dd8fa69353e3d7ed45eaad45285e4e0490b8597fe95e`.
- Assignment: `primary-catch-call-carrier-repair-20261017`, revision 1.
- Author: `/root` (Luna primary); selector-authorized same-sprint repair.
- Requested model/effort: Luna/high. Observed effective model/effort: UNKNOWN.
- Budget: 120 seconds from reserve, fully charged conservatively; reserve reduced
  from 180 to 60 seconds. No Cargo/build/test/run used.

## Finding and repair

The rev3 pre-run reviewer found that `source_carrier_outcomes()` omits opt-in
binding `LocalSource` values: `lower_module_with_local_source` stores these in
`local_sources`, while `local_source_for` falls back to that map. The original
inventory therefore missed the `result` binding's three Apply sites and would
stop before solve.

The repaired inventory now unions:

1. supported entries in `source_carrier_outcomes()`, resolved back through
   `local_source_for` and checked for pointer identity; and
2. every HIR binding's `local_source(definition_root)` result.

Both paths check authentic source-root ownership. Duplicate roots must resolve
to the same LocalSource object and are retained once. Every retained expression
still must have an exact HIR source key owned by the parse. Every Apply resolves
its authentic callee and argument indices. The full per-Apply / CandidateSourceCall
bijection, owner/source/operand identity, checking-occurrence/cause consistency,
and explicit partial-HIR diagnostic guards remain unchanged.

No source owner is selected by spelling. Unavailable binding LocalSource values
are skipped only when the HIR API returns `None`; availability errors stop the
example. Unmatched/extra Apply or CandidateSourceCall records remain fatal.

## Scope and evidence boundary

The changed/created paths are the exact example and this repair handoff, plus
the primary-owned frozen pre-repair snapshot below. The original implementation
handoff remains immutable. The exact pre-repair example is preserved at
`tasks/agent-loop/snapshots/20261017-catch-call-bijection-pre-carrier-repair.rs`
with SHA-256 `dfb67257941f628faa2c3c9f31504cedb5c53d8f12e25e08466ff3f8a71f933f`.

This repairs static inventory completeness for supported LocalSource carriers;
it does not claim source acceptance, full source representation, source typing,
handler adequacy, runtime semantics, or parent theorem progress. Both prior
`UnsupportedItem` and `UnsupportedExpression` diagnostics remain required and
printed. `CATCH-EXIT-INPUT-1`, F1/FK1, and every downstream parent remain OPEN.

The author stopped after freezing this handoff and the example. Fresh
independent pre-run review is required before Luna may use the one unused
feature-enabled Cargo invocation (120 seconds, no retry). No descendants,
scratch paths, tests, builds, Cargo, Git, or network activity.
