# R256 — current tuple source-to-runtime obstruction

Status: primary-only read-only source audit. No compiler edits, tests, builds,
sample executions, subagents, or gate closure.

## Parent and outcome

The unchanged R149 Types example requires `pair: (int, str)` and the payload
`(42, Yulang)\n`. R253/R254 add provisional native ordered Tuple terms and
live indexed comparison, but the parent also requires source admission,
candidate inference, retained scheme transport, runtime evaluation and public
type output. R168 remains an unreviewed construction/consumer matrix; this
packet grants no code lease.

Outcome: inspect the current exact owner path after R254, locate the earliest
Tuple refusal and enumerate later consumers that must be implemented before
the Types example can pass. Keep the original sample and output unchanged.

## Exact scope

- Baseline: `93daff511` on `research/simple-sub-intrusion`.
- Governing source map: `notes/theory/2026-10-20-r168-ordered-tuple-construction.md`
  (SHA-256 `c88ce484dd1a6456f4e29cfcd932438db9ef6579f30584bc826aab9e4975a886`).
- Governing sample: `notes/design/2026-10-20-r149-types-console.md`
  (SHA-256 `1644743185363d3c258c606a2e65245b3db8206dddeb666d2994e2471d74f7fa`).
- Read-only owners: `yu-hir/module/local_source.rs`, `yu-hir/module.rs`,
  `yu-solver/candidate_source.rs`, `candidate_value_graph.rs`, `term.rs`,
  `lib.rs`, `candidate_scheme.rs`, `shadow_apply.rs`, `yu-types/lib.rs`,
  `runtime/program.rs`, and `runtime/machine.rs`.
- Output paths: this contract, `notes/theory/2026-10-21-r256-tuple-source-runtime-obstruction.md`,
  and `tasks/agent-loop/inbox/20261021-r256-tuple-source-runtime-result.md`.
- Budget: 420 seconds, charged in full, no carryover.

## Boundary

LocalSource's ordered tuple carrier does not imply canonical HIR projection,
candidate acceptance, source-graph incidence, scheme capture, public closed
types, or runtime support. Record the exact constructors and refusals at each
owner. Do not read outside the repository, reinterpret Tuple as Group/Unit,
or infer missing work from an absent search match alone.

No implementation or production permission follows. Independent review,
source/native proof, Console readiness, and all original parent gates remain
OPEN.
