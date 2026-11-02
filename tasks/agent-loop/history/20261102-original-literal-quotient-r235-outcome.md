# R235 outcome — literal quotient readout

Status: **REVIEWED MODEL-INCOMPLETE**. Baseline `0d31b1277` on `yulang3`.
Unchanged parent: `YulangClosure.SourceProblem.InferenceSoundness`,
`Contracts.lean:128–130`.

## Result

The primary-checked Lean module defines mutual structural `Sub`, the resulting
value-term `Setoid`, and a quotient observation. It proves that reciprocal
subtyping bounds imply equality of observations for every satisfying valuation.
It also proves the R232 union case: `union B B` and `B` have the same quotient
observation without claiming syntactic identity.

The three checked declarations are:

- `observe_eq_of_mutual_sub`
- `reciprocal_base_bounds_readout`
- `union_self_observation`

Pinned Lean 4.35.0 / Lake 5.0.0 module build and named type/axiom audits passed.
Each theorem reports only `[Quot.sound]`. The independent source/model review
passed for this abstract leaf and its incomplete disposition.

## Parent application

The result does **not** establish that the selected Yulang algorithm generates
reciprocal literal constraints, map all eight literal forms to typed atoms,
interpret the quotient in the adopted `PaperTypes` descriptor/effect carriers,
derive original `LiteralAtom`/Return at the same source coordinates, or build
the shared `sameScoped` witness. No theorem was applied to the original parent.
Parent-premise delta **0**; roots **0/4**. No source or solver semantics changed.

The next evidence must address the actual generator/carrier equation at its
abstract model owner. Repeating a reciprocal-bound lemma or another clean
conditional quotient result will not count as progress toward soundness.

## Verification, review and resources

The pinned checker built the module and audited all three named declarations.
The static sprint consistency checker passed; no Rust/Cargo or general tests ran.
The fresh reviewer checked the frozen source authority and exact limitations,
but did not rerun Lean or the producer axiom audit.

Existing `.lake` was 134,545,883 bytes before and 134,587,836 after R235:
growth 41,953 bytes. No new worktree, environment, target or cache path was
created. Unrelated dirty files and UNKNOWN/quarantined leases were preserved.

Artifacts: contract `tasks/agent-loop/sprints/original-literal-quotient-r235.md`,
module `notes/theory/lean/YulangClosure/OriginalLiteralConstraintModelR235.lean`,
handoff `tasks/agent-loop/inbox/original-literal-model-r235.md`, and review
`tasks/agent-loop/inbox/original-literal-model-r235-review.md`.
