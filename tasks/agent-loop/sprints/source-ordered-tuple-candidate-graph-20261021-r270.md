# R270 — connect source tuples to candidate inference graphs

Status: ACTIVE; primary-only, no delegated workers. Branch / baseline: `research/simple-sub-intrusion` / `62c173f78`. Authority: unchanged Types semantics in R149; R168 tuple relation; R251 source arity mapping; R253-R254 ordered native terms/live comparisons; proof-companion §7 constructor-to-consumer connection.

## Outcome

Replace candidate source's blanket refusal of `LocalSourceForm::Tuple` with an identity-preserving source relation. The positive ordered tuple term must contain one endpoint for each source child in source order; all child computation effects must flow to the tuple expression's effect result. Candidate graph capture and fresh reconstruction must retain arbitrary finite tuple arity/order and all child rows. Empty tuples stay Unit/refused according to existing source mapping; singleton comma remains a one-element tuple.

Success evidence: focused candidate inference on heterogeneous source tuples of arities 1, 2, 3; graph export and fresh-use reconstruction expose the same ordered child identities; effectful child evidence reaches the tuple result row; unequal arity and per-index type mismatch continue using R254's indexed diagnostics; ordinary solver tests pass. Falsifiers include dropped/reordered/duplicated elements, lost child effects, tuple terms failing capture/replay, or output dependent on a source spelling.

## Exact writes and boundaries

Allowed writes: `crates/yu-solver/src/candidate_source.rs`, `crates/yu-solver/src/candidate_scheme.rs`, `crates/yu-solver/src/shadow_apply.rs`, `crates/yu-solver/src/lib.rs`, this contract, `notes/theory/2026-10-21-r270-source-tuple-candidate-graph.md`, `tasks/agent-loop/inbox/20261021-r270-source-tuple-candidate-graph.md`, and primary-owned `tasks/agent-loop/current.json`.

No parser/HIR semantic changes, public `yu-types` tuple scheme export, runtime Tuple instruction/value, module/library resolver, sample/expected-output edits, production promotion, or claims of R149/sample closure in this packet. Keep original Y2 input and output requirements intact. Provisional source/native evidence only; no independent review.

## Proof and implementation method

At source admission, carry the exact `LocalSourceIndex` children and their effect component positions into one tuple relation. At solver admission, build one positive native tuple term from the source-order child endpoints and constrain it against the tuple expression's negative value component. Admit one child-effect-to-parent-effect relation per source child with noncolliding, range-checked local slots. Extend candidate graph shape capture and fresh reconstruction with ordered tuple children and account retained backing capacity. Reuse R254's live tuple arity/index worklist. Add source-level falsifiers for heterogeneous positions, duplicate positions, nested tuples, and tuple-contained effect contributions.

Cap 1,200 seconds, no carryover, one heavy Cargo process. Keep full-solver limitations and baseline failures separately identified. Commit/push a coherent verified checkpoint; leave unrelated user-provided untracked documents untouched.
