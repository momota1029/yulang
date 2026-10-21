# R273 — public closed ordered Tuple nodes

Status: ACTIVE; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 playground and proof-backed compiler/evaluator goal; R149 Types/Console remain open.
Baseline: `eeaa516ee` on `research/simple-sub-intrusion`.
Authority: R149 arbitrary finite ordered products; R168 §§3–6; unified design plan §3; R254 exact same-index/arity behavior; current `yu-types` closed-arena API.

## Outcome

Add ordered arbitrary-arity Tuple constructors to the public closed-type representation for both positive and negative value views. Carry ordered children through indexed scheme input, draft finalization, validation, planned commit, permanent arena nodes, borrowed views and alpha-equivalence. Preserve exact arity and each indexed child; tuples are not unions or intersections.

Success evidence: indexed and draft paths finalize heterogeneous and nested positive/negative tuples; public views expose children in the original order; alpha-equivalence recognizes identical tuple shape and distinguishes reordered or different-arity products; existing finalization atomicity/resource tests remain intact; focused `yu-types` tests pass.

Falsifiers: a child is omitted/reordered, a malformed child span is accepted, order/arity is erased by alpha-equivalence, positive/negative paths diverge, or a failed finalization leaks partial arena state.

## Exact write paths

- `crates/yu-types/src/lib.rs`
- this contract
- `notes/theory/2026-10-22-r273-public-ordered-tuple-types.md`
- `tasks/agent-loop/inbox/20261022-r273-public-ordered-tuple-types.md`
- primary-owned `tasks/agent-loop/current.json`

No solver candidate exporter wiring, inference semantics, runtime changes, public renderer integration, source/native proof, exact Y2 samples, proof-gate closure, or production promotion in this packet. This only equips the closed-type API with the already approved product constructor.

## Method and limits

Mirror the existing ordered child spans used by Union/Intersection storage, with a distinct Tuple constructor and distinct public borrowed view. Use the existing `positive_children` and `negative_children` lanes with their checked reservation, validation, rollback and accounting rules. Extend every indexed/planned/final arena traversal and `alpha_eq`. Preserve product order and arity exactly; do not normalize Tuple children as a set.

Budget: 1200 seconds, no carryover, one heavy Cargo process. Solo primary work; no independent review under the user's instruction. Focused type finalization/equality tests, sprint static check and `git diff --check`. Parent source/native, solver-to-public export and production gates remain OPEN.
