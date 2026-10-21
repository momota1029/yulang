# R274 — render ordered Tuple children in candidate graph output

Status: ACTIVE; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 playground and proof-backed compiler/evaluator goal; R149 Types/Console remain open.
Baseline: `a5744c060` on `research/simple-sub-intrusion`.
Authority: R149/R168 arbitrary ordered product semantics; R270 candidate graph Tuple capture; R273 public closed Tuple API.

## Outcome

Make the experimental playground candidate-graph renderer traverse and print ordered Tuple children, including nested Tuple nodes. Keep the graph view's unresolved/provisional label and do not present this output as a public closed scheme or accepted Types pane.

Success evidence: candidate graph export for direct and nested source Tuple reaches each child node and prints their ordered references; nested constructor identity is preserved; focused renderer tests pass.

Falsifiers: the root or a bound Tuple prints as opaque, a child is skipped/reordered, nested tuples flatten, or the output implies that this candidate graph is a public/closed type scheme.

## Exact write paths

- `tools/inference-playground/src/render.rs`
- `tools/inference-playground/src/lib.rs`
- this contract
- `notes/theory/2026-10-22-r274-candidate-tuple-graph-rendering.md`
- `tasks/agent-loop/inbox/20261022-r274-candidate-tuple-graph-rendering.md`
- primary-owned `tasks/agent-loop/current.json`

No solver semantics, public type export, R149 type pane/sample claim, imports, host writes, proof closure, or production promotion in this packet. The renderer remains experimental candidate graph output only.

## Method and limits

Use the existing borrowed `CandidateGraphNode::tuple_children()` observation. Include those children in the same bounded iterative worklist used for Function nodes and print a distinct `Tuple([ordered node references])` constructor. Continue charging node/edge traversal against the existing output work cap.

Budget: 600 seconds, no carryover, one heavy Cargo process. Solo primary work; no independent review under the user's instruction. Focused renderer tests, sprint static check and `git diff --check`. Public scheme export and all parent proof/sample/production gates remain OPEN.
