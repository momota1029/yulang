# R274 rev1 — Tuple rendering with downstream view compatibility

Revision reason: `yu-playground` verification exposed three exhaustive consumers of the newly added public `yu-types` Tuple views in the legacy F5 path. Add an owner-local compatibility update so the renderer package builds. The original R274 packet remains immutable and its renderer goal is unchanged.

Status: ACTIVE; solo primary implementation, no delegated workers.
Parent: unchanged Yulang2 playground and proof-backed compiler/evaluator goal; R149 Types/Console remain open.
Baseline: `81ba87d7f` plus the uncommitted R274 renderer diff.
Authority: R149/R168 arbitrary ordered product semantics; R270 candidate graph Tuple capture; R273 public closed Tuple API; existing F5 closed-scheme instantiation contract.

## Outcome

Render ordered Tuple children in experimental candidate graph output. Make direct `yu_types::PositiveValueView` and `NegativeValueView` consumers exhaustive. The legacy F5 term-instantiation route does not yet have Tuple reconstruction semantics; it must return its existing explicit `SolveAvailabilityError` instead of silently dropping Tuple structure. Do not claim that this adds Tuple support to old F5 inference or makes the public Types pane work.

Success evidence: direct and nested candidate graph export prints every ordered child reference; the `yu-playground` package compiles; any legacy closed-scheme Tuple instantiation is explicitly withheld; focused renderer/type-view checks pass.

Falsifiers: child order/identity is lost; nested constructors flatten; an old F5 consumer ignores a Tuple or fabricates a scalar/function term; or the candidate graph output is labeled as a public closed scheme.

## Exact write paths

- `tools/inference-playground/src/render.rs`
- `tools/inference-playground/src/lib.rs`
- `crates/yu-solver/src/lib.rs`
- this revision contract
- `notes/theory/2026-10-22-r274-candidate-tuple-graph-rendering.md`
- `tasks/agent-loop/inbox/20261022-r274-candidate-tuple-graph-rendering.md`
- primary-owned `tasks/agent-loop/current.json`

No source constraint, candidate solver, Tuple inference, public-scheme exporter, R149 Types pane/sample success, imports, host writes, proof closure, or production promotion. Legacy F5 Tuple instantiation remains unsupported and is surfaced as unavailable.

## Method and limits

Use `CandidateGraphNode::tuple_children()` in the existing bounded iterative renderer traversal; print a distinct ordered `Tuple([n...])` node. In F5's closed-scheme-to-term adapter, traverse Tuple children with the existing explicit work stack, then return `SolveAvailabilityError::IdentityExhausted` at Tuple reconstruction until that route has an approved, resource-bounded product-of-alternatives construction. Do not flatten or convert a Tuple to a leaf/function/union.

Budget: 600 seconds, no carryover, one heavy Cargo process. Solo primary work; no independent review under the user's instruction. Focused playground renderer/type-view checks, sprint static check and `git diff --check`. Public scheme export and all parent proof/sample/production gates remain OPEN.
