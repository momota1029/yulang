# Current task: investigate Simple-Sub SCC intrusion

Updated: 2026-09-29. Branch: `research/simple-sub-intrusion`.

## Objective

Study whether Yulang3 type inference can use SCC-preserving intrusion for
generalization and instantiation. This is a proof/research branch. It does not
authorize implementation, an F5/F5c cutover, or a change to the current
Authoritative F5 contract.

## Governing material

- `notes/design/2026-09-29-scc-intrusion-generalization-sketch.md`
- `notes/design/2026-09-29-intrude-effect-hygiene.md`
- Authoritative baseline: `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`, especially §§8–9, 23, 25, and 33.
- The prior `yulang3` branch retains the in-progress F5c task state at parent commit `32f0a063`; its guarded-cycle measurement budgets are consumed as recorded in the linked plans/checkpoints there.

## Active gate

Reviewed protocol: `notes/design/2026-09-29-pure-f5-intrusion-reference-model.md`.
Next, work the first finite pure-F5 witnesses by hand and define one concrete
candidate parent-transport transition. Compare it with insertion-time F5
level-aging from the same pre-insertion input, then compare per-member schemes
and same-member independent uses. Keep post-insertion projection evidence
separate from any claim that intrusion replaces extrusion.

The initial reviews found that SCC membership does not delimit bound-graph
reachability, parent sharing does not establish member-local binders or fresh
per-use instantiation, and F5's insertion-time extrusion must be compared from
pre-insertion state. The protocol records those obligations and exact
comparison fixtures in `notes/progress/2026-09-29-intrusion-research-start.md`.

## Stop conditions and next action

Do not implement until the proof/characterization is reviewed and any new
representation decision is explicitly approved. Stop or revise the proposal
if it collapses polarity, changes Q/R ownership, shares substitutions across
incoming uses, loses lower/upper recursive bounds, or fails closed-scheme
equivalence. Effect hygiene and runtime freshness remain a later separate
gate.

Do not implement or claim general equivalence from finite examples. A general
extrusion-replacement claim needs a simulation relation and induction
invariant; any new scheme/lifecycle decision needs separate approval. Do not
run guarded-cycle resource captures: the current F5c plans on `yulang3` have
consumed their authorized runs.
