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

Pure F5 proof or executable characterization: define the polarized boundary
closure and eligible variables, then compare ordinary extrusion against
parent-based intrusion per member and per incoming use. Include polarity,
outer non-generic endpoints, one-sided bounds, guarded and unguarded cycles,
Q/R identity, root-order independence, two incompatible incoming uses, internal
live uses, and exact closed-scheme alpha-equivalence.

The initial independent architecture and compiler reviews found unresolved
correctness obligations. In particular, definition-SCC membership alone does
not delimit the reachable polarized bound graph, and a shared component map
does not establish F5's member-local binders or fresh per-use instantiation.
See `notes/progress/2026-09-29-intrusion-research-start.md`.

## Stop conditions and next action

Do not implement until the proof/characterization is reviewed and any new
representation decision is explicitly approved. Stop or revise the proposal
if it collapses polarity, changes Q/R ownership, shares substitutions across
incoming uses, loses lower/upper recursive bounds, or fails closed-scheme
equivalence. Effect hygiene and runtime freshness remain a later separate
gate.

Next: write the smallest formal state model and reference relation for pure
F5 extrusion versus intrusion; use the counterexample shapes in the progress
record as mandatory fixtures. Do not run guarded-cycle resource captures: the
current F5c plans on `yulang3` have consumed their authorized runs.
