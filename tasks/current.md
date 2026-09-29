# Current task: redesign Function inference with SCC intrusion

Updated: 2026-09-29. Branch: `research/simple-sub-intrusion`.

## Objective

Replace the F5 Function generalization/closed-scheme architecture with a new
SCC-intrusion design. F5 is legacy comparison material, not the target
semantics. The observable target is Oracle-compatible behavior on the
supported envelope, using frozen Yulang2 `main` at `a58eefc3` as the concrete
reference. This is still a design/research branch; no compiler implementation
or frozen `main` change is authorized here.

## Inputs and existing contracts

- `notes/design/2026-09-29-scc-intrusion-generalization-sketch.md`
- `notes/design/2026-09-29-intrude-effect-hygiene.md`
- Existing F5 contract to supersede through an approved successor: `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`, especially §§8–9, 23, 25, and 33. It is not this redesign's acceptance criterion.
- The prior `yulang3` branch retains the in-progress F5c task state at parent commit `32f0a063`; its guarded-cycle measurement budgets are consumed as recorded in the linked plans/checkpoints there.

## Active gate

Replacement-design charter: `notes/design/2026-09-29-scc-intrusion-redesign-charter.md`.
The initial source/test ledger is in
`notes/progress/2026-09-29-intrusion-oracle-ledger.md`. It confirms in-place
level aging in Yulang2 and records a few identity/instantiation witnesses;
source-level and mutual-SCC cases remain open. Next, complete those Oracle
observations, then define the new abstract intrusion semantics against them.
Do not make F5's Q/R shape, closed schemes, numbering, or resource contract
the pass condition.

The reviewed pure-F5 protocol exposed a mistaken compatibility premise and is
retained only as historical review evidence. Scope correction and current
research stages are recorded in
`notes/progress/2026-09-29-intrusion-research-start.md`.

## Stop conditions and next action

Do not implement until the proof/characterization is reviewed and any new
replacement-design decision is explicitly approved. Stop or revise if it
captures an enclosing non-generic variable, merges distinct polarized
constraints, shares substitutions across independent uses, loses a recursive
bound, or changes Oracle-observable behavior inside the supported envelope.
Effect hygiene and runtime freshness remain a later separate gate.

Do not implement before the replacement design is independently reviewed and
approved. Finite examples characterize the candidate but do not alone prove
soundness or principality. Do not run guarded-cycle resource captures: the
current F5c plans on `yulang3` have consumed their authorized runs.
