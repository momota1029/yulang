# R283 — Lean row-reference preservation in the extrusion Work model

Status: admitted bounded Lean model trial. Sol owns proof construction and the
pinned checker; Luna owns admission, exact leases and independent review.
Original inference soundness, Simple-sub A/B, source/native correspondence,
R70 W and Rust implementation remain unchanged and open. Parent/A/B stays
0->0; implementation stays NO_SAFE_CODE_SLICE.

R282 remains PREPARATION_STOPPED after its recorded cfg(test) read-boundary
incident. Keep its full 600s charge and preserve its record. This sprint uses
only the existing Lean model and its pinned import cone; it does not reopen or
rely on R282 Rust reads.

## Fixed statement and useful outcome

The model authority is `YulangClosure.OriginalExtrusionWork`, imported from
`OriginalInferenceTerminationResolution`.lean through the authenticated
11-module cone listed in the admission. Preserve all existing constructors and
the actual definitions of `State`, `Result`, `step`, and `runPrefix`.

Construct a non-tautological state invariant that accounts for valid canonical
row representatives, every stored Value/Effect row reference in bounds,
`rows` and `structureMemo` keys and images, term cells, pending Work, and
retained Parents. Define a total result-state projection for all three existing
`Result` constructors (`next`, `external`, `failed`). Then attempt:

- `step_preserves_rows`: the actual `step` preserves the invariant for every
  `Funding` and invariant-satisfying state;
- `runPrefix_preserves_rows`: the actual finite `runPrefix` preserves it for
  every fuel, including normal `next`, external-yield and failed results.

The invariant may add only constructor-derived premises needed to express
validity of the represented state; do not assume the post-state invariant,
introduce `LocalLaws`, or hide preservation in an arbitrary strengthening. A
kernel-checked counterexample showing the proposed invariant insufficient is a
valid trial result. Account for all `Work` constructors and partial publication
before failure. Apply the result to an existing computed row-prefix example if
its initial invariant is derivable without new assumptions.

This can establish only a Lean-model local preservation component. It does not
establish Rust initialization, native external callback behavior, source
reachability, the full R70 `W`, or original theorem closure. Keep those bridges
explicitly open.

## Frozen inputs, outputs and checker

Before writing, verify the contract, 11 input module hashes, project
configuration, native `lake` path and pinned Lean version. The imported module
cone and configuration were clean in Luna's admission scan. The project pins
Lean 4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and declares no external
packages. No installation, package/config update, Mathlib, Rust/Cargo, tests,
runtime probes, production code or Git writes are authorized.

Exact Sol leases:

- `notes/theory/lean/YulangClosure/OriginalExtrusionRowValidityR283.lean`
- `tasks/agent-loop/inbox/extrusion-row-validity-r283.md` (proof, exact theorem
  types, complete checker output, axiom audits and STOP receipt)
- `notes/theory/lean/.lake/build` (exclusive Lake build/cache ownership)

The `.lake/build` lease transfers from Luna to Sol for this assignment. Sol is
the sole build/cache verifier until STOP. Preserve all existing cache contents;
do not clean the project. Use the native resolved Lake only and `-j1 -M1024`.
The maximum proof allocation is 1,800s; no renewal. No descendants. Stop after
proof/counterexample, exact theorem type and full axiom audit are frozen.

After Sol STOP, Luna assigns a different fresh reviewer up to 900s to check the
frozen invariant, represented Work/Result cases, actual `runPrefix` application,
the exact checked theorem types/axioms, and the model/native boundary. Luna's
preparation/adjudication allowance is 300s. Total envelope: 3,000s.
