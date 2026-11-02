# R284 producer outcome — candidate invariant refuted

Producer `/root/sol_r284_capture_validity` STOPPED / WRITES_STOPPED with no
descendants or processes. Charge the full 2,400s reservation; exact CPU/RSS and
active runtime were not reported. No carryover. The module and handoff are
frozen pending independent Sol review.

## Frozen outputs and verified baseline

- Contract `tasks/agent-loop/sprints/extrusion-capture-validity-r284.md`:
  `b603f920183eed952cfa4df176f81a5026736c4295ecc0bece1b0486c75b8741`.
- Lean module `notes/theory/lean/YulangClosure/OriginalExtrusionCaptureValidityR284.lean`:
  `6842d0af28691e18ea6c50f250ff08f14205c5cb45ced3d0c58e07178e30f49c`.
- Handoff `tasks/agent-loop/inbox/extrusion-capture-validity-r284.md`:
  `8f4d100930853d61b6d7f883f14955b67c3b79ffb170c76e87aec88d5e4b3407`.
- The 16-path R283-R2 manifest and every parent/R283 authority pin matched;
  Lean 4.35.0 / commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` was used.

## Candidate and checked result

The proposed invariant defines
`CaptureSourceValid s source := source < s.effects.length ∧ s.qe source < s.effects.length`,
`CapturesValid s := ∀ id incidence, incidence ∈ s.captures id → CaptureSourceValid s incidence.source`,
and `CaptureComplete s := RowsValid s ∧ CapturesValid s`.
It quantifies over every capture key, including not-yet-allocated indices,
because allocation can expose a latent capture list at a fresh index in an
arbitrary state. `incomingJobs` consumes a capture's raw Effect source and its
canonical Effect representative. The handoff contains the full 18-theorem
type table and complete per-theorem `#print axioms` results.

The kernel-checked results show that `CaptureComplete` implies R283
`RowsValid`, excludes the R283 `captureGap`, and holds for
`Computed.rowInput caller`. Allocation, canonical-map and queue frame lemmas
are also proved. The candidate nevertheless fails preservation by the actual
`step` for its original arbitrary-Funding/every-satisfying-State quantifiers.

Concrete falsifier `viewTailGap`: two Value rows, one Effect row, no captures,
a published allowance view 7 with Effect tail row 99, and a positive Visit of
that allowance. The state satisfies `CaptureComplete`. `step funded` returns
`.next`, queues an Effect Visit for row 99, and has an Effect vector of length
1. The resulting Work violates R283 `RowsValid`. The exact checked theorem is
`¬ StepPreservesCaptureComplete`; no preservation conclusion follows.
The first newly visible missing premise is validity/closure of published
view tails. This does not refute R70 or any source/Rust execution.

Checks in the pinned project: focused Lake build (14 jobs), direct Lean check,
and bundled checker auditing all 18 declarations exited 0. The checked axiom
sets are only `propext` / `Quot.sound` or none; no `Classical.choice`, project
axiom or `sorryAx`. `rg` over the module found no `sorry`, `admit`, project
`axiom`, `unsafe` or kernel-skip token. Initial proof attempts failed on
case-split and exact-length obligations; they were repaired before freeze.
No broad suite, Rust/Cargo, probes, model edits, external contact or Git work
occurred.

## Parent application and open cases

R284 refutes this candidate invariant and identifies another storage premise.
It closes no R70 entry-to-return obligation. Other Work constructors, other
Visit branches, `.external`, `.failed`, partial publication, arbitrary
Funding success/failure branches and finite `runPrefix` remain unproved; the
step claim is already false. The computed initial invariant cannot be
inducted through the existing three-step computed row prefix under this false
predicate.

The next proof must account for view-tail validity and canonical/effect
closure while covering every actual transition and failure projection. Rust
initialization/mutation correspondence through `candidate_source` and
`candidate_intrusion` remains unaudited and was not in the lease. Parent/A/B
stays 0->0; R70, source/native correspondence and production readiness remain
OPEN; `NO_SAFE_CODE_SLICE` remains. Independent review and Luna adjudication
are pending.
