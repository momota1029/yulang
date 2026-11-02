# R284 — capture-complete storage invariant for the extrusion model

## Fixed parent and bounded outcome

The unchanged parent is `R70-ORDINARY-EXTRUSION-ENTRY-RETURN-1`, fixed by
`tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md`.
Preserve its original entry-to-return claim, source domain, quantifiers and
approved semantics. This packet targets only the row/capture reference-safety
component exposed by the reviewed R283 counterexample. It does not establish
the R70 entry envelope or its Rust/source correspondence. Parent/A/B remains
0->0; R70, source/native bridge and production gates remain OPEN unless a
source-qualified result actually resolves them.

Produce a kernel-checked theorem or a decisive kernel-checked falsifier for a
capture-complete storage invariant over the existing model. Extend the
R283 `RowsValid` candidate with validity of every capture-incidence source
row consumed by `incomingJobs`, including the required relation to
kind-separated canonical representatives. The contract does not prescribe an
unjustified exact formula: derive the weakest useful clause from the actual
model definitions and state its type precisely.

## Required proof path

1. Freeze the exact invariant and establish that it implies R283 `RowsValid`,
   excludes `captureGap`, and holds for the existing computed initial state.
   Do not assume reachability or restrict the supported state domain.
2. Prove or refute preservation by the **actual** `OriginalExtrusionWork.step`
   for arbitrary `Funding` and every satisfying state. Use explicit frame
   lemmas for row allocation, canonical-map changes and queue construction.
   Cover every Work constructor and all `.next`, `.external`, and `.failed`
   projections, including failure after partial publication.
3. If step preservation closes, derive finite `runPrefix` preservation and
   apply it to the existing computed row prefix where initialization is
   established. If a premise or case remains open, freeze the first
   kernel-checked counterexample or exact remaining constructor obligation;
   do not call adding a predicate success.

No circular preservation hypothesis, assumed `LocalLaws`, hidden axiom,
omitted failure case, narrowed source domain, edit to the existing model, or
change to the original parent is allowed. An honest conditional/local result
does not close R70. A second missing storage condition is useful evidence if
its exact falsifier is kernel checked.

## Frozen dependencies and project

Reuse exactly the 16-path input manifest
`tasks/agent-loop/sprints/extrusion-row-validity-r283-review-r2-inputs.json`,
SHA-256 `1a6f485ba1e48dc0b351d644d32803a70cbe485aa5793538ab811cc732b409e5`.
All 16 entries matched in the reviewed R283-R2 gate. Keep R283 candidate,
handoff and model bytes frozen.

Additional pins:

- R283-R2 independent review:
  `tasks/agent-loop/history/20261103-r283-counterexample-review-r2.md`,
  SHA-256 `431b907c16dcbd8958bf319c2e7140f81e577418d071cf1e45fdab041c380c0b`.
- Unchanged parent authority:
  `tasks/agent-loop/sprints/ordinary-extrusion-invariant-20261019-r70.md`,
  SHA-256 `4fa363c4dcbd97450b16dd2afb8b1bf2889f9faf00168d444205fe3633bee5cf`;
  `tasks/agent-loop/inbox/20261019-r70-proof.md`, SHA-256
  `25f6a370ae1aa2d7a623a8aa0eaede979248d85b8c03c894fbf8f7850775e8db`;
  approved principles `notes/design/2026-10-11-yulang-inference-top-level-principles.md`,
  SHA-256 `7701841ab4b961a788574c899af877f5d69b2eced4b628477cc6065ab0d81b81`.
- Lean `4.35.0`, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; use
  the existing `notes/theory/lean` project and unchanged 11-module import
  cone. No package update or new dependency is authorized.

## Ownership, review and resource envelope

Producer: `/root/sol_r284_capture_validity`, registered `lean_prover`,
requested Sol/high, maximum 2,400s, no descendants. Exact write leases:

- `notes/theory/lean/YulangClosure/OriginalExtrusionCaptureValidityR284.lean`
- `tasks/agent-loop/inbox/extrusion-capture-validity-r284.md`
- `notes/theory/lean/.lake/build` (exclusive producer ownership until STOP).

Run the focused pinned Lake build, direct Lean check and bundled axiom checker
for the new module. Report complete declaration types and per-theorem axiom
lists. Do not run a broad suite. Freeze all writes and processes at STOP.

After producer STOP and cache ownership reconciliation, assign a fresh
independent Sol Lean reviewer for up to 900s. The reviewer checks the frozen
module/source order, exact quantified theorem, every Work/Result and failure
case, theorem applications, complete axiom audit, computed-prefix application,
and performs the focused independent checker run using the transferred cache
lease. The reviewer may not certify the producer's proof from its report alone.
Luna owns the review receipt and adjudication; reviewer has no write lease.

Luna's preparation/adjudication allocation is 300s. Fresh R284 envelope:
3,600s total—producer 2,400s, independent reviewer 900s, Luna 300s. All R282,
R283 and earlier charges remain consumed. No refund, renewal or producer
budget reset. No Rust/source/Cargo/test/probe, external-body, implementation,
semantic, Git or source-domain change authority is granted. Stop on a genuine
counterexample, unavailable checker, dependency/scope expansion, or exhausted
budget; consult the dispatcher at that material boundary.

## Required handoff and status boundary

Handoff must state exact invariant, theorem types/axioms, source/model input
definitions inspected, every constructor result, checks, hashes, exact omitted
cases and first remaining premise with its owner. Apply the result to the
unchanged R70 edge: state what follows and what does not. Keep Rust capture
initialization and mutation correspondence through `candidate_source` and
`candidate_intrusion` open; this packet grants no Rust body access. A proved
abstract invariant, refutation of a candidate invariant, or green checker does
not by itself close R70, Simple-sub A/B, Parent, source correspondence, or
production readiness.
