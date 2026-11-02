# R283-R2 — corrected clean independent review

Review-only continuation: no producer or compiler work is authorized. Preserve
R283-R1 as INCOMPLETE with its full 450s charge and preserve all earlier
charges. This distinct continuation adds 600s: independent Sol auditor up to
450s, Luna preflight/gates/adjudication up to 150s. Cumulative R283 allocation
becomes 4,200s. No refund or producer grant.

## Frozen question and inputs

Review only whether the frozen Lean module contains a valid counterexample to
its particular candidate `RowsValid` predicate. This does not imply that no
stronger invariant exists, that Rust reaches the state, or that original R70 W
is refuted. Parent/A/B remains 0->0; source/native correspondence remains
open; implementation remains NO_SAFE_CODE_SLICE.

The exact 16 technical paths and expected SHA-256 digests are in
`tasks/agent-loop/sprints/extrusion-row-validity-r283-review-r2-inputs.json`,
whose SHA-256 is
`1a6f485ba1e48dc0b351d644d32803a70cbe485aa5793538ab811cc732b409e5`.
All 16 digests matched Luna's preflight. Paths are repository-relative and
already include `notes/theory/lean/` where appropriate; do not resolve
filename-only paths relative to repository root or infer alternate paths.
The 16 comprise the exact 11 workspace modules, three pinned project config
files, candidate module, and Sol handoff. No other technical dependency is
authorized.

## Mandatory review sequence

1. **Contract-only WAITING:** initially read/hash only this contract. Return
   actual identity and observed digest, then wait. Do not open the manifest or
   technical inputs.
2. **Luna GO:** Luna checks exact identity and immutable contract digest, then
   sends explicit GO. The acknowledgement is not a pinned technical input.
3. **First technical operation:** hash the manifest and all 16 paths from the
   explicit entries, rendering only match/mismatch results. Stop on any true
   byte mismatch or missing path. Do not print bodies, parsed records, or
   theorem text during this gate.
4. **Source-first review:** after the hash gate passes, inspect the authenticated
   `OriginalExtrusionWork.lean` definitions for `incomingJobs`, `copiedRow`,
   `step`, and `runPrefix`. Only after reconstructing that transition inspect
   the candidate module and handoff.

No Lake/checker rerun is assigned. Do not access `.lake/build`. If independent
kernel rerunning becomes necessary, stop and return that need to Luna; no
reviewer-owned cache/build lease is granted.

## Questions to adjudicate

- Does `RowsValid` omit a necessary capture-incidence source-row clause?
- Does `captureGap` satisfy the exact candidate predicate?
- Does the actual `step funded` queue pending Effect Visit row 99 while the
  resulting effect-row count is two?
- Is `resultState` total for `.next`, `.external`, and `.failed`?
- What are the exact quantifiers in `StepPreservesRows` and
  `RunPrefixPreservesRows`; do their kernel-checked negations apply this state,
  with fuel one for `runPrefix`?
- What are the exact theorem types and complete axiom lists? Does
  `computed_rowInput_valid` follow as stated?
- Which other Work, failure, external-yield, and partial-publication cases
  remain open?
- What is the first repair premise, and which Rust/source initialization and
  mutation bridges are still absent?

Challenge whether the omitted reference component is required by the intended
storage invariant. Treat a genuine counterexample to the candidate predicate
as evidence against that predicate only. Do not promote it to source-language
reachability, Rust validity failure, R70 refutation, or parent closure.

## Ownership and limits

Fresh reviewer `/root/r283_counterexample_clean_review_r2`, registered
`parent_edge_auditor`; profile fixes the requested Sol role. Maximum 450s,
read-only, no descendants. No Rust, Cargo, tests, probes, external bodies,
writes, Git or semantic changes. The reviewer returns findings to Luna. Luna
owns `tasks/agent-loop/history/20261103-r283-counterexample-review-r2.md`,
all adjudication and state/Git integration. After the substantive finding,
stop; no capture-closed proof is admitted by this review.
