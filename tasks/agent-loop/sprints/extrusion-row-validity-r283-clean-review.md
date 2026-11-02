# R283-R1 — clean independent review of the frozen Lean counterexample

Review-only continuation: no producer or compiler work is authorized. Preserve
R283's proof result and prior incomplete review unchanged. This continuation
adds 600s: a fresh independent auditor has 450s and Luna has 150s for gates and
adjudication. All prior R283 and R282 charges remain consumed; no renewal or
refund. Parent/A/B remains 0->0, R70 and source/native correspondence remain
open, and implementation remains NO_SAFE_CODE_SLICE.

## Frozen question and dependencies

Review only the claim that the frozen Lean module gives a genuine
counterexample to its particular candidate `RowsValid` predicate. Do not
promote that claim into impossibility of stronger invariants, source-language
counterexample, Rust reachability, or refutation of R70 W.

Exact frozen artifacts:

- `notes/theory/lean/YulangClosure/OriginalExtrusionRowValidityR283.lean` —
  SHA-256 `31c83006c8d9b411b00d045fd16c9e5875e8a73d5baead989c7a55315f3a3f10`.
- `tasks/agent-loop/inbox/extrusion-row-validity-r283.md` — SHA-256
  `63e79d8e52243eccd6e83ddf4eef4c11d72e40e91a3f0fcea551e58084b72428`.
- Governing model `notes/theory/lean/YulangClosure/OriginalExtrusionWork.lean`
  and the exact 11-module/config pins in
  `tasks/agent-loop/history/20261103-r283-proof-admission.md`.
- Pinned toolchain: Lean 4.35.0, commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; no package update or external
  source is needed.

## Mandatory review sequence

1. **Contract-only WAITING gate:** initially read/hash this contract only.
   Return the observed hash and actual identity, then WAIT. Do not open the
   candidate, handoff, imported module or proof output yet.
2. **Luna GO:** Luna compares the contract digest and actual identity, then
   issues explicit GO. The acknowledgement itself is not a technical
   dependency and needs no expected hash.
3. **Technical hash gate:** the first operation after GO hashes every exact
   technical input listed above and in the R283 admission, rendering only
   match/mismatch results. Stop on any mismatch.
4. **Source-first review:** inspect the pinned model definitions for
   `incomingJobs`, `copiedRow`, `step`, and `runPrefix`; only after that inspect
   the frozen candidate and handoff. Do not rely on the producer's narrative
   before reconstructing the path.

No checker or Lake rerun is assigned. Use the Sol handoff's frozen commands,
complete theorem types and axiom audit; if independent kernel rerunning is
needed, stop and return that need to Luna rather than touching `.lake/build`.

## Questions to adjudicate

Independently verify:

- whether `RowsValid` omits a required capture-incidence source-row clause;
- `captureGap_valid` and the actual `step funded` transition;
- the pending Effect Visit for row 99 while the resulting effect-row count is
  two;
- `resultState` for `.next`, `.external` and `.failed`;
- the exact quantifiers in `StepPreservesRows` and `RunPrefixPreservesRows`, and
  whether the kernel-checked negations use this counterexample (fuel one for
  `runPrefix`);
- `computed_rowInput_valid`, complete printed theorem types and axiom lists;
- which other Work, failure, external-yield and partial-publication cases remain
  open;
- the first repair premise and the still-missing Rust/source initialization and
  mutation bridge.

Report PASS, INCOMPLETE, or a concrete defect. A valid counterexample to this
candidate predicate is not evidence that no stronger invariant exists.

## Exact ownership and limits

Fresh identity `/root/r283_counterexample_clean_review`, registered
`parent_edge_auditor`, requested Sol role as fixed by the profile, maximum 450s,
no descendants. Read-only: no file, cache, build, tests, Rust, Cargo, probes,
external bodies, Git or semantic edits. The reviewer returns its frozen receipt
to Luna; Luna owns
`tasks/agent-loop/history/20261103-r283-counterexample-clean-review.md`.

The next capture-closed invariant proof is not authorized by this review
continuation. It requires a separate admitted sprint after clean adjudication.
