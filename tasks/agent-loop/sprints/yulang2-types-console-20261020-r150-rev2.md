# Yulang2 Types/Console initializer certificate — R150 rev2

Status: prospective contract rev2; Luna owns activation after exact hash review.
Supersedes prospective rev1 `f22f022b75b60af7bb393b5cb1e16bffa002fd3cde0ddc3b790fa7caf70b098d`; rev1 remains immutable and rejected for incorrect repository ownership.
Goal: continue the unchanged user goal: implement proof-backed Yulang inference/evaluation and broaden unchanged Yulang2 Web sample execution. R149 is a capability increment, not the compatibility ceiling.
Parent: R149 provisional Types/Console behavior, `notes/design/2026-10-20-r149-types-console.md`. Exact samples and Y2 oracle are pinned there. Parent A/B/R70/R71/source-native/soundness/principality/production gates remain OPEN.
Baseline Y3: commit `b7b320d0516208ab4f6aeac14b795f99c6f92cce`, tree `7c2f1f06f1f1f6719e5a88a8854a04f98a7774e7`.
Y2 oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, 40 source blobs from R149 rev5; exact Y2 sample templates/hashes in the design.
Reviewed dependency: R149 rev10 contract `31214917352b673c7467873b60d5db8e470e4d16c8370d882c266a7fcef5b3e9`; checkpoint note `0ce7e3127519e6a17aeb1f2f6d25b24490fbca4ea3644efaf7e1ea8a7b3420c0`; inbox `5d786082cabf7b2ce0f9c463eba13c9b1dc9f0cc1ee8e1f8e9d51a4bb03b2ea4`; integration commit `e5eda27cbed5fd2702601d3f9907198616a3c30b`.

## Outcome

Produce a reviewed, construction-directed initializer certificate for the two unchanged modules, or a precise obstruction at the actual constructor/carrier that prevents it. For each required imported computation, connect:

`module/declaration identity → evaluation/fetch classification → publication decision → ordered root → specialization → runtime consumer`.

Determine whether the pinned `Request` rejection boundary can be reached by a required initializer in either sample. Do not infer membership from lexical source shape, file order, or a possible library definition. A conditional runtime boundary does not establish sample failure.

## Source/proof lane — 600 seconds

Read-only source investigation. Keep repository provenance explicit; these are different trees and must never be conflated.

- Y2 oracle: the complete 40-file library closure and loader/schedule owners pinned by R149 rev5. Y2 classification owner `crates/infer/src/typing.rs`, blob `7d8ad7846aaf4942512a23ad3710ddfd9d2e78be`; the Y2 computation/root/specialization/runtime pins and branch are in the reviewed R149 rev2 checkpoint.
- Y3 baseline `b7b320d0516208ab4f6aeac14b795f99c6f92cce`: `crates/yu-hir/src/module.rs` blob `d8c3e696734463a7bf63d05da00f77f57b9982f4` (`SemanticImports`, 108–150); `tools/inference-playground/src/lib.rs` blob `9eeaa94180265970a81f9771a7196e4f0d77008d` (HIR/import and candidate selection, 291–308); `tools/inference-playground/src/runtime/program.rs` blob `fd69daa3d10aeeb4a685766762eef4d80fc0b5de` (root construction/classification, 256–262 and 625–655); `tools/inference-playground/src/runtime/machine.rs` blob `4bfd5e244a768ef4cfe61b50fff512d5969b3c88` (schedule consumption and identity checks, 292–340); and `crates/yu-solver/src/candidate_source.rs` blob `e03d92dcb6016e726fe2748bcfb3f17d52e17cd2` (source schedules/consumers, 1544–1545 and 1623–1653).

Inspect only these admitted owners and the R149 pins. If the certificate needs another source owner, stop at that exact dependency and ask Luna to issue a sequential contract/lease revision. Do not read unavailable Y2 paths as if they were Y3 owners.

Leased outputs only:
- `notes/theory/2026-10-20-types-console-initializer-certificate.md`
- `tasks/agent-loop/inbox/20261020-types-console-initializer-certificate.md`

Outcome class must distinguish proof, conditional evidence, and exact obstruction. Include artifact hashes, source blob pins, root census/order, omitted-case analysis, runtime branch, remaining premise and owner, and worker stop receipt. No code/tests/builds/executions.

## Implementation lane — 180 seconds

Read-only Luna/high owner handoff; no compiler edits. Trace the exact current Y3 path from imported HIR and `SemanticImports` through solver selection and `RuntimeProgram::from_hir`/schedule consumption. Identify carrier and identity obligations needed to use the source certificate. Record `NO_SAFE_CODE_SLICE` unless the reviewed certificate supplies a safe implementation boundary.

Leased output only: `tasks/agent-loop/inbox/20261020-r150-implementation-handoff.md`.

## Reviews and resources

Preparation/pinning: 120 seconds. Independent source/spec review after both results freeze: 180 seconds. Luna closeout: 120 seconds. Total fresh cap: 1200 seconds; charge allocations on issue, no carryover, Astra 0. Do not reuse R149's unissued 240 seconds. No tests, builds or executions in this sprint.

The reviewer must challenge omitted computation roots, source and Y3 ordering, identity joins, root publication, Request reachability, and any claimed sample-specific conclusion. Authors/coauthors cannot review their own lane. CLEAN review is required before accepting the certificate as an implementation prerequisite.

## Authority and stop conditions

No semantic expansion or narrowing, compiler writes, expected-output/fixture changes, or production admission. The exact R149 behavior and unchanged examples stay as adopted. Stop at missing pins, an unleased source owner, inability to identify a real constructor/carrier, or budget exhaustion; report the precise missing premise. Keep all original parent gates OPEN unless separately proven and reviewed. Only Luna owns current state, leases, staging and Git.
