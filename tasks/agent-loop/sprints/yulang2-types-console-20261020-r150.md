# Yulang2 Types/Console initializer certificate — R150

Status: prospective contract; Luna owns activation after exact hash review.
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

Read-only source investigation. Inspect only pinned owners needed for the construction: the complete 40-file Y2 closure; Y2 computation classification/root publication, compiled runtime-root composition and specialization; Y3 `crates/infer/src/lowering/body/methods.rs`, `crates/infer/src/lowering/body/mod.rs`, `crates/infer/src/module_map/mod.rs`, `crates/specialize/src/lib_support/specializer.rs`, `crates/mono-runtime/src/runtime/engine.rs`, and `crates/mono-runtime/src/lib.rs`. Add a source owner only by reporting its exact immutable blob and requesting Luna to revise the lease.

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
