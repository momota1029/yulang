# R277 — Fixed-witness admission to the public candidate route

## Unchanged parent and bounded outcome

The authorized goal remains inference/effects soundness → R70 → R71 canonical-fiber coverage. Preserve the original source domain and quantifiers, Parent/A/B, Simple-sub source/native correspondence, independent satisfying assignments, shared witnesses, F1/FK1 and foreign continuations. Parent/A/B stays 0→0; `Need_D`, R71 and full soundness stay OPEN. Implementation remains `NO_SAFE_CODE_SLICE`.

R276 established, under `shadow-apply-candidate`, a public `solve_receiving_residual_experiment(hir, answer)` route that reaches `assemble` before `collect_candidate_mode(hir, true, true)`. R277 asks whether the exact existing 87-byte loop/direct/helper witness, lowered through its source-production path, supplies an HIR and actual `outer: DefinitionRootId` plus `answer` that satisfy `assemble`'s real guards and connect to candidate collection/session startup.

Stop at candidate session startup. Do not claim `execute_receiving_assembly`, residual publication, complete inference success, ordinary compiler acceptance beyond the inspected source construction, R71 necessity/coverage, or parent closure.

Return exactly one result:

1. **ENTRY_ADMITTED_PREFIX:** derive the exact source-produced HIR/root and answer, satisfy each visible `assemble` guard, and connect the result to candidate collection/session startup under explicit normal-return/fallible premises.
2. **WITNESS_REJECTED_AT_GUARD:** identify the first exact production guard rejecting this unchanged witness and the actual source-produced value at that guard. This excludes only this witness from this public entry under those conditions; it does not establish global unreachability or refute soundness.
3. **UNRESOLVED:** identify the first omitted owner or premise that prevents either result.

Never change the 87-byte source, synthesize or substitute a private answer/HIR, bypass `assemble`, or infer missing constructors from a test. If the actual caller outside the authorized inventory is required, STOP before opening it and return its exact path/symbol; this contract grants no external-path authority.

## Fixed witness and authority

The exact 87-byte fixture spelling is:

```text
my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }
```

Its sole source occurrence is the fixture-only interval `candidate_source.rs:2525–2540` in authenticated R275-r3 payload `R274-E001`; no test body, assertion, `unwrap`, or outcome is evidence. Preserve the existing feature configuration `shadow-apply-candidate`; no feature or source change is authorized.

R276's independently reviewed conditional public-route result is frozen in its final milestone `tasks/agent-loop/history/20261103-r276-closed-milestone.md`, SHA-256 `695c18a2b067faf39c3cfa08e94c324607e163c5ddb42a216cb62f037c63e992`. It does not establish this witness's admission to `assemble`.

## Exact authenticated inputs

The source inventory is `tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json`, SHA-256 `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f` (229 entries). Every path must be derived from this inventory and its expected hash checked before opening.

**Existing lossless source-production view**, admitted previously by R275-r3 contract SHA-256 `4e30e9c048596a57da7cfa80fe1261e67e2db17f2ba8c07e70dc3961b02138c5`:

- R275-r3 ranges `tasks/agent-loop/sprints/source-acceptance-r275-r3-ranges.json` — `2cd3ad9dc9a66129a42ec11d8d45ef4b78a0a877d0d066dc262313d524c03c3e`
- R275-r3 production/fixture view `tasks/agent-loop/sprints/source-acceptance-r275-r3-source-view.txt` — `6b3836953c876c40f2cda0b944ff5f8a8d912d179e5ac58f9e93c7e6d38e8373`
- R275-r3 byte index `tasks/agent-loop/sprints/source-acceptance-r275-r3-view-index.json` — `0966c2429bb64896bd31de52f2e20609642c2a75bba6dae3cf5fec46ebcb94e5`
- R275-r3 coverage map — `61d22ccc8004305fb377a12556cd53550926c59cb5857a55b0f01f5921e775cb`
- R275-r3 entry/flag index — `74ec95494935e803296f8ab276b6237369253f73d3df57ec2bc5f33f12426481`

Relevant authenticated source-production payloads include `R274-E001` (fixture-only exact bytes), `R274-E009/E010` (syntax parse/root path), `R274-E020/E021/E022/E023` (HIR identity/module/local-source owners), and `R275R3-E001/E002` (root parser and public HIR forwarding). The view index is authoritative for exact payload ID, file, interval and byte offset. The corrected coverage map says E022 contains module lowering and E023 the local-source carrier; check the index rather than trusting prose labels.

**R276 reviewed public route:** contract `tasks/agent-loop/sprints/production-entry-provenance-r276.md` SHA-256 `632d5b648b6ebcc005e064d0e03bbb41f1b034396fd690d475e16f110c1fd78c`; source view `c80d993a2a0bcb38ea428f4c4c11bfc2d03b804ba0e24d45807b6c2b65a502df`; view index `2e8892ae1d7ca1e95016b393bdb3c62881c79d47ed848275b154232a2dfe60e1`; clean independent review `8d7060f9157a3a028b02c45b171f2f94b4ed0c3de06d098755427554677b5c9e`. Use corrected owner map v2 `tasks/agent-loop/sprints/production-entry-provenance-r276-source-owner-index-v2.json`, SHA-256 `6edcf1f02efabb81c3d45b4d75c498cbc2f503b41c1b7ee72c61bb1bded51e42`; original v1 remains immutable and non-authoritative for route labels.

**R277 production-only backward slice:**

- Exact ranges `tasks/agent-loop/sprints/public-entry-admission-r277-ranges.json` — `63f2ce9d1ffb2e14a497d89b928065edd955f3ecd2266b0eb51f670fabd4e855`
- Exact source view `tasks/agent-loop/sprints/public-entry-admission-r277-source-view.txt` — `ebeae02540be5811850017b6f8b7ff49783a95e17d2b05358a155bd47bb22b21`
- Byte index `tasks/agent-loop/sprints/public-entry-admission-r277-view-index.json` — `8fb7a74c4953d0f78e04f321f437432bbdb9baae811027c555854ade06bfa0da`

`R277-E001` contains the production `Assembly` type, helper owners, complete `assemble` body and the adjacent public-entry forwarding continuation from `candidate_receiver.rs:2921–3179`. It contains no `#[cfg(test)]` boundary. These excerpts, together with the authenticated R275 and R276 views, are the bounded source domain. Original source bytes may be hashed and compared in memory, but production bodies are read for reasoning only from exact indexed view payloads.

## Stage 1 — Sol readiness and owner closure

Producer/trial owner: stopped Sol identity `/root/sol_r274_source_acceptance`, requested Sol/high, prior cumulative Sol charges 9,300 seconds. Stage allocation: 300 seconds. Sol first reads and hashes only this contract and the admission record. After a contract-only WAITING acknowledgement, Luna issues a separate immutable GO for readiness; no source/index/view bodies are read before that GO.

Readiness independently checks every top-level pin, the 229 inventory rows, all 41 inherited payloads and the R277 extension payload. Reconstruct the `assemble` function's direct helper/callee and caller ownership; verify the source fixture → syntax/root → HIR/module/local-source/root-identity → actual public `assemble` entry chain; identify the exact origin of `answer` and `outer: DefinitionRootId`; check that each relevant owner is in the pinned view and that no production/test boundary is crossed. The owner map is navigation only. If an owner is missing or an input/hash is ambiguous, STOP and report the exact missing path/symbol/range. Do not start fixture derivation or main trial during readiness.

Luna adjudicates readiness. Only a full PASS can unlock a separate 1,500-second main-trial GO under this unchanged contract. A readiness failure cancels the main and reviewer stages; no fixture substitution or budget extension.

## Stage 2 — Sol constructive admission trial

After readiness PASS and Luna's explicit GO, Sol derives the source-produced HIR and answer for the exact witness, checks actual source/root identity and every `assemble` guard, and follows its normal return into the reviewed candidate collection/session route. Report the first failed guard if rejected. Keep execution after candidate startup outside the claim. Freeze only the two outputs below with exact hashes, complete resource/STOP receipt and remaining premises.

No runtime execution, probes, builds, tests, Cargo, Lean, network, scratch/cache output, code edits, descendants, external source reads, semantic changes or production promotion.

## Review, resources, outputs and stop conditions

A fresh independent compiler referee receives 900 seconds only after a coherent frozen pair. Luna receives 300 seconds total across preparation/adjudication. Total new R277 envelope: **3,000 seconds**—Sol readiness 300, Sol main trial 1,500, independent review 900, Luna 300. Full grants are charged; R276's 1,800-second charges remain intact. No Astra, descendants, or implementation worker.

Exact producer outputs, written only after main GO:

- `notes/theory/2026-11-03-public-entry-admission-r277.md`
- `tasks/agent-loop/inbox/public-entry-admission-r277.md`

Review receipt after freeze: `tasks/agent-loop/history/20261103-r277-public-entry-admission-review.md`. The reviewer writes no repository output.

STOP on any pin mismatch, out-of-view source need, missing direct owner, source identity mismatch, test-boundary exposure, or unavailable constructor premise. Preserve the exact witness and report the first failure without widening claims. Even a successful finite prefix does not close A/B, Need_D, R70/R71, ordinary full compiler acceptance, or the unchanged parent theorem.
