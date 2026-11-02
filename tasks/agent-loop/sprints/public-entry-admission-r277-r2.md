# R277-r2 — Fixed-witness admission to the public candidate route

## Correction to R277-r1

Preserve `tasks/agent-loop/sprints/public-entry-admission-r277.md` unchanged. R277-r1 readiness correctly reported that no existing production caller in the 229-path inventory invokes `solve_receiving_residual_experiment`; its STOP record remains valid. Dispatcher adjudication established that such an existing caller is **not required** for the fixed-witness public-entry prefix. The API itself is public and feature-gated; the trial constructs its argument pair from the exact source-production path and checks that application's guards. This does not claim an external invocation.

R277-r1 readiness consumed 300 seconds and is closed INCOMPLETE. Its main/reviewer stages were never issued. R277-r2 newly authorizes only the 1,500-second main trial after a fresh contract acknowledgement and Luna's sequential primary pin gate. There is no repeated readiness grant.

## Unchanged parent, witness and result

The objective remains inference/effects soundness → R70 → R71 canonical-fiber coverage with original source domain, quantifiers, Parent/A/B, Simple-sub source/native correspondence, F1/FK1 and foreign continuations intact. Parent/A/B remains 0→0; `Need_D`, R71 and full soundness remain OPEN. `NO_SAFE_CODE_SLICE` remains.

Use the unchanged 87-byte ASCII witness:

```text
my outer = { my loop x = { my direct = loop x; my helper y = loop y; helper x }; loop }
```

Construct, from the exact production parse/HIR owners, the actual returned HIR artifact and its real outer `DefinitionRootId R`; derive `answer = R` only if the production source equations justify that identity and it satisfies the public API's real type/identity contract. Apply the public API as the proof edge `solve_receiving_residual_experiment(hir, R)`. This is a source-derived API application, not an assertion that a compiler/frontend already calls it or that the function was run.

Establish either:

1. **ENTRY_ADMITTED_PREFIX:** source construction yields the actual HIR and outer root; `answer=R` is justified; each `assemble` guard passes; its normal return connects to candidate collection and the reviewed session-start prefix under explicit fallible premises; or
2. **WITNESS_REJECTED_AT_GUARD:** the exact source-produced pair fails at its first production guard, with the real value and owner shown; or
3. **UNRESOLVED:** the first constructor/identity owner is missing or ambiguous.

A rejection excludes only this unchanged witness from this public API under the stated conditions. It is not global unreachability or a soundness refutation. Stop at candidate session startup; do not claim full `execute_receiving_assembly`, residual publication, ordinary compiler invocation, successful runtime completion, R71 application, or parent closure.

## Authenticated source inputs

The exact source inventory is `tasks/agent-loop/sprints/source-successful-consumer-r273-inputs.json`, SHA-256 `42040552635bb7c2652eb0bad68cb46295078d03ae70620b7edd555d3883fa5f` (229 entries). Derive every source path from it and check expected hashes before opening.

Reuse unchanged indexed views, with hashes rechecked sequentially before any body display:

- R275-r3 contract `tasks/agent-loop/sprints/source-acceptance-r275-r3.md`: `4e30e9c048596a57da7cfa80fe1261e67e2db17f2ba8c07e70dc3961b02138c5`.
- R275-r3 ranges: `2cd3ad9dc9a66129a42ec11d8d45ef4b78a0a877d0d066dc262313d524c03c3e`.
- R275-r3 production/fixture view: `6b3836953c876c40f2cda0b944ff5f8a8d912d179e5ac58f9e93c7e6d38e8373`.
- R275-r3 byte index: `0966c2429bb64896bd31de52f2e20609642c2a75bba6dae3cf5fec46ebcb94e5`.
- R275-r3 corrected HIR ownership coverage: `61d22ccc8004305fb377a12556cd53550926c59cb5857a55b0f01f5921e775cb`.
- R275-r3 entry index: `74ec95494935e803296f8ab276b6237369253f73d3df57ec2bc5f33f12426481`.
- R276 reviewed public route: source view `c80d993a2a0bcb38ea428f4c4c11bfc2d03b804ba0e24d45807b6c2b65a502df`, byte index `2e8892ae1d7ca1e95016b393bdb3c62881c79d47ed848275b154232a2dfe60e1`, clean review `8d7060f9157a3a028b02c45b171f2f94b4ed0c3de06d098755427554677b5c9e`.
- R277 `candidate_receiver.rs:2921–3179` exact extension view: ranges `63f2ce9d1ffb2e14a497d89b928065edd955f3ecd2266b0eb51f670fabd4e855`, view `ebeae02540be5811850017b6f8b7ff49783a95e17d2b05358a155bd47bb22b21`, byte index `8fb7a74c4953d0f78e04f321f437432bbdb9baae811027c555854ade06bfa0da`.
- R276 corrected owner map v2: `6edcf1f02efabb81c3d45b4d75c498cbc2f503b41c1b7ee72c61bb1bded51e42`; source view/index supersede owner-map labels.
- R277-r1 readiness STOP: `tasks/agent-loop/history/20261103-r277-readiness-stop.md`, SHA-256 `38b8e45df76fc7eada38b4ddb22fd3195e4afa4b93a326a08a86b82008328c74`. Its only unresolved assertion was the unneeded pre-existing production callsite.

The 87-byte literal is fixture data only from R275-r3 payload `R274-E001`; test bodies, assertions, `unwrap`, helpers and outcomes remain excluded. R275 payload IDs must be read from the authenticated byte index: E022 is module lowering and E023 the local-source carrier. The actual public API invocation for this theorem packet is the constructed application to `(hir,R)`; no pre-existing caller path is required.

## Contract gate and main Sol assignment

Trial producer `/root/sol_r274_source_acceptance`, requested Sol/high; prior cumulative Sol charge 9,600 seconds. New main-trial grant: 1,500 seconds. First read/hash only this r2 contract and `tasks/agent-loop/history/20261103-r277-r2-admission.md`; independently match both pins and return a fresh current-session WAITING acknowledgement. Luna then revalidates all top-level pins, 229 inventory rows, 41 inherited R275 payloads, 25 R276 payloads and R277-E001, and issues a separate immutable GO. A fresh resume acknowledgement is recorded separately before technical reads; never amend the GO receipt.

Before constructing the witness, Sol's first in-scope step checks whether the pinned production owners actually suffice to derive the HIR artifact, root `R`, and `answer=R`. If a genuine constructor/accessor owner is absent, STOP with exact path/symbol; do not seek an existing caller, do not enter an external path, and do not write outputs. Otherwise continue within the same 1,500 seconds through the exact source derivation and all `assemble` guards to the stated candidate-entry boundary.

## Restrictions, review and accounting

No existing caller is required or asserted. No external path, tests, builds, probes, Cargo, Lean, runtime execution, fixture modification, source edits, scratch/cache/generated output, descendants, semantics changes or production promotion. Never hand-build HIR or `DefinitionRootId`, substitute an answer, bypass `assemble`, or infer source/HIR success from tests.

After coherent freeze, a fresh independent compiler referee receives 900 seconds under a separate review contract. Luna's total R277 preparation/adjudication allocation remains 300 seconds. Total R277 envelope ceiling: **3,000 seconds**—r1 readiness 300 charged; R2 main Sol 1,500 newly issued; fresh reviewer 900 after freeze; Luna 300. The old unissued r1 main/review reservations were canceled and are re-reserved only here. Sol cumulative charge after full r2 grant is 11,100 seconds. No reset/refund; R276's separate 1,800-second accounting remains closed.

Exact output paths remain absent and are leased only at GO:

- `notes/theory/2026-11-03-public-entry-admission-r277.md`
- `tasks/agent-loop/inbox/public-entry-admission-r277.md`

Review receipt after freeze: `tasks/agent-loop/history/20261103-r277-public-entry-admission-review.md`. No reviewer writes a repository file. A PASS establishes only this fixed witness's source-derived admission prefix; it cannot close Need_D, R71, Parent/A/B or the unchanged parent theorem.
